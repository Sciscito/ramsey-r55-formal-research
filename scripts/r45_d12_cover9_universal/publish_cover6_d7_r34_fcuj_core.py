#!/usr/bin/env python3
"""Publish and verify the exact FCUj compact LRAT core in the repository.

The external reducer owns the large ``S:`` transaction and its committed Lean
replay.  This module performs the separate, explicit repository publication:

* revalidate the committed external transaction through the parameterized
  reducer;
* copy the exact CNF, LRAT, and ordered source-clause map without rewriting;
* generate a repository-relative ``Replay.lean`` and the exact indexed-source
  bridge module from the TSV;
* refuse every overwrite and leave any failed partial publication quarantined;
* optionally replay the tracked copy under the same 600-second / 1.5-GiB Lean
  family caps, then publish a portable manifest and milestone report last.

No command in this module invokes a SAT solver.  The default ``preflight`` is
local and does not read ``S:`` or run Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import secrets
from contextlib import nullcontext
from dataclasses import dataclass
from itertools import zip_longest
from pathlib import Path

from . import cover6_d7_r34_safety as safety
from . import reduce_cover6_d7_r34_fgravegow_lrat_core as frozen_core
from . import reduce_cover6_d7_r34_leaf_lrat_core as reducer
from . import reduce_master8_lrat_core as corelib


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
TRACKED_DIRECTORY = HERE / "master7_r34_fcuj_core"
TRACKED_REPORT = HERE / "MASTER7_R34_FCUJ_LRAT_CORE_V1.json"
LEAN_MODULE = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master7R34FCUjCore.lean"
)

SOURCE_DIRECTORY_DEFAULT = Path(
    r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-mincenter-v1"
)
EXTERNAL_CORE_DEFAULT = Path(
    r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-r34-fcuj-core-v1"
)

SLUG = "FCUj_"
RECORD = "FCUj_"
CATALOGUE_INDEX = 0
ICNF_INDEX = 1
INCREMENTAL_POSITION = 2
CORE_CLAUSES = 1_104
SOURCE_CLAUSES = 4_312_440
SOURCE_VARIABLES = 66

CORE_CNF_NAME = "cover6_closed_f7_r34_i2_FCUj__core.cnf"
CORE_LRAT_NAME = "cover6_closed_f7_r34_i2_FCUj__core.lrat"
MAPPING_NAME = "core_clause_map.tsv"
REDUCTION_NAME = "reduction.json"
REPLAY_NAME = "Replay.lean"
ATTRIBUTES_NAME = ".gitattributes"
LEAN_LOG_NAME = "lean_replay.log"
MANIFEST_NAME = "MANIFEST.json"

QUALIFIED_REPLAY_THEOREM = (
    "LRATCatcher.Tests.Cover6D7R34FCUjCoreReplay."
    "cover6_d7_r34_fcuj__core_unsat"
)

EXACT_EXTERNAL_ARTIFACTS = {
    CORE_CNF_NAME: {
        "bytes": 51_238,
        "lines": 1_105,
        "sha256": "B166C31CD69B44D0480602DA904947588E71A7E70C13369E93CB61DD7C9DBC88",
    },
    CORE_LRAT_NAME: {
        "bytes": 115_578,
        "lines": 2_493,
        "sha256": "3069B9CCECC754D0480A8E07BB1FE197B4A25F85745205E963410B059956B739",
    },
    MAPPING_NAME: {
        "bytes": 84_401,
        "lines": 1_105,
        "sha256": "F8E4DA255A42846DFCBC5968B776CEE05560C4EFE8CCBD0699294A525199F723",
    },
    REDUCTION_NAME: {
        "bytes": 6_416,
        "lines": 218,
        "sha256": "69E07377E092A81996ECF13F61DA3045C86DAA0CE1B0B5F7AB5661C23BF82C76",
    },
    REPLAY_NAME: {
        "bytes": 544,
        "lines": 12,
        "sha256": "7F81A40DD433B8BECB786B0558E7C44EFF5FC45424E6796B6AE42DB280EEE4A4",
    },
}
EXTERNAL_MANIFEST = {
    "bytes": 13_817,
    "lines": 411,
    "sha256": "A5DE6752F17CF8A96BF6EC5053F19AFC5738E7DED22F582A995F00D178482564",
}
EXTERNAL_LEAN_LOG = {
    "bytes": 200,
    "lines": 4,
    "sha256": "09A483664F85B18B37C4ED63EA3251CD5AA032723DA792191F819BEA55AE81C0",
}

PORTABLE_ARTIFACT_NAMES = (
    CORE_CNF_NAME,
    CORE_LRAT_NAME,
    MAPPING_NAME,
    REDUCTION_NAME,
    REPLAY_NAME,
    ATTRIBUTES_NAME,
)
COMPLETE_ARTIFACT_NAMES = PORTABLE_ARTIFACT_NAMES + (LEAN_LOG_NAME, MANIFEST_NAME)
ABSOLUTE_PATH_PATTERN = re.compile(
    rb"(?:[A-Za-z]:[\\/]|file://|(?:^|[\s\"'])\\\\)", re.MULTILINE
)
SHA256_PATTERN = re.compile(r"[0-9A-F]{64}")


class FCUjPublicationError(ValueError):
    """Raised at the first identity, portability, or publication mismatch."""


@dataclass(frozen=True)
class FileMeta:
    name: str
    bytes: int
    lines: int
    sha256: str

    def json(self) -> dict[str, object]:
        return {
            "name": self.name,
            "bytes": self.bytes,
            "lines": self.lines,
            "sha256": self.sha256,
        }


def file_metadata(path: Path) -> FileMeta:
    digest = hashlib.sha256()
    size = 0
    lines = 0
    last = b""
    with path.open("rb", buffering=1024 * 1024) as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
            size += len(block)
            lines += block.count(b"\n")
            last = block[-1:]
    if size and last != b"\n":
        lines += 1
    return FileMeta(path.name, size, lines, digest.hexdigest().upper())


def payload_metadata(name: str, payload: bytes) -> FileMeta:
    lines = payload.count(b"\n")
    if payload and not payload.endswith(b"\n"):
        lines += 1
    return FileMeta(
        name,
        len(payload),
        lines,
        hashlib.sha256(payload).hexdigest().upper(),
    )


def json_payload(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def assert_portable(payload: bytes, label: str) -> None:
    if ABSOLUTE_PATH_PATTERN.search(payload):
        raise FCUjPublicationError(f"{label} contains an absolute path")


def ensure_repo_path(path: Path, label: str) -> None:
    try:
        path.resolve(strict=False).relative_to(REPOSITORY.resolve(strict=True))
    except ValueError as error:
        raise FCUjPublicationError(f"{label} is outside the repository") from error


def write_new(path: Path, payload: bytes) -> None:
    ensure_repo_path(path, path.name)
    with path.open("xb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())


def copy_new(source: Path, target: Path, expected: dict[str, object]) -> FileMeta:
    ensure_repo_path(target, target.name)
    digest = hashlib.sha256()
    size = 0
    lines = 0
    last = b""
    with source.open("rb", buffering=1024 * 1024) as src:
        with target.open("xb", buffering=1024 * 1024) as dst:
            for block in iter(lambda: src.read(1024 * 1024), b""):
                dst.write(block)
                digest.update(block)
                size += len(block)
                lines += block.count(b"\n")
                last = block[-1:]
            dst.flush()
            os.fsync(dst.fileno())
    if size and last != b"\n":
        lines += 1
    actual = FileMeta(target.name, size, lines, digest.hexdigest().upper())
    for field in ("bytes", "lines", "sha256"):
        if getattr(actual, field) != expected[field]:
            raise FCUjPublicationError(f"copied {target.name} {field} mismatch")
    return actual


def tracked_replay_source() -> bytes:
    payload = f"""import LRATCatcher.Reflect

namespace LRATCatcher.Tests.Cover6D7R34FCUjCoreReplay

-- Exact frozen-DIMACS core only; no semantic S7 composition here.
lrat_reflect cover6_d7_r34_fcuj__core_unsat
  \"../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/{CORE_CNF_NAME}\"
  \"../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/{CORE_LRAT_NAME}\"

#print axioms cover6_d7_r34_fcuj__core_unsat

end LRATCatcher.Tests.Cover6D7R34FCUjCoreReplay
""".encode("utf-8")
    assert_portable(payload, "tracked Replay.lean")
    return payload


def attributes_source() -> bytes:
    return (
        "*.cnf binary\n"
        "*.lrat binary\n"
        "*.tsv binary\n"
        "*.json -text\n"
        "*.lean -text\n"
        "*.log -text\n"
    ).encode("ascii")


def read_zero_based_indices(mapping_path: Path) -> list[int]:
    with mapping_path.open("r", encoding="ascii", newline="") as stream:
        header = stream.readline()
        if header != "core_clause_id\tfcuj__clause_id\tclause_sha256\n":
            raise FCUjPublicationError("FCUj mapping header changed")
        indices: list[int] = []
        previous = 0
        for expected_core_id, raw in enumerate(stream, start=1):
            fields = raw.rstrip("\n").split("\t")
            if len(fields) != 3:
                raise FCUjPublicationError("malformed FCUj mapping row")
            core_id_text, source_id_text, clause_sha = fields
            try:
                core_id = int(core_id_text)
                source_id = int(source_id_text)
            except ValueError as error:
                raise FCUjPublicationError("non-integer FCUj mapping id") from error
            if core_id != expected_core_id:
                raise FCUjPublicationError("FCUj core ids are not contiguous")
            if not 1 <= source_id <= SOURCE_CLAUSES or source_id <= previous:
                raise FCUjPublicationError("FCUj source ids are not strict/in-bounds")
            if SHA256_PATTERN.fullmatch(clause_sha) is None:
                raise FCUjPublicationError("malformed FCUj clause hash")
            indices.append(source_id - 1)
            previous = source_id
    if len(indices) != CORE_CLAUSES:
        raise FCUjPublicationError("FCUj mapping row count changed")
    return indices


def verify_mapping_clause_hashes(mapping_path: Path, cnf_path: Path) -> None:
    with mapping_path.open("r", encoding="ascii", newline="") as mapping:
        mapping.readline()
        with cnf_path.open("rb") as cnf:
            header = cnf.readline()
            if header != b"p cnf 66 1104\n":
                raise FCUjPublicationError("tracked FCUj core header changed")
            for expected_core_id, pair in enumerate(
                zip_longest(mapping, cnf), start=1
            ):
                row, clause = pair
                if row is None or clause is None:
                    raise FCUjPublicationError(
                        "tracked FCUj CNF/map lengths differ"
                    )
                fields = row.rstrip("\n").split("\t")
                if int(fields[0]) != expected_core_id:
                    raise FCUjPublicationError("tracked FCUj map id changed")
                if hashlib.sha256(clause).hexdigest().upper() != fields[2]:
                    raise FCUjPublicationError("tracked FCUj clause hash mismatch")


def format_indices(indices: list[int]) -> str:
    rows = []
    for start in range(0, len(indices), 12):
        rows.append("  " + ", ".join(str(value) for value in indices[start : start + 12]) + ",")
    return "\n".join(rows)


def lean_module_source(indices: list[int]) -> bytes:
    if len(indices) != CORE_CLAUSES:
        raise FCUjPublicationError("refusing Lean module with wrong index count")
    payload = f"""import LRATCatcher.Reflect
import LRATCatcher.Tests.R44Cover6Master7R34IndexedSource

/-!
  # Certified indexed-source bridge for the FCUj degree-seven branch

  The tracked compact CNF is an ordered {CORE_CLAUSES:,}-clause subsequence of
  the exact F7 source followed by the 21 units for catalogue representative
  FCUj.  The indices below are the zero-based form of the tracked
  `core_clause_map.tsv` source IDs.  Lean recomputes every selected clause,
  checks exact ordered CNF equality, replays the compact LRAT certificate, and
  transfers UNSAT to the complete lazy branch source.

  This module certifies one branch only.  It does not compose the nine R34
  orbits and does not prove the degree-seven cover6 theorem.
-/

namespace LRATCatcher.Tests.R44Cover6Master7R34FCUjCore

open Std.Sat
open LRATCatcher.Tests.R44Cover6Master8CoreBridge
open LRATCatcher.Tests.R44Cover6Master7R34IndexedSource
open LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization

set_option maxRecDepth 100000

/-! ## Exact branch identity -/

def fCUjCatalogueIndex : Fin 9 := ⟨{CATALOGUE_INDEX}, by decide⟩
def fCUjICNFIndex : Fin 9 := ⟨{ICNF_INDEX}, by decide⟩

theorem fCUjCatalogueRecord_exact :
    r34Catalogue7Graph6Records.getD fCUjCatalogueIndex.val "" = "FCUj_" := by
  native_decide

theorem fCUjICNFRecord_exact :
    r34IcnfGraph6Records.getD fCUjICNFIndex.val "" = "FCUj_" := by
  native_decide

theorem fCUjIndexSwap_exact :
    r34IndexSwap fCUjICNFIndex = fCUjCatalogueIndex := by
  native_decide

theorem fCUjICNFBranchSource_exact :
    iCNFBranchSource fCUjICNFIndex = branchSource fCUjCatalogueIndex := by
  rw [iCNFBranchSource, fCUjIndexSwap_exact]

/-! ## Tracked {CORE_CLAUSES:,}-clause selection -/

def fCUjCoreZeroBasedIndices : Array Nat := #[
{format_indices(indices)}
]

def checkedBranchFin (index : Nat) : Option (Fin branchClauseCount) :=
  if h : index < branchClauseCount then some ⟨index, h⟩ else none

def fCUjCoreFinIndices : Array (Fin branchClauseCount) :=
  fCUjCoreZeroBasedIndices.filterMap checkedBranchFin

theorem fCUjCoreIndexCount :
    fCUjCoreZeroBasedIndices.size = {CORE_CLAUSES} := by
  native_decide

theorem fCUjCoreFinIndexCount :
    fCUjCoreFinIndices.size = {CORE_CLAUSES} := by
  native_decide

theorem fCUjCoreIndices_inBounds :
    ∀ index, index ∈ fCUjCoreZeroBasedIndices → index < branchClauseCount := by
  native_decide

/-! ## Exact tracked CNF and compact LRAT replay -/

def fCUjCoreCNFText : String :=
  include_str "../../../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/{CORE_CNF_NAME}"

def fCUjCertifiedCoreCNF : CNF Nat :=
  LRATCatcher.parseDimacs fCUjCoreCNFText

theorem fCUjCoreCNFText_byteSize :
    fCUjCoreCNFText.utf8ByteSize = 51238 := by
  native_decide

lrat_reflect fCUjCertifiedCoreUnsat
  "../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/{CORE_CNF_NAME}"
  "../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/{CORE_LRAT_NAME}"

set_option maxHeartbeats 0 in
theorem fCUjCoreSelection_eq_certifiedCore :
    (branchSource fCUjCatalogueIndex).selectCNF fCUjCoreFinIndices =
      fCUjCertifiedCoreCNF := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

theorem fCUjCoreSelection_unsat :
    ((branchSource fCUjCatalogueIndex).selectCNF fCUjCoreFinIndices).Unsat := by
  rw [fCUjCoreSelection_eq_certifiedCore]
  exact fCUjCertifiedCoreUnsat

/-- The exact full F7 + 21-unit source for catalogue representative FCUj is
UNSAT. -/
theorem fCUjBranchSource_unsat :
    (branchSource fCUjCatalogueIndex).fullCNF.Unsat :=
  (branchSource fCUjCatalogueIndex).full_unsat_of_select_unsat
    fCUjCoreFinIndices fCUjCoreSelection_unsat

/-- Same endpoint in the incremental-CNF indexing convention. -/
theorem fCUjICNFBranchSource_unsat :
    (iCNFBranchSource fCUjICNFIndex).fullCNF.Unsat := by
  rw [fCUjICNFBranchSource_exact]
  exact fCUjBranchSource_unsat

/-! ## Lightweight semantic interface

The existing R34 relabeling theorem supplies the exact 21-unit tail for this
representative.  Closing a degree-seven Ramsey-free coloring from the branch
UNSAT theorem still requires the separate F7-body semantics theorem: every
one of the first 4,312,419 clauses must evaluate to true under the relabeled
coloring.  That large semantic bridge is intentionally not asserted here. -/

theorem fCUjRelabeled_unitTail_eval_true
    (coloring : Nat -> Bool)
    (sourceToRepresentative : LRATCatcher.Tests.R35.FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring fCUjCatalogueIndex
      sourceToRepresentative) (position : Fin 21) :
    CNF.Clause.eval
        (d7R34RelabeledColoring coloring sourceToRepresentative)
        ((branchSource fCUjCatalogueIndex).clauseAt
          ⟨f7ClauseCount + position.val, by
            change f7ClauseCount + position.val < branchClauseCount
            dsimp [branchClauseCount, f7ClauseCount, r34UnitClauseCount]
            omega⟩) = true :=
  branchSource_unitClause_eval_true coloring fCUjCatalogueIndex
    sourceToRepresentative hmap position

#print axioms fCUjCoreSelection_eq_certifiedCore
#print axioms fCUjBranchSource_unsat
#print axioms fCUjICNFBranchSource_unsat
#print axioms fCUjRelabeled_unitTail_eval_true

end LRATCatcher.Tests.R44Cover6Master7R34FCUjCore
""".encode("utf-8")
    assert_portable(payload, "FCUj indexed-source Lean module")
    return payload


def external_paths(directory: Path) -> dict[str, Path]:
    return {
        CORE_CNF_NAME: directory / CORE_CNF_NAME,
        CORE_LRAT_NAME: directory / CORE_LRAT_NAME,
        MAPPING_NAME: directory / MAPPING_NAME,
        REDUCTION_NAME: directory / REDUCTION_NAME,
        REPLAY_NAME: directory / REPLAY_NAME,
        "external_manifest": directory / "lean_replay.run" / MANIFEST_NAME,
        "external_log": directory / "lean_replay.run" / LEAN_LOG_NAME,
    }


def validate_external(source_dir: Path, external_core: Path) -> dict[str, object]:
    verification = reducer.verify_core(source_dir, external_core, SLUG)
    if verification.get("status") != "LEAN_REPLAY_PASS":
        raise FCUjPublicationError("external FCUj core lacks committed Lean replay")
    paths = external_paths(external_core)
    for name, expected in EXACT_EXTERNAL_ARTIFACTS.items():
        actual = file_metadata(paths[name])
        for field in ("bytes", "lines", "sha256"):
            if getattr(actual, field) != expected[field]:
                raise FCUjPublicationError(f"external {name} {field} changed")
    for key, expected in (
        ("external_manifest", EXTERNAL_MANIFEST),
        ("external_log", EXTERNAL_LEAN_LOG),
    ):
        actual = file_metadata(paths[key])
        for field in ("bytes", "lines", "sha256"):
            if getattr(actual, field) != expected[field]:
                raise FCUjPublicationError(f"{key} {field} changed")
    manifest = json.loads(paths["external_manifest"].read_text(encoding="utf-8"))
    if manifest.get("status") != "LEAN_REPLAY_PASS":
        raise FCUjPublicationError("external manifest status changed")
    if (
        manifest.get("validation", {}).get("lean", {}).get("status")
        != "LEAN_LRAT_REPLAY_PASS"
    ):
        raise FCUjPublicationError("external Lean replay anchor changed")
    return verification


def portable_reduction_payload(
    verification: dict[str, object], external_core: Path
) -> bytes:
    paths = external_paths(external_core)
    source_analysis = verification["source_analysis"]
    tracked_artifacts = {
        "cnf": {
            "name": CORE_CNF_NAME,
            **EXACT_EXTERNAL_ARTIFACTS[CORE_CNF_NAME],
        },
        "lrat": {
            "name": CORE_LRAT_NAME,
            **EXACT_EXTERNAL_ARTIFACTS[CORE_LRAT_NAME],
        },
        "mapping": {
            "name": MAPPING_NAME,
            **EXACT_EXTERNAL_ARTIFACTS[MAPPING_NAME],
        },
        "replay": payload_metadata(REPLAY_NAME, tracked_replay_source()).json(),
        "gitattributes": payload_metadata(
            ATTRIBUTES_NAME, attributes_source()
        ).json(),
    }
    value = {
        "schema_version": 1,
        "status": "PASS_TRACKED_FCUJ_CORE_REPLAY_REQUIRED",
        "selection": verification["selection"],
        "source": source_analysis["input"],
        "source_run_report": source_analysis["source_run_report"],
        "source_artifacts": source_analysis["source_artifacts"],
        "proof": source_analysis["proof"],
        "dependency_core": source_analysis["core"],
        "caps": verification["caps"],
        "artifacts": tracked_artifacts,
        "validation": {
            "external_committed_lean_replay": {
                "status": "LEAN_REPLAY_PASS",
                "manifest": file_metadata(paths["external_manifest"]).json(),
                "lean_log": file_metadata(paths["external_log"]).json(),
                "storage": "external cache, not tracked",
            },
            "mapping": verification["mapping"],
            "reduced_pair": verification["reduced_pair"],
            "tracked_lean_replay": "PENDING",
        },
        "reducer": {
            "name": "reduce_cover6_d7_r34_leaf_lrat_core.py",
            "sha256": file_metadata(HERE / "reduce_cover6_d7_r34_leaf_lrat_core.py").sha256,
            "algorithm": "all-RUP full index, backward closure, dense id remap v1",
        },
        "formal_boundary": (
            "portable tracked copy of the exact frozen FCUj leaf core only; "
            "tracked-path Lean replay pending; no S7 orbit composition, cover6-d7 "
            "theorem, global gluing, Ramsey bound, or major discovery"
        ),
    }
    payload = json_payload(value)
    assert_portable(payload, "portable FCUj reduction")
    return payload


def tracked_paths() -> dict[str, Path]:
    return {name: TRACKED_DIRECTORY / name for name in COMPLETE_ARTIFACT_NAMES}


def portable_core_metadata(directory: Path) -> dict[str, dict[str, object]]:
    return {name: file_metadata(directory / name).json() for name in PORTABLE_ARTIFACT_NAMES}


def verify_portable_core() -> dict[str, object]:
    if not TRACKED_DIRECTORY.is_dir():
        raise FileNotFoundError(TRACKED_DIRECTORY)
    expected = {TRACKED_DIRECTORY / name for name in PORTABLE_ARTIFACT_NAMES}
    optional = {TRACKED_DIRECTORY / LEAN_LOG_NAME, TRACKED_DIRECTORY / MANIFEST_NAME}
    observed = set(TRACKED_DIRECTORY.iterdir())
    if observed not in (expected, expected | optional):
        raise FCUjPublicationError("tracked FCUj directory inventory is not exact")
    for name in (CORE_CNF_NAME, CORE_LRAT_NAME, MAPPING_NAME):
        actual = file_metadata(TRACKED_DIRECTORY / name)
        frozen = EXACT_EXTERNAL_ARTIFACTS[name]
        for field in ("bytes", "lines", "sha256"):
            if getattr(actual, field) != frozen[field]:
                raise FCUjPublicationError(f"tracked {name} {field} changed")
    if (TRACKED_DIRECTORY / REPLAY_NAME).read_bytes() != tracked_replay_source():
        raise FCUjPublicationError("tracked Replay.lean changed")
    if (TRACKED_DIRECTORY / ATTRIBUTES_NAME).read_bytes() != attributes_source():
        raise FCUjPublicationError("tracked .gitattributes changed")
    for name in (REDUCTION_NAME, REPLAY_NAME, ATTRIBUTES_NAME):
        assert_portable((TRACKED_DIRECTORY / name).read_bytes(), f"tracked {name}")
    reduction = json.loads(
        (TRACKED_DIRECTORY / REDUCTION_NAME).read_text(encoding="utf-8")
    )
    if reduction.get("status") != "PASS_TRACKED_FCUJ_CORE_REPLAY_REQUIRED":
        raise FCUjPublicationError("tracked FCUj reduction status changed")
    if reduction.get("selection", {}).get("record") != RECORD:
        raise FCUjPublicationError("tracked FCUj reduction selection changed")
    claimed = reduction.get("artifacts")
    if not isinstance(claimed, dict):
        raise FCUjPublicationError("tracked FCUj reduction artifacts missing")
    expected_claims = {
        "cnf": file_metadata(TRACKED_DIRECTORY / CORE_CNF_NAME).json(),
        "lrat": file_metadata(TRACKED_DIRECTORY / CORE_LRAT_NAME).json(),
        "mapping": file_metadata(TRACKED_DIRECTORY / MAPPING_NAME).json(),
        "replay": file_metadata(TRACKED_DIRECTORY / REPLAY_NAME).json(),
        "gitattributes": file_metadata(TRACKED_DIRECTORY / ATTRIBUTES_NAME).json(),
    }
    if claimed != expected_claims:
        raise FCUjPublicationError("tracked FCUj reduction artifact table changed")
    indices = read_zero_based_indices(TRACKED_DIRECTORY / MAPPING_NAME)
    verify_mapping_clause_hashes(
        TRACKED_DIRECTORY / MAPPING_NAME, TRACKED_DIRECTORY / CORE_CNF_NAME
    )
    reduced = corelib.verify_reduced_pair(
        TRACKED_DIRECTORY / CORE_CNF_NAME, TRACKED_DIRECTORY / CORE_LRAT_NAME
    )
    if not LEAN_MODULE.is_file():
        raise FileNotFoundError(LEAN_MODULE)
    expected_module = lean_module_source(indices)
    if LEAN_MODULE.read_bytes() != expected_module:
        raise FCUjPublicationError("FCUj indexed-source Lean module changed")
    return {
        "status": "PASS_EXACT_TRACKED_FCUJ_CORE",
        "artifacts": portable_core_metadata(TRACKED_DIRECTORY),
        "module": file_metadata(LEAN_MODULE).json(),
        "reduced_pair": reduced,
        "index_count": len(indices),
    }


def publish(source_dir: Path, external_core: Path) -> dict[str, object]:
    for path, label in (
        (TRACKED_DIRECTORY, "tracked FCUj directory"),
        (TRACKED_REPORT, "tracked FCUj report"),
        (LEAN_MODULE, "FCUj indexed-source Lean module"),
    ):
        if os.path.lexists(path):
            raise FileExistsError(f"refusing existing {label}: {path}")
    verification = validate_external(source_dir, external_core)
    external = external_paths(external_core)
    indices = read_zero_based_indices(external[MAPPING_NAME])
    module_payload = lean_module_source(indices)
    nonce = secrets.token_hex(16)
    staging = TRACKED_DIRECTORY.with_name(TRACKED_DIRECTORY.name + f".partial.{nonce}")
    module_partial = LEAN_MODULE.with_name(LEAN_MODULE.name + f".partial.{nonce}")
    if os.path.lexists(staging) or os.path.lexists(module_partial):
        raise FileExistsError("fresh FCUj publication nonce unexpectedly exists")
    staging.mkdir()
    try:
        for name in (CORE_CNF_NAME, CORE_LRAT_NAME, MAPPING_NAME):
            copy_new(external[name], staging / name, EXACT_EXTERNAL_ARTIFACTS[name])
        write_new(staging / REPLAY_NAME, tracked_replay_source())
        write_new(staging / ATTRIBUTES_NAME, attributes_source())
        write_new(
            staging / REDUCTION_NAME,
            portable_reduction_payload(verification, external_core),
        )
        write_new(module_partial, module_payload)
        verify_mapping_clause_hashes(staging / MAPPING_NAME, staging / CORE_CNF_NAME)
        corelib.verify_reduced_pair(staging / CORE_CNF_NAME, staging / CORE_LRAT_NAME)
        if os.path.lexists(TRACKED_DIRECTORY) or os.path.lexists(LEAN_MODULE):
            raise FileExistsError("FCUj publication target appeared")
        os.rename(staging, TRACKED_DIRECTORY)
        os.rename(module_partial, LEAN_MODULE)
    except BaseException:
        # Deliberately no cleanup: any partial/final fragment is quarantine data.
        raise
    return verify_portable_core()


def portable_stack(stack: dict[str, object]) -> dict[str, object]:
    return frozen_core._portable_stack(stack)


def portable_supervision(supervision: dict[str, object]) -> dict[str, object]:
    value = frozen_core._portable_supervision(supervision)
    value["command"] = ["lean.exe", REPLAY_NAME]
    return value


def tracked_manifest_payload(
    verification: dict[str, object],
    artifacts: dict[str, dict[str, object]],
    stack: dict[str, object],
    supervision: dict[str, object],
    axioms: list[str],
) -> bytes:
    reduction = json.loads((TRACKED_DIRECTORY / REDUCTION_NAME).read_text(encoding="utf-8"))
    value = {
        "schema_version": 1,
        "status": "PASS_TRACKED_FCUJ_COMPACT_CORE_LEAN_REPLAY",
        "selection": reduction["selection"],
        "source_fcuj_leaf": {
            "cnf": reduction["source"]["cnf"],
            "lrat": reduction["source"]["lrat"],
            "run_report": reduction["source_run_report"],
            "external_core_manifest": reduction["validation"][
                "external_committed_lean_replay"
            ]["manifest"],
        },
        "dependency_core": reduction["dependency_core"],
        "caps": reduction["caps"],
        "artifacts": artifacts,
        "validation": {
            "source_proof_syntax": "376462 RUP additions, zero RAT",
            "forward_hint_policy": "all forward hints rejected during full indexing",
            "backward_closure": "unique final empty-clause dependency closure",
            "mapping": reduction["validation"]["mapping"],
            "reduced_pair": verification["reduced_pair"],
            "post_replay_artifacts_unchanged": True,
            "lean": {
                "status": "LEAN_LRAT_REPLAY_PASS",
                "theorem": QUALIFIED_REPLAY_THEOREM,
                "axioms": axioms,
                "axioms_allowed": True,
                "frozen_stack": portable_stack(stack),
                "supervision": portable_supervision(supervision),
            },
        },
        "eol_policy": (
            "CNF, LRAT, and TSV are Git binary; JSON, Lean, and log are -text "
            "so frozen byte hashes are not rewritten"
        ),
        "formal_boundary": (
            "Lean proves UNSAT only for the exact tracked ordered-subsequence "
            "core of the frozen FCUj leaf CNF. This does not prove encoder "
            "semantics, S7 orbit coverage/composition, a cover6-d7 theorem, "
            "global gluing, a Ramsey-number bound, or a major discovery."
        ),
    }
    payload = json_payload(value)
    assert_portable(payload, "tracked FCUj MANIFEST.json")
    return payload


def milestone_payload(manifest: dict[str, object], manifest_meta: FileMeta) -> bytes:
    value = {
        "schema_version": 1,
        "status": "PASS_MASTER7_R34_FCUJ_TRACKED_CORE_V1",
        "milestone": (
            "the exact FCUj conditioned leaf has a compact tracked RUP core "
            "independently replayed by Lean/LRATCatcher"
        ),
        "artifact_directory": TRACKED_DIRECTORY.name,
        "source_fcuj_leaf": manifest["source_fcuj_leaf"],
        "selection": manifest["selection"],
        "dependency_core": manifest["dependency_core"],
        "artifacts": {**manifest["artifacts"], "manifest": manifest_meta.json()},
        "validation": {
            "status": manifest["status"],
            "theorem": manifest["validation"]["lean"]["theorem"],
            "axioms": manifest["validation"]["lean"]["axioms"],
            "mapping_status": manifest["validation"]["mapping"]["status"],
            "reduced_pair_status": manifest["validation"]["reduced_pair"]["status"],
            "post_replay_artifacts_unchanged": manifest["validation"][
                "post_replay_artifacts_unchanged"
            ],
        },
        "value": (
            "This turns the solver-only FCUj result into a small, portable, "
            "hash-frozen Lean-replayed certificate. It is a rigorous leaf "
            "checkpoint, not the remaining S7 composition theorem."
        ),
        "remaining": (
            "certify and compose the six remaining nontrivial R34 leaves via "
            "S7, then prove the cover6-d7 theorem before any global gluing or "
            "Ramsey claim"
        ),
        "formal_boundary": manifest["formal_boundary"],
    }
    payload = json_payload(value)
    assert_portable(payload, "tracked FCUj milestone report")
    return payload


def replay_tracked(temporary_directory: Path) -> dict[str, object]:
    verification = verify_portable_core()
    paths = tracked_paths()
    for path in (paths[LEAN_LOG_NAME], paths[MANIFEST_NAME], TRACKED_REPORT):
        if os.path.lexists(path):
            raise FileExistsError(f"refusing existing tracked replay output: {path}")
    log_partial = paths[LEAN_LOG_NAME].with_name(LEAN_LOG_NAME + ".partial")
    manifest_partial = paths[MANIFEST_NAME].with_name(MANIFEST_NAME + ".partial")
    report_partial = TRACKED_REPORT.with_name(TRACKED_REPORT.name + ".partial")
    for path in (log_partial, manifest_partial, report_partial):
        if os.path.lexists(path):
            raise FileExistsError(f"refusing residual tracked replay partial: {path}")
    temporary_directory = reducer.require_absolute_s(
        temporary_directory, "tracked replay temporary directory"
    )
    safety.require_existing_directory(temporary_directory, "temporary directory")
    safety.reject_absolute_s_reparse(
        temporary_directory, "tracked replay temporary directory"
    )
    for protected in (
        reducer.LEAN_TOOLCHAIN_ROOT,
        reducer.LRAT_CATCHER_LEAN_PATH,
        EXTERNAL_CORE_DEFAULT,
        SOURCE_DIRECTORY_DEFAULT,
    ):
        if reducer.paths_overlap(temporary_directory, protected):
            raise FCUjPublicationError(
                "tracked replay temporary directory overlaps protected data"
            )
    if any(temporary_directory.iterdir()):
        raise FCUjPublicationError("tracked replay temporary directory is not empty")
    core_inputs = [TRACKED_DIRECTORY / name for name in PORTABLE_ARTIFACT_NAMES]
    locks = safety.WindowsReadLocks(core_inputs) if os.name == "nt" else nullcontext()
    with locks:
        before = portable_core_metadata(TRACKED_DIRECTORY)
        stack_before = reducer.verify_replay_stack()
        supervision = reducer._lean_supervised(
            TRACKED_DIRECTORY / REPLAY_NAME,
            log_partial,
            temporary_directory=temporary_directory,
        )
        log_payload = log_partial.read_bytes()
        assert_portable(log_payload, "tracked FCUj Lean log")
        log_text = log_payload.decode("utf-8", errors="replace")
        axioms = reducer.parse_axioms(log_text, QUALIFIED_REPLAY_THEOREM)
        success = (
            supervision["stop_reason"] is None
            and supervision["returncode"] == 0
            and reducer.axioms_allowed(axioms, "cover6_d7_r34_fcuj__core_unsat")
            and "sorryAx" not in log_text
            and "declaration uses 'sorry'" not in log_text
            and before == portable_core_metadata(TRACKED_DIRECTORY)
            and stack_before == reducer.verify_replay_stack()
            and not any(temporary_directory.iterdir())
        )
        if not success:
            raise FCUjPublicationError("tracked FCUj Lean replay failed closed")
    os.rename(log_partial, paths[LEAN_LOG_NAME])
    artifacts = portable_core_metadata(TRACKED_DIRECTORY)
    artifacts[LEAN_LOG_NAME] = file_metadata(paths[LEAN_LOG_NAME]).json()
    manifest_payload = tracked_manifest_payload(
        verification, artifacts, stack_before, supervision, axioms
    )
    write_new(manifest_partial, manifest_payload)
    os.rename(manifest_partial, paths[MANIFEST_NAME])
    manifest = json.loads(manifest_payload.decode("utf-8"))
    report_payload = milestone_payload(manifest, file_metadata(paths[MANIFEST_NAME]))
    write_new(report_partial, report_payload)
    os.rename(report_partial, TRACKED_REPORT)
    return verify_complete()


def verify_complete() -> dict[str, object]:
    verification = verify_portable_core()
    paths = tracked_paths()
    if not paths[LEAN_LOG_NAME].is_file() or not paths[MANIFEST_NAME].is_file():
        raise FCUjPublicationError("tracked FCUj replay publication is incomplete")
    if not TRACKED_REPORT.is_file():
        raise FCUjPublicationError("tracked FCUj milestone report is missing")
    for path in (paths[LEAN_LOG_NAME], paths[MANIFEST_NAME], TRACKED_REPORT):
        assert_portable(path.read_bytes(), path.name)
    manifest = json.loads(paths[MANIFEST_NAME].read_text(encoding="utf-8"))
    report = json.loads(TRACKED_REPORT.read_text(encoding="utf-8"))
    if manifest.get("status") != "PASS_TRACKED_FCUJ_COMPACT_CORE_LEAN_REPLAY":
        raise FCUjPublicationError("tracked FCUj manifest status changed")
    if report.get("status") != "PASS_MASTER7_R34_FCUJ_TRACKED_CORE_V1":
        raise FCUjPublicationError("tracked FCUj report status changed")
    actual_artifacts = portable_core_metadata(TRACKED_DIRECTORY)
    actual_artifacts[LEAN_LOG_NAME] = file_metadata(paths[LEAN_LOG_NAME]).json()
    if manifest.get("artifacts") != actual_artifacts:
        raise FCUjPublicationError("tracked FCUj manifest artifacts changed")
    if report.get("artifacts", {}).get("manifest") != file_metadata(
        paths[MANIFEST_NAME]
    ).json():
        raise FCUjPublicationError("tracked FCUj report manifest identity changed")
    expected_report = milestone_payload(
        manifest, file_metadata(paths[MANIFEST_NAME])
    )
    if TRACKED_REPORT.read_bytes() != expected_report:
        raise FCUjPublicationError(
            "tracked FCUj report differs from deterministic rendering"
        )
    return {
        **verification,
        "status": "PASS_MASTER7_R34_FCUJ_TRACKED_CORE_V1",
        "manifest": file_metadata(paths[MANIFEST_NAME]).json(),
        "report": file_metadata(TRACKED_REPORT).json(),
    }


def preflight() -> dict[str, object]:
    return {
        "status": "PREFLIGHT_ONLY_NO_S_NO_SOLVER_NO_LEAN",
        "leaf": SLUG,
        "tracked_directory": TRACKED_DIRECTORY.relative_to(REPOSITORY).as_posix(),
        "tracked_report": TRACKED_REPORT.relative_to(REPOSITORY).as_posix(),
        "lean_module": LEAN_MODULE.relative_to(REPOSITORY).as_posix(),
        "core_clauses": CORE_CLAUSES,
        "expected_external_artifacts": EXACT_EXTERNAL_ARTIFACTS,
        "publication": (
            "all outputs are create-new; a failure leaves partial data quarantined; "
            "the portable milestone report is published last"
        ),
        "solver_policy": "this publisher never invokes a SAT solver",
        "formal_boundary": (
            "one exact FCUj leaf core only; no semantics, S7 composition, "
            "cover6-d7 theorem, global gluing, or Ramsey-number bound"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        default="preflight",
        choices=("preflight", "publish", "verify", "replay-tracked", "verify-complete"),
    )
    parser.add_argument("--source-dir", type=Path, default=SOURCE_DIRECTORY_DEFAULT)
    parser.add_argument("--external-core-dir", type=Path, default=EXTERNAL_CORE_DEFAULT)
    parser.add_argument("--temporary-directory", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    elif args.command == "publish":
        result = publish(args.source_dir, args.external_core_dir)
    elif args.command == "verify":
        result = verify_portable_core()
    elif args.command == "verify-complete":
        result = verify_complete()
    else:
        if args.temporary_directory is None:
            parser.error("replay-tracked requires --temporary-directory")
        result = replay_tracked(args.temporary_directory)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
