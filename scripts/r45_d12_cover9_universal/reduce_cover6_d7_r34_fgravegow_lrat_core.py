#!/usr/bin/env python3
"""Reduce and independently replay the frozen F`GOW LRAT dependency core.

No SAT solver is invoked.  The source pair is accepted only at its frozen
identity.  Every LRAT addition is indexed, forward hints are rejected, RAT
steps cause a hard refusal, and the backward dependency closure of the final
empty clause is densely remapped onto an exact ordered CNF subsequence.

All large inputs and generated artifacts must live below absolute S: paths.
The reducer never overwrites or deletes a path.  A failed write can therefore
leave a dedicated ``.partial`` forensic artifact in the newly-created output
directory; reruns must use a fresh output directory.
"""

from __future__ import annotations

import argparse
import ctypes
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import threading
import time
from ctypes import wintypes
from pathlib import Path, PureWindowsPath

from . import materialize_cover6_d7_r34_fgravegow_leaf as leaf
from . import reduce_master8_lrat_core as corelib
from . import run_cover6_d7_r34_fgravegow_lrat as lrat_runner


SOURCE_CNF_NAME = leaf.TARGET_NAME
SOURCE_CNF_VARIABLES = 66
SOURCE_CNF_CLAUSES = 4_312_440
SOURCE_CNF_BYTES = 246_507_635
SOURCE_CNF_SHA256 = "78D066E03B1F55FACBF8839BCC409E0D45BABF93FA6D266628BB526D2F5E5971"

SOURCE_LRAT_NAME = lrat_runner.PROOF_NAME
SOURCE_LRAT_BYTES = 73_928_822
SOURCE_LRAT_SHA256 = "580D4B8FC24BCE446D2DF22370C4D56397EE54E7272A4A48796A86962E5D5A3A"
SOURCE_LRAT_ADDITIONS = 399_094
SOURCE_LRAT_DELETION_ACTIONS = 396_487
SOURCE_LRAT_DELETED_IDENTIFIERS = 4_428_897

SOURCE_RUN_REPORT_NAME = lrat_runner.REPORT_NAME
SOURCE_RUN_REPORT_BYTES = 4_898
SOURCE_RUN_REPORT_SHA256 = (
    "BEB9352364B9EA0B860E69B7FB65DD142207F935C73D0B488AD4E3086C5A5DFD"
)

CORE_CNF_NAME = "cover6_closed_f7_r34_i6_FgraveGOW_core.cnf"
CORE_LRAT_NAME = "cover6_closed_f7_r34_i6_FgraveGOW_core.lrat"
MAPPING_NAME = "core_clause_map.tsv"
REDUCTION_REPORT_NAME = "reduction.json"
REPLAY_NAME = "Replay.lean"
LEAN_LOG_NAME = "lean_replay.log"
MANIFEST_NAME = "MANIFEST.json"
PARTIAL_SUFFIX = ".partial"
MAPPING_SOURCE_LABEL = "fgravegow_clause_id"

MAX_CORE_CLAUSES = 50_000
MAX_CORE_CNF_BYTES = 32 * 1024 * 1024
MAX_CORE_LRAT_BYTES = 128 * 1024 * 1024
LEAN_WALL_LIMIT_SECONDS = 600.0
LEAN_JOB_MEMORY_LIMIT_BYTES = 1_536 * 1024 * 1024
LEAN_LOG_LIMIT_BYTES = 8 * 1024 * 1024
POLL_SECONDS = 0.05

LEAN_NAMESPACE = "LRATCatcher.Tests.Cover6D7FgraveGowCoreReplay"
LEAN_THEOREM = "cover6_d7_fgravegow_core_unsat"
LEAN_QUALIFIED_THEOREM = f"{LEAN_NAMESPACE}.{LEAN_THEOREM}"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPOSITORY = Path(__file__).resolve().parents[2]
LRAT_CATCHER = REPOSITORY / "vendor" / "lrat-catcher"
LRAT_CATCHER_BUILD_ROOT = Path(
    r"S:\CodexResearchCache\ramsey-formal\lake-build"
)
LRAT_CATCHER_LEAN_PATH = LRAT_CATCHER_BUILD_ROOT / "lib" / "lean"
HERE = Path(__file__).resolve().parent
TRACKED_DIRECTORY = HERE / "master7_r34_fgravegow_core"
TRACKED_MILESTONE_REPORT = HERE / "MASTER7_R34_FGRAVEGOW_LRAT_CORE_V1.json"
TRACKED_GITATTRIBUTES_NAME = ".gitattributes"
EXTERNAL_MANIFEST_SHA256 = (
    "4D0BABD9CED3154291B7C81675EE8E4F644A649AFE8315E7BB773E9D26412036"
)
EXTERNAL_MANIFEST_BYTES = 9_715
TRACKED_CORE_CNF_BYTES = 289_163
TRACKED_CORE_CNF_SHA256 = (
    "2DD4F2F3359A78163B20B7103804A34E081F71CE436D8332DAE71309A54C0B6E"
)
TRACKED_CORE_LRAT_BYTES = 864_692
TRACKED_CORE_LRAT_SHA256 = (
    "2663E5943CE593EB7E9C3E21D588601AFFD528C419C946CE3B337D4649A1D188"
)
TRACKED_MAPPING_BYTES = 450_424
TRACKED_MAPPING_SHA256 = (
    "4324BD649921CA8EF00673A002D051C7046FE0B5D31144B59A07FAD7BF73D992"
)
TRACKED_CORE_INITIAL_CLAUSES = 5_807
TRACKED_CORE_DERIVED_ADDITIONS = 9_475
MAX_TRACKED_FILE_BYTES = 95 * 1024 * 1024
LEAN_TOOLCHAIN_ROOT = Path(
    r"S:\CodexResearchCache\ramsey-formal\lean-toolchains\leanprover--lean4---v4.30.0"
)
LEAN_EXE = LEAN_TOOLCHAIN_ROOT / "bin" / "lean.exe"
LEAN_VERSION = "4.30.0"
LEAN_EXE_SHA256 = "8132256D484B8ECC4561BEC70ABD1271F4C0D03BADBC3BC272F6C4053AF9FDBC"
TOOLCHAIN_BIN_TREE_FILES = 21
TOOLCHAIN_BIN_TREE_BYTES = 381_505_372
TOOLCHAIN_BIN_TREE_SHA256 = (
    "EE2F0D219C4AE65CC06A247A7555869D22067479A4B3AC74F0764FBE96139DDB"
)
FROZEN_STANDARD_MODULES = {
    "lib/lean/Std/Tactic/BVDecide/LRAT.olean": (
        "E176AE5339E181A2FD16B64912B8043824585F84D279B860D52B9451000CCB6E"
    ),
    "lib/lean/Std/Sat/CNF.olean": (
        "76CD0AF7E0D670E294A38F2C67A556D02442B44F5E96866D37311A76B65D2746"
    ),
}
FROZEN_LRAT_CATCHER_SOURCE_FILES = {
    "LRATCatcher/Basic.lean": (
        "EBA596F276AE5E54C6CF7AD0092DD30513127574C7DC5E4BC5D70CE376D144BE"
    ),
    "LRATCatcher/Kernel.lean": (
        "03E3A3F07A623158F9DA69444E4C82CD0B6F73CC64EAAF13B493BEFF95C8CD9D"
    ),
    "LRATCatcher/Reflect.lean": (
        "1DB3676E4AE0C96B079E79A5AD2CBCC870FAA2731B6B424681B3AFFD228BB1B2"
    ),
    "lakefile.toml": (
        "E75C93ADC0C4F72A0932FD3F84E17BB075ADA99B8B6E3708D2BDDDA22D553DDF"
    ),
    "lean-toolchain": (
        "54727EEC5CBA149C18842E6DEB5C41B369D66455C93CE135D7D5347C782B2325"
    ),
    "lake-manifest.json": (
        "CD4356C2CBDF289ED5CB7643E5DFCDB3C73EA0A84461EFD52305604889CB48AE"
    ),
}
FROZEN_LRAT_CATCHER_BUILD_FILES = {
    "lib/lean/LRATCatcher/Basic.olean": (
        "85147C8B959621FD1683BE57AF6945F69C322449C2A916D1EE31BD1EEEF3502D"
    ),
    "lib/lean/LRATCatcher/Kernel.olean": (
        "FD8A073996EEBDFC97F82DC8D2BB34729AEE1FEEB2557EFC9D8ED074CF745E32"
    ),
    "lib/lean/LRATCatcher/Reflect.olean": (
        "FC4356F894B609D5EDC12DCAAA856E8372618682B0E76B10D1500F575764F251"
    ),
}


class FgraveGowCoreError(ValueError):
    """Raised at the first identity, proof-shape, cap, or replay mismatch."""


def sha256_file(path: Path) -> tuple[str, int]:
    return corelib.sha256_file(path)


def file_metadata(path: Path, *, lines: bool = False) -> dict[str, object]:
    digest, size = sha256_file(path)
    result: dict[str, object] = {
        "name": path.name,
        "bytes": size,
        "sha256": digest,
    }
    if lines:
        count = 0
        with path.open("rb", buffering=8 * 1024 * 1024) as stream:
            for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
                count += block.count(b"\n")
        result["lines"] = count
    return result


def require_absolute_s(path: Path, label: str) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise FgraveGowCoreError(f"{label} must be an absolute S: path: {path}")
    if ".." in parsed.parts:
        raise FgraveGowCoreError(f"{label} must not contain '..': {path}")
    return path


def reject_reparse_components(path: Path, label: str) -> None:
    """Reject junction/symlink escapes below the accepted S: drive root."""

    require_absolute_s(path, label)
    current = path
    drive_root = Path(PureWindowsPath(str(path)).anchor)
    while current != drive_root:
        try:
            status = os.lstat(current)
        except FileNotFoundError:
            current = current.parent
            continue
        attributes = getattr(status, "st_file_attributes", 0)
        if attributes & 0x00000400:  # FILE_ATTRIBUTE_REPARSE_POINT
            raise FgraveGowCoreError(
                f"{label} crosses a reparse point below S: at {current}"
            )
        current = current.parent


def reject_reparse_between(path: Path, root: Path, label: str) -> None:
    """Reject a symlink/junction at or below a fixed local repository root."""

    absolute_path = path.absolute()
    absolute_root = root.absolute()
    try:
        absolute_path.relative_to(absolute_root)
    except ValueError as error:
        raise FgraveGowCoreError(f"{label} is outside the repository root") from error
    current = absolute_path
    while True:
        try:
            status = os.lstat(current)
        except FileNotFoundError:
            pass
        else:
            if getattr(status, "st_file_attributes", 0) & 0x00000400:
                raise FgraveGowCoreError(f"{label} crosses reparse point {current}")
        if current == absolute_root:
            break
        current = current.parent


def directory_tree_identity(path: Path) -> dict[str, object]:
    if not path.is_dir():
        raise FileNotFoundError(path)
    aggregate = hashlib.sha256()
    files = 0
    total_bytes = 0
    entries = sorted(
        (candidate for candidate in path.rglob("*") if candidate.is_file()),
        key=lambda candidate: candidate.relative_to(path).as_posix().casefold(),
    )
    for candidate in entries:
        relative = candidate.relative_to(path).as_posix()
        digest, size = sha256_file(candidate)
        try:
            row = f"{relative}\t{size}\t{digest}\n".encode("ascii")
        except UnicodeEncodeError as error:
            raise FgraveGowCoreError(
                f"non-ASCII path in frozen toolchain tree: {relative}"
            ) from error
        aggregate.update(row)
        files += 1
        total_bytes += size
    return {
        "path": str(path),
        "algorithm": "casefold-sorted relative_path<TAB>bytes<TAB>SHA256<LF>",
        "files": files,
        "bytes": total_bytes,
        "sha256": aggregate.hexdigest().upper(),
    }


def _frozen_files_identity(
    root: Path, expected: dict[str, str], label: str
) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for relative, expected_hash in expected.items():
        path = root / Path(relative)
        digest, size = sha256_file(path)
        if digest != expected_hash:
            raise FgraveGowCoreError(
                f"frozen {label} identity mismatch for {relative}: {digest}"
            )
        result.append(
            {
                "relative_path": relative,
                "bytes": size,
                "sha256": digest,
            }
        )
    return result


def frozen_replay_files() -> list[Path]:
    return (
        [candidate for candidate in (LEAN_TOOLCHAIN_ROOT / "bin").rglob("*") if candidate.is_file()]
        + [LEAN_TOOLCHAIN_ROOT / Path(relative) for relative in FROZEN_STANDARD_MODULES]
        + [
            LRAT_CATCHER / Path(relative)
            for relative in FROZEN_LRAT_CATCHER_SOURCE_FILES
        ]
        + [
            LRAT_CATCHER_BUILD_ROOT / Path(relative)
            for relative in FROZEN_LRAT_CATCHER_BUILD_FILES
        ]
    )


def verify_replay_stack() -> dict[str, object]:
    require_absolute_s(LEAN_EXE, "frozen Lean executable")
    reject_reparse_components(LEAN_EXE, "frozen Lean executable")
    require_absolute_s(LRAT_CATCHER_LEAN_PATH, "direct LRATCatcher build path")
    reject_reparse_components(
        LRAT_CATCHER_LEAN_PATH, "direct LRATCatcher build path"
    )
    lean_digest, lean_bytes = sha256_file(LEAN_EXE)
    if lean_digest != LEAN_EXE_SHA256:
        raise FgraveGowCoreError("frozen Lean executable identity mismatch")
    bin_tree = directory_tree_identity(LEAN_TOOLCHAIN_ROOT / "bin")
    if (
        bin_tree["files"],
        bin_tree["bytes"],
        bin_tree["sha256"],
    ) != (
        TOOLCHAIN_BIN_TREE_FILES,
        TOOLCHAIN_BIN_TREE_BYTES,
        TOOLCHAIN_BIN_TREE_SHA256,
    ):
        raise FgraveGowCoreError("frozen Lean toolchain bin tree identity mismatch")
    standard_modules = _frozen_files_identity(
        LEAN_TOOLCHAIN_ROOT, FROZEN_STANDARD_MODULES, "Lean standard module"
    )
    checker_source_files = _frozen_files_identity(
        LRAT_CATCHER,
        FROZEN_LRAT_CATCHER_SOURCE_FILES,
        "LRATCatcher source/config file",
    )
    checker_build_files = _frozen_files_identity(
        LRAT_CATCHER_BUILD_ROOT,
        FROZEN_LRAT_CATCHER_BUILD_FILES,
        "LRATCatcher compiled module",
    )
    return {
        "status": "PASS_PINNED_SELECTED_LEAN_LRATCATCHER_IDENTITIES",
        "lean_version": LEAN_VERSION,
        "lean_executable": {
            "path": str(LEAN_EXE),
            "bytes": lean_bytes,
            "sha256": lean_digest,
        },
        "toolchain_bin_tree": bin_tree,
        "standard_modules": standard_modules,
        "lratcatcher_source_root": str(LRAT_CATCHER),
        "lratcatcher_build_root": str(LRAT_CATCHER_BUILD_ROOT),
        "lratcatcher_lean_path": str(LRAT_CATCHER_LEAN_PATH),
        "lratcatcher_source_files": checker_source_files,
        "lratcatcher_build_files": checker_build_files,
        "identity_scope": {
            "pinned": (
                "complete toolchain bin tree; direct Std LRAT/CNF modules; "
                "LRATCatcher Basic/Kernel/Reflect source and compiled modules"
            ),
            "not_exhaustive": (
                "Lean.olean and the full transitive imported module closure are "
                "not exhaustively hashed; this is reproducibility provenance, "
                "not an adversarial full-stack immutability guarantee"
            ),
            "runtime_import_path": (
                "direct S: build target; the repository .lake/build junction is bypassed"
            ),
        },
    }


def source_paths(source_dir: Path) -> dict[str, Path]:
    return {
        "cnf": source_dir / SOURCE_CNF_NAME,
        "lrat": source_dir / SOURCE_LRAT_NAME,
        "run_report": source_dir / SOURCE_RUN_REPORT_NAME,
    }


def output_paths(output_dir: Path) -> dict[str, Path]:
    names = {
        "cnf": CORE_CNF_NAME,
        "lrat": CORE_LRAT_NAME,
        "mapping": MAPPING_NAME,
        "reduction": REDUCTION_REPORT_NAME,
        "replay": REPLAY_NAME,
        "lean_log": LEAN_LOG_NAME,
        "manifest": MANIFEST_NAME,
    }
    result = {key: output_dir / name for key, name in names.items()}
    result.update(
        {
            f"{key}_partial": output_dir / f"{path.name}{PARTIAL_SUFFIX}"
            for key, path in tuple(result.items())
        }
    )
    return result


def _json_field(value: object, *keys: str) -> object:
    current = value
    for key in keys:
        if not isinstance(current, dict):
            return None
        current = current.get(key)
    return current


def validate_run_report_payload(report: dict[str, object]) -> None:
    """Freeze the semantic anchors in addition to the report's byte identity."""

    checks = (
        (report.get("status"), "CADICAL_CHECKED_LRAT_CANDIDATE_PENDING_INDEPENDENT_REPLAY"),
        (_json_field(report, "formula", "sha256"), SOURCE_CNF_SHA256),
        (_json_field(report, "formula", "bytes"), SOURCE_CNF_BYTES),
        (_json_field(report, "formula", "lines"), SOURCE_CNF_CLAUSES + 1),
        (_json_field(report, "result", "lrat", "sha256"), SOURCE_LRAT_SHA256),
        (_json_field(report, "result", "lrat", "bytes"), SOURCE_LRAT_BYTES),
        (_json_field(report, "result", "metrics", "lrat_added_clauses"), SOURCE_LRAT_ADDITIONS),
        (_json_field(report, "result", "lrat_published"), True),
        (_json_field(report, "solver", "returncode"), 20),
        (_json_field(report, "selection", "record"), "F`GOW"),
        (_json_field(report, "selection", "source_catalogue_index_zero_based"), 5),
        (_json_field(report, "selection", "incremental_position_one_based"), 6),
    )
    for observed, expected in checks:
        if observed != expected:
            raise FgraveGowCoreError(
                f"F`GOW run-report semantic mismatch: {observed!r} != {expected!r}"
            )


def verify_run_report(path: Path) -> dict[str, object]:
    digest, size = sha256_file(path)
    if (digest, size) != (SOURCE_RUN_REPORT_SHA256, SOURCE_RUN_REPORT_BYTES):
        raise FgraveGowCoreError("F`GOW LRAT run-report identity mismatch")
    report = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(report, dict):
        raise FgraveGowCoreError("F`GOW LRAT run report is not a JSON object")
    validate_run_report_payload(report)
    return {"name": path.name, "bytes": size, "sha256": digest}


def _check_exact_source_analysis(analysis: dict[str, object]) -> None:
    source = analysis["input"]
    proof = analysis["proof"]
    if source["cnf"] != {"bytes": SOURCE_CNF_BYTES, "sha256": SOURCE_CNF_SHA256}:
        raise FgraveGowCoreError("F`GOW CNF identity mismatch")
    if source["lrat"] != {"bytes": SOURCE_LRAT_BYTES, "sha256": SOURCE_LRAT_SHA256}:
        raise FgraveGowCoreError("F`GOW LRAT identity mismatch")
    if (source["variables"], source["initial_clauses"]) != (
        SOURCE_CNF_VARIABLES,
        SOURCE_CNF_CLAUSES,
    ):
        raise FgraveGowCoreError("F`GOW DIMACS dimensions changed")
    if proof["additions"] != SOURCE_LRAT_ADDITIONS:
        raise FgraveGowCoreError("F`GOW LRAT addition count changed")
    if proof["deletion_actions"] != SOURCE_LRAT_DELETION_ACTIONS:
        raise FgraveGowCoreError("F`GOW LRAT deletion-action count changed")
    if proof["deleted_identifiers"] != SOURCE_LRAT_DELETED_IDENTIFIERS:
        raise FgraveGowCoreError("F`GOW LRAT deleted-id count changed")
    if proof["rat_additions"] != 0 or proof["rup_additions"] != proof["additions"]:
        raise corelib.RatReductionUnsupported(
            "F`GOW reduction requires every addition to use RUP hint syntax"
        )


def analyze_exact(source_dir: Path) -> dict[str, object]:
    source_dir = require_absolute_s(source_dir, "source directory")
    if not source_dir.is_dir():
        raise FileNotFoundError(source_dir)
    paths = source_paths(source_dir)
    reject_reparse_components(source_dir, "source directory")
    for key, path in paths.items():
        reject_reparse_components(path, f"source {key}")
    run_report = verify_run_report(paths["run_report"])
    analysis = corelib.analyze(paths["cnf"], paths["lrat"], master_identity=False)
    public = corelib._public_analysis(analysis)
    _check_exact_source_analysis(public)
    for key, expected_hash, expected_bytes in (
        ("cnf", SOURCE_CNF_SHA256, SOURCE_CNF_BYTES),
        ("lrat", SOURCE_LRAT_SHA256, SOURCE_LRAT_BYTES),
    ):
        observed_hash, observed_bytes = sha256_file(paths[key])
        if (observed_hash, observed_bytes) != (expected_hash, expected_bytes):
            raise FgraveGowCoreError(f"source {key} changed during analysis")
    public["source_run_report"] = run_report
    public["status"] = "PASS_EXACT_FGRAVEGOW_ALL_RUP_BACKWARD_CORE_ANALYSIS"
    public["audit"] = {
        "all_additions_rup_syntax": True,
        "rat_additions": 0,
        "forward_hints_rejected_during_indexing": True,
        "backward_closure_from_unique_final_empty_clause": True,
        "semantic_rup_replay_still_required": True,
    }
    public["caps"] = {
        "core_clauses_max": MAX_CORE_CLAUSES,
        "core_cnf_bytes_max": MAX_CORE_CNF_BYTES,
        "core_lrat_bytes_max": MAX_CORE_LRAT_BYTES,
    }
    public["_index"] = analysis["_index"]
    public["_core"] = analysis["_core"]
    return public


def public_analysis(analysis: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in analysis.items() if not key.startswith("_")}


def validate_compact_caps(
    clauses: int, cnf_bytes: int, lrat_bytes: int
) -> dict[str, object]:
    observed = {
        "clauses": clauses,
        "cnf_bytes": cnf_bytes,
        "lrat_bytes": lrat_bytes,
    }
    limits = {
        "clauses": MAX_CORE_CLAUSES,
        "cnf_bytes": MAX_CORE_CNF_BYTES,
        "lrat_bytes": MAX_CORE_LRAT_BYTES,
    }
    for name, value in observed.items():
        if value < 0 or value > limits[name]:
            raise FgraveGowCoreError(
                f"compact core {name} cap exceeded: {value} > {limits[name]}"
            )
    return {"status": "PASS_COMPACT_CORE_CAPS", "observed": observed, "limits": limits}


def _write_new(path: Path, payload: bytes) -> dict[str, object]:
    with path.open("xb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    return {
        "name": path.name,
        "bytes": len(payload),
        "lines": payload.count(b"\n"),
        "sha256": hashlib.sha256(payload).hexdigest().upper(),
    }


def _publish_new(partial: Path, final: Path) -> None:
    if final.exists():
        raise FileExistsError(f"refusing to overwrite {final}")
    os.rename(partial, final)


def lean_source(cnf: Path, lrat: Path) -> bytes:
    cnf_text = cnf.as_posix().replace('"', '\\"')
    lrat_text = lrat.as_posix().replace('"', '\\"')
    return (
        "import LRATCatcher.Reflect\n\n"
        f"namespace {LEAN_NAMESPACE}\n\n"
        "-- Exact frozen-DIMACS core only; no semantic S7 composition here.\n"
        f"lrat_reflect {LEAN_THEOREM}\n"
        f"  \"{cnf_text}\"\n"
        f"  \"{lrat_text}\"\n\n"
        f"#print axioms {LEAN_THEOREM}\n\n"
        f"end {LEAN_NAMESPACE}\n"
    ).encode("utf-8")


def reduce_exact(source_dir: Path, output_dir: Path) -> dict[str, object]:
    source_dir = require_absolute_s(source_dir, "source directory")
    output_dir = require_absolute_s(output_dir, "output directory")
    if output_dir.exists():
        raise FileExistsError(f"refusing existing output directory: {output_dir}")
    if not output_dir.parent.is_dir():
        raise FileNotFoundError(f"output parent does not exist: {output_dir.parent}")
    reject_reparse_components(output_dir.parent, "output parent")
    analysis = analyze_exact(source_dir)
    index = analysis["_index"]
    dependency = analysis["_core"]
    assert isinstance(index, corelib.ProofIndex)
    assert isinstance(dependency, corelib.DependencyCore)
    if dependency.initial_count > MAX_CORE_CLAUSES:
        raise FgraveGowCoreError("dependency core exceeds the 50k-clause cap")

    output_dir.mkdir(exist_ok=False)
    sources = source_paths(source_dir)
    paths = output_paths(output_dir)
    initial_map, cnf_metadata, mapping_metadata = corelib.write_core_cnf(
        sources["cnf"],
        paths["cnf_partial"],
        paths["mapping_partial"],
        SOURCE_CNF_VARIABLES,
        SOURCE_CNF_CLAUSES,
        dependency,
        source_clause_label=MAPPING_SOURCE_LABEL,
    )
    if int(cnf_metadata["bytes"]) > MAX_CORE_CNF_BYTES:
        raise FgraveGowCoreError("core CNF exceeds the 32 MiB cap")
    lrat_metadata = corelib.write_core_lrat(
        sources["lrat"],
        paths["lrat_partial"],
        SOURCE_CNF_CLAUSES,
        index,
        dependency,
        initial_map,
    )
    caps = validate_compact_caps(
        dependency.initial_count,
        int(cnf_metadata["bytes"]),
        int(lrat_metadata["bytes"]),
    )
    for key, expected_hash, expected_bytes in (
        ("cnf", SOURCE_CNF_SHA256, SOURCE_CNF_BYTES),
        ("lrat", SOURCE_LRAT_SHA256, SOURCE_LRAT_BYTES),
    ):
        observed_hash, observed_bytes = sha256_file(sources[key])
        if (observed_hash, observed_bytes) != (expected_hash, expected_bytes):
            raise FgraveGowCoreError(f"source {key} changed during reduction")

    reduced_verification = corelib.verify_reduced_pair(
        paths["cnf_partial"], paths["lrat_partial"]
    )
    mapping_verification = corelib.verify_clause_mapping(
        sources["cnf"],
        paths["cnf_partial"],
        paths["mapping_partial"],
        source_clause_label=MAPPING_SOURCE_LABEL,
    )
    if mapping_verification["status"] != "PASS_EXACT_ORDERED_SUBSEQUENCE":
        raise FgraveGowCoreError("exact source-clause mapping verification failed")
    _verify_core_linkage(
        analysis, reduced_verification, mapping_verification, caps
    )

    replay_payload = lean_source(paths["cnf"], paths["lrat"])
    replay_metadata = _write_new(paths["replay_partial"], replay_payload)
    reduction = {
        **public_analysis(analysis),
        "status": "PASS_REDUCED_FGRAVEGOW_CORE_REPLAY_REQUIRED",
        "generated_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "caps": caps,
        "output": {
            "cnf": {"name": CORE_CNF_NAME, **cnf_metadata},
            "lrat": {"name": CORE_LRAT_NAME, **lrat_metadata},
            "initial_clause_mapping": {"name": MAPPING_NAME, **mapping_metadata},
            "replay_module": {"name": REPLAY_NAME, **{k: v for k, v in replay_metadata.items() if k != "name"}},
        },
        "validation": {
            "reduced_pair": public_analysis(reduced_verification),
            "initial_clause_mapping": mapping_verification,
            "lean_replay": "PENDING",
        },
        "formal_boundary": (
            "exact frozen F`GOW DIMACS leaf only; independent Lean replay pending; "
            "no S7 transport, cover6-d7 theorem, global gluing, or Ramsey bound"
        ),
    }
    reduction_payload = (
        json.dumps(reduction, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    _write_new(paths["reduction_partial"], reduction_payload)

    for key in ("cnf", "lrat", "mapping", "replay", "reduction"):
        _publish_new(paths[f"{key}_partial"], paths[key])
    return reduction


def _verify_reduction_report(
    reduction: dict[str, object],
    analysis: dict[str, object],
    reduced: dict[str, object],
    mapping: dict[str, object],
    caps: dict[str, object],
    artifacts: dict[str, dict[str, object]],
) -> None:
    if reduction.get("status") != "PASS_REDUCED_FGRAVEGOW_CORE_REPLAY_REQUIRED":
        raise FgraveGowCoreError("unexpected reduction report status")
    expected_analysis = public_analysis(analysis)
    for key in ("input", "proof", "core", "audit", "source_run_report"):
        if reduction.get(key) != expected_analysis.get(key):
            raise FgraveGowCoreError(f"reduction report {key} differs from re-analysis")
    if reduction.get("caps") != caps:
        raise FgraveGowCoreError("reduction report cap result differs from artifacts")
    validation = reduction.get("validation")
    if not isinstance(validation, dict):
        raise FgraveGowCoreError("reduction report validation is malformed")
    if validation.get("reduced_pair") != public_analysis(reduced):
        raise FgraveGowCoreError("reduction report reduced-pair claim differs")
    if validation.get("initial_clause_mapping") != mapping:
        raise FgraveGowCoreError("reduction report mapping claim differs")
    if validation.get("lean_replay") != "PENDING":
        raise FgraveGowCoreError("reduction report must leave Lean replay pending")

    claims = reduction.get("output")
    if not isinstance(claims, dict):
        raise FgraveGowCoreError("reduction report output table is malformed")
    key_map = {
        "cnf": "cnf",
        "lrat": "lrat",
        "initial_clause_mapping": "mapping",
        "replay_module": "replay",
    }
    for claim_key, artifact_key in key_map.items():
        claim = claims.get(claim_key)
        if not isinstance(claim, dict):
            raise FgraveGowCoreError(f"missing reduction output claim {claim_key}")
        actual = artifacts[artifact_key]
        for field in ("name", "bytes", "lines", "sha256"):
            if claim.get(field) != actual.get(field):
                raise FgraveGowCoreError(
                    f"reduction output claim {claim_key}.{field} differs"
                )


def _verify_core_linkage(
    analysis: dict[str, object],
    reduced: dict[str, object],
    mapping: dict[str, object],
    caps: dict[str, object],
) -> None:
    """Tie the compact pair back to every source dependency-core count."""

    source_core = analysis.get("core")
    reduced_input = reduced.get("input")
    reduced_proof = reduced.get("proof")
    reduced_core = reduced.get("core")
    cap_observed = caps.get("observed")
    if not all(
        isinstance(value, dict)
        for value in (
            source_core,
            reduced_input,
            reduced_proof,
            reduced_core,
            cap_observed,
        )
    ):
        raise FgraveGowCoreError("malformed core linkage metadata")
    checks = (
        (reduced_input.get("variables"), SOURCE_CNF_VARIABLES, "compact variables"),
        (
            reduced_input.get("initial_clauses"),
            source_core.get("initial_clauses"),
            "compact initial clauses",
        ),
        (
            mapping.get("rows"),
            source_core.get("initial_clauses"),
            "mapping rows",
        ),
        (
            mapping.get("core_clauses"),
            source_core.get("initial_clauses"),
            "mapped core clauses",
        ),
        (
            mapping.get("master_variables"),
            SOURCE_CNF_VARIABLES,
            "mapped source variables",
        ),
        (
            mapping.get("master_clauses"),
            SOURCE_CNF_CLAUSES,
            "mapped source clauses",
        ),
        (
            mapping.get("core_variables"),
            SOURCE_CNF_VARIABLES,
            "mapped compact variables",
        ),
        (
            reduced_proof.get("additions"),
            source_core.get("derived_additions"),
            "compact additions",
        ),
        (
            reduced_core.get("dependency_edges"),
            source_core.get("dependency_edges"),
            "compact dependency edges",
        ),
        (
            reduced_proof.get("deletion_actions"),
            source_core.get("retained_deletion_actions"),
            "compact deletion actions",
        ),
        (
            reduced_proof.get("deleted_identifiers"),
            source_core.get("retained_deleted_identifiers"),
            "compact deleted identifiers",
        ),
        (
            cap_observed.get("clauses"),
            source_core.get("initial_clauses"),
            "capped compact clauses",
        ),
    )
    for observed, expected, label in checks:
        if observed != expected:
            raise FgraveGowCoreError(
                f"{label} does not match source dependency core: "
                f"{observed!r} != {expected!r}"
            )


def verify_core(source_dir: Path, output_dir: Path) -> dict[str, object]:
    source_dir = require_absolute_s(source_dir, "source directory")
    output_dir = require_absolute_s(output_dir, "output directory")
    if not output_dir.is_dir():
        raise FileNotFoundError(output_dir)
    sources = source_paths(source_dir)
    paths = output_paths(output_dir)
    reject_reparse_components(output_dir, "output directory")
    for key in ("cnf", "lrat", "mapping", "reduction", "replay"):
        reject_reparse_components(paths[key], f"core {key}")
    analysis = analyze_exact(source_dir)
    reduced = corelib.verify_reduced_pair(paths["cnf"], paths["lrat"])
    mapping = corelib.verify_clause_mapping(
        sources["cnf"],
        paths["cnf"],
        paths["mapping"],
        source_clause_label=MAPPING_SOURCE_LABEL,
    )
    _, clauses = corelib.read_cnf_header(paths["cnf"])
    caps = validate_compact_caps(
        clauses, paths["cnf"].stat().st_size, paths["lrat"].stat().st_size
    )
    expected_replay = lean_source(paths["cnf"], paths["lrat"])
    if paths["replay"].read_bytes() != expected_replay:
        raise FgraveGowCoreError("Replay.lean path/theorem payload changed")
    reduction = json.loads(paths["reduction"].read_text(encoding="utf-8"))
    if not isinstance(reduction, dict):
        raise FgraveGowCoreError("reduction report is not a JSON object")
    artifacts = {
        key: file_metadata(paths[key], lines=True)
        for key in ("cnf", "lrat", "mapping", "reduction", "replay")
    }
    _verify_core_linkage(analysis, reduced, mapping, caps)
    _verify_reduction_report(reduction, analysis, reduced, mapping, caps, artifacts)
    return {
        "status": "PASS_EXACT_COMPACT_FGRAVEGOW_CORE_REPLAY_REQUIRED",
        "source_analysis": public_analysis(analysis),
        "reduced_pair": public_analysis(reduced),
        "mapping": mapping,
        "caps": caps,
        "artifacts": artifacts,
    }


class WindowsFamilyJob:
    """Aggregate-memory Job Object for Lean and every descendant process."""

    JOB_OBJECT_LIMIT_JOB_MEMORY = 0x00000200
    JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000
    INFORMATION_CLASS = 9

    def __init__(self, memory_limit_bytes: int) -> None:
        if os.name != "nt":
            raise FgraveGowCoreError("Lean family supervision requires Windows")
        if memory_limit_bytes <= 0:
            raise ValueError("Job Object family memory limit must be positive")
        self.memory_limit_bytes = memory_limit_bytes
        self.kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        self.kernel32.CreateJobObjectW.argtypes = (
            ctypes.c_void_p,
            wintypes.LPCWSTR,
        )
        self.kernel32.CreateJobObjectW.restype = wintypes.HANDLE
        self.kernel32.SetInformationJobObject.argtypes = (
            wintypes.HANDLE,
            ctypes.c_int,
            ctypes.c_void_p,
            wintypes.DWORD,
        )
        self.kernel32.SetInformationJobObject.restype = wintypes.BOOL
        self.kernel32.AssignProcessToJobObject.argtypes = (
            wintypes.HANDLE,
            wintypes.HANDLE,
        )
        self.kernel32.AssignProcessToJobObject.restype = wintypes.BOOL
        self.kernel32.QueryInformationJobObject.argtypes = (
            wintypes.HANDLE,
            ctypes.c_int,
            ctypes.c_void_p,
            wintypes.DWORD,
            ctypes.POINTER(wintypes.DWORD),
        )
        self.kernel32.QueryInformationJobObject.restype = wintypes.BOOL
        self.kernel32.TerminateJobObject.argtypes = (
            wintypes.HANDLE,
            wintypes.UINT,
        )
        self.kernel32.TerminateJobObject.restype = wintypes.BOOL
        self.kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
        self.kernel32.CloseHandle.restype = wintypes.BOOL
        self.handle = self.kernel32.CreateJobObjectW(None, None)
        if not self.handle:
            raise ctypes.WinError(ctypes.get_last_error())
        information = lrat_runner._JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        information.BasicLimitInformation.LimitFlags = (
            self.JOB_OBJECT_LIMIT_JOB_MEMORY | self.JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
        )
        information.JobMemoryLimit = memory_limit_bytes
        if not self.kernel32.SetInformationJobObject(
            self.handle,
            self.INFORMATION_CLASS,
            ctypes.byref(information),
            ctypes.sizeof(information),
        ):
            error = ctypes.WinError(ctypes.get_last_error())
            self.close()
            raise error
        self.assigned = False

    def assign(self, process: subprocess.Popen[bytes]) -> None:
        handle = getattr(process, "_handle", None)
        if handle is None or not self.kernel32.AssignProcessToJobObject(
            self.handle, wintypes.HANDLE(int(handle))
        ):
            raise ctypes.WinError(ctypes.get_last_error())
        self.assigned = True

    def peak_memory_bytes(self) -> int:
        information = lrat_runner._JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        if not self.kernel32.QueryInformationJobObject(
            self.handle,
            self.INFORMATION_CLASS,
            ctypes.byref(information),
            ctypes.sizeof(information),
            None,
        ):
            raise ctypes.WinError(ctypes.get_last_error())
        return int(information.PeakJobMemoryUsed)

    def terminate(self) -> None:
        if self.handle and not self.kernel32.TerminateJobObject(self.handle, 1):
            raise ctypes.WinError(ctypes.get_last_error())

    def close(self) -> None:
        if self.handle:
            self.kernel32.CloseHandle(self.handle)
            self.handle = None


class WindowsReadLocks:
    """Hold existing replay inputs open with read sharing but no write/delete."""

    GENERIC_READ = 0x80000000
    FILE_SHARE_READ = 0x00000001
    OPEN_EXISTING = 3
    FILE_ATTRIBUTE_NORMAL = 0x00000080

    def __init__(self, paths: list[Path]) -> None:
        if os.name != "nt":
            raise FgraveGowCoreError("replay input locks require Windows")
        self.paths = paths
        self.kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        self.kernel32.CreateFileW.argtypes = (
            wintypes.LPCWSTR,
            wintypes.DWORD,
            wintypes.DWORD,
            ctypes.c_void_p,
            wintypes.DWORD,
            wintypes.DWORD,
            wintypes.HANDLE,
        )
        self.kernel32.CreateFileW.restype = wintypes.HANDLE
        self.kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
        self.kernel32.CloseHandle.restype = wintypes.BOOL
        self.handles: list[int] = []

    def __enter__(self) -> "WindowsReadLocks":
        invalid = ctypes.c_void_p(-1).value
        try:
            for path in self.paths:
                handle = self.kernel32.CreateFileW(
                    str(path),
                    self.GENERIC_READ,
                    self.FILE_SHARE_READ,
                    None,
                    self.OPEN_EXISTING,
                    self.FILE_ATTRIBUTE_NORMAL,
                    None,
                )
                if int(handle) == invalid:
                    raise ctypes.WinError(
                        ctypes.get_last_error(), f"cannot read-lock replay input {path}"
                    )
                self.handles.append(int(handle))
        except BaseException:
            self.close()
            raise
        return self

    def close(self) -> None:
        while self.handles:
            self.kernel32.CloseHandle(wintypes.HANDLE(self.handles.pop()))

    def __exit__(self, *_unused: object) -> None:
        self.close()


class _THREADENTRY32(ctypes.Structure):
    _fields_ = (
        ("dwSize", wintypes.DWORD),
        ("cntUsage", wintypes.DWORD),
        ("th32ThreadID", wintypes.DWORD),
        ("th32OwnerProcessID", wintypes.DWORD),
        ("tpBasePri", wintypes.LONG),
        ("tpDeltaPri", wintypes.LONG),
        ("dwFlags", wintypes.DWORD),
    )


def resume_suspended_process(process: subprocess.Popen[bytes]) -> None:
    """Resume only after the frozen process has entered its Job Object."""

    if os.name != "nt":
        raise FgraveGowCoreError("suspended Lean launch requires Windows")
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateToolhelp32Snapshot.argtypes = (wintypes.DWORD, wintypes.DWORD)
    kernel32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
    kernel32.Thread32First.argtypes = (
        wintypes.HANDLE,
        ctypes.POINTER(_THREADENTRY32),
    )
    kernel32.Thread32First.restype = wintypes.BOOL
    kernel32.Thread32Next.argtypes = (
        wintypes.HANDLE,
        ctypes.POINTER(_THREADENTRY32),
    )
    kernel32.Thread32Next.restype = wintypes.BOOL
    kernel32.OpenThread.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
    kernel32.OpenThread.restype = wintypes.HANDLE
    kernel32.ResumeThread.argtypes = (wintypes.HANDLE,)
    kernel32.ResumeThread.restype = wintypes.DWORD
    kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
    kernel32.CloseHandle.restype = wintypes.BOOL

    TH32CS_SNAPTHREAD = 0x00000004
    THREAD_SUSPEND_RESUME = 0x0002
    INVALID_HANDLE_VALUE = ctypes.c_void_p(-1).value
    snapshot = kernel32.CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0)
    if int(snapshot) == INVALID_HANDLE_VALUE:
        raise ctypes.WinError(ctypes.get_last_error())
    resumed = 0
    try:
        entry = _THREADENTRY32()
        entry.dwSize = ctypes.sizeof(entry)
        present = kernel32.Thread32First(snapshot, ctypes.byref(entry))
        if not present:
            raise ctypes.WinError(ctypes.get_last_error())
        while present:
            if int(entry.th32OwnerProcessID) == process.pid:
                thread_handle = kernel32.OpenThread(
                    THREAD_SUSPEND_RESUME, False, entry.th32ThreadID
                )
                if not thread_handle:
                    raise ctypes.WinError(ctypes.get_last_error())
                try:
                    previous = kernel32.ResumeThread(thread_handle)
                    if previous == 0xFFFFFFFF:
                        raise ctypes.WinError(ctypes.get_last_error())
                    if previous != 1:
                        raise FgraveGowCoreError(
                            "fresh Lean primary thread had suspension count "
                            f"{previous}, expected exactly 1"
                        )
                    resumed += 1
                finally:
                    kernel32.CloseHandle(thread_handle)
            entry.dwSize = ctypes.sizeof(entry)
            present = kernel32.Thread32Next(snapshot, ctypes.byref(entry))
    finally:
        kernel32.CloseHandle(snapshot)
    if resumed != 1:
        raise FgraveGowCoreError(
            f"expected one suspended primary thread for Lean, resumed {resumed}"
        )


def _terminate_and_wait(
    process: subprocess.Popen[bytes], job: WindowsFamilyJob | None
) -> list[str]:
    """Bound all termination waits; return diagnostics instead of hanging."""

    errors: list[str] = []
    if process.poll() is None:
        terminated_by_job = False
        if job is not None and job.assigned:
            try:
                job.terminate()
                terminated_by_job = True
            except BaseException as error:
                errors.append(f"Job terminate failed: {type(error).__name__}: {error}")
        if not terminated_by_job:
            try:
                process.kill()
            except BaseException as error:
                errors.append(f"process kill failed: {type(error).__name__}: {error}")
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        errors.append("process wait timed out after 10 seconds")
        try:
            process.kill()
        except BaseException as error:
            errors.append(f"fallback kill failed: {type(error).__name__}: {error}")
        try:
            process.wait(timeout=10)
        except BaseException as error:
            errors.append(f"fallback wait failed: {type(error).__name__}: {error}")
    except BaseException as error:
        errors.append(f"process wait failed: {type(error).__name__}: {error}")
    return errors


def parse_axioms(log_text: str) -> list[str]:
    match = re.search(
        rf"'{re.escape(LEAN_QUALIFIED_THEOREM)}' depends on axioms: \[(.*?)\]",
        log_text,
        re.DOTALL,
    )
    if not match:
        return []
    return [item.strip() for item in match.group(1).split(",") if item.strip()]


def axioms_allowed(axioms: list[str]) -> bool:
    native = re.compile(
        rf"{re.escape(LEAN_THEOREM)}\._native\.native_decide\.ax_[0-9]+_[0-9]+"
    )
    return bool(axioms) and all(
        axiom in ALLOWED_AXIOMS or native.fullmatch(axiom) is not None
        for axiom in axioms
    )


def _lean_supervised(
    lean: Path,
    replay_path: Path,
    log_partial: Path,
    *,
    temporary_directory: Path | None = None,
) -> dict[str, object]:
    command = [str(lean), str(replay_path)]
    temporary_directory = temporary_directory or replay_path.parent
    windows_root = r"C:\Windows"
    system32 = str(Path(windows_root) / "System32")
    environment = {
        "SystemRoot": windows_root,
        "WINDIR": windows_root,
        "COMSPEC": str(Path(system32) / "cmd.exe"),
        "PATHEXT": ".COM;.EXE;.BAT;.CMD",
        "PATH": str(LEAN_TOOLCHAIN_ROOT / "bin") + os.pathsep + system32,
        "TEMP": str(temporary_directory),
        "TMP": str(temporary_directory),
        "LEAN_PATH": str(LRAT_CATCHER_LEAN_PATH),
        "LEAN_ABORT_ON_PANIC": "1",
    }
    budget = lrat_runner.CombinedLogBudget(LEAN_LOG_LIMIT_BYTES)
    started = time.perf_counter()
    stop_reason: str | None = None
    returncode: int | None = None
    peak_memory = 0
    launch_error: str | None = None
    process: subprocess.Popen[bytes] | None = None
    job: WindowsFamilyJob | None = None
    thread: threading.Thread | None = None
    with log_partial.open("xb") as log_stream:
        try:
            job = WindowsFamilyJob(LEAN_JOB_MEMORY_LIMIT_BYTES)
            process = subprocess.Popen(
                command,
                cwd=LRAT_CATCHER,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                creationflags=(
                    getattr(subprocess, "CREATE_NO_WINDOW", 0)
                    | getattr(subprocess, "CREATE_SUSPENDED", 0x00000004)
                ),
            )
            job.assign(process)
            resume_suspended_process(process)
            if process.stdout is None:
                raise FgraveGowCoreError("Lean stdout pipe was not created")
            thread = threading.Thread(
                target=budget.copy,
                args=(process.stdout, log_stream),
                name="fgravegow-core-lean-log",
                daemon=True,
            )
            thread.start()
            while process.poll() is None:
                elapsed = time.perf_counter() - started
                peak_memory = max(peak_memory, job.peak_memory_bytes())
                if elapsed >= LEAN_WALL_LIMIT_SECONDS:
                    stop_reason = "WALL_LIMIT"
                elif peak_memory >= LEAN_JOB_MEMORY_LIMIT_BYTES:
                    stop_reason = "JOB_MEMORY_LIMIT"
                elif budget.limit_reached.is_set():
                    stop_reason = "LOG_BYTES_LIMIT"
                elif budget.errors:
                    stop_reason = "LOG_CAPTURE_ERROR"
                if stop_reason is not None:
                    termination_errors = _terminate_and_wait(process, job)
                    if termination_errors:
                        launch_error = "; ".join(termination_errors)
                    break
                time.sleep(POLL_SECONDS)
            if process.poll() is None:
                termination_errors = _terminate_and_wait(process, job)
                if termination_errors:
                    launch_error = "; ".join(termination_errors)
                    stop_reason = stop_reason or "TERMINATION_ERROR"
            else:
                process.wait(timeout=10)
            returncode = process.returncode
            peak_memory = max(peak_memory, job.peak_memory_bytes())
        except BaseException as error:
            launch_error = f"{type(error).__name__}: {error}"
            stop_reason = stop_reason or "LAUNCH_OR_MONITOR_ERROR"
            if process is not None:
                termination_errors = _terminate_and_wait(process, job)
                if termination_errors:
                    launch_error += "; " + "; ".join(termination_errors)
                returncode = process.returncode
        finally:
            if thread is not None:
                thread.join(timeout=10)
            if thread is not None and thread.is_alive():
                stop_reason = "LOG_CAPTURE_THREAD_TIMEOUT"
                if process is not None:
                    termination_errors = _terminate_and_wait(process, job)
                    if termination_errors:
                        launch_error = "; ".join(
                            filter(None, (launch_error, *termination_errors))
                        )
                    if process.stdout is not None:
                        process.stdout.close()
                thread.join(timeout=5)
                if thread.is_alive():
                    launch_error = "; ".join(
                        filter(None, (launch_error, "log thread remained alive after pipe close"))
                    )
            if launch_error:
                message = budget.accepted_prefix(
                    ("Lean supervision error: " + launch_error + "\n").encode(
                        "utf-8", "replace"
                    )
                )
                log_stream.write(message)
            log_stream.flush()
            os.fsync(log_stream.fileno())
            if job is not None:
                job.close()
    elapsed = time.perf_counter() - started
    if stop_reason is None and elapsed >= LEAN_WALL_LIMIT_SECONDS:
        stop_reason = "WALL_LIMIT"
    if stop_reason is None and peak_memory >= LEAN_JOB_MEMORY_LIMIT_BYTES:
        stop_reason = "JOB_MEMORY_LIMIT"
    if stop_reason is None and budget.limit_reached.is_set():
        stop_reason = "LOG_BYTES_LIMIT"
    return {
        "command": command,
        "environment_policy": {
            "inherited": False,
            "lean_path": str(LRAT_CATCHER_LEAN_PATH),
            "path": environment["PATH"],
            "temporary_directory": str(temporary_directory),
        },
        "returncode": returncode,
        "stop_reason": stop_reason,
        "wall_seconds": round(elapsed, 6),
        "peak_job_memory_bytes": peak_memory,
        "job_memory_limit_bytes": LEAN_JOB_MEMORY_LIMIT_BYTES,
        "wall_limit_seconds": LEAN_WALL_LIMIT_SECONDS,
        "log_limit_bytes": LEAN_LOG_LIMIT_BYTES,
        "job_object_assigned": bool(job is not None and job.assigned),
        "launch_suspended_until_job_assignment": True,
        "job_memory_scope": "lean plus every descendant process",
        "kill_on_job_close": True,
        "launch_error": launch_error,
    }


def replay_lean(source_dir: Path, output_dir: Path) -> dict[str, object]:
    source_dir = require_absolute_s(source_dir, "source directory")
    output_dir = require_absolute_s(output_dir, "output directory")
    verification = verify_core(source_dir, output_dir)
    paths = output_paths(output_dir)
    for key in ("lean_log", "manifest", "lean_log_partial", "manifest_partial"):
        if paths[key].exists():
            raise FileExistsError(f"refusing existing replay artifact: {paths[key]}")
    core_keys = ("cnf", "lrat", "mapping", "reduction", "replay")
    replay_inputs = [paths[key] for key in core_keys] + frozen_replay_files()
    with WindowsReadLocks(replay_inputs):
        stack_before = verify_replay_stack()
        locked_artifacts_before = {
            key: file_metadata(paths[key], lines=True) for key in core_keys
        }
        if locked_artifacts_before != verification["artifacts"]:
            raise FgraveGowCoreError(
                "compact artifacts changed before replay inputs were read-locked"
            )
        supervision = _lean_supervised(
            LEAN_EXE, paths["replay"], paths["lean_log_partial"]
        )
        _publish_new(paths["lean_log_partial"], paths["lean_log"])
        log_text = paths["lean_log"].read_text(encoding="utf-8", errors="replace")
        axioms = parse_axioms(log_text)
        artifacts_after = {
            key: file_metadata(paths[key], lines=True) for key in core_keys
        }
        stack_after = verify_replay_stack()
        core_identity_unchanged = artifacts_after == locked_artifacts_before
        stack_identity_unchanged = stack_after == stack_before
        success = (
            supervision["stop_reason"] is None
            and supervision["returncode"] == 0
            and LEAN_QUALIFIED_THEOREM in log_text
            and "sorryAx" not in log_text
            and "declaration uses 'sorry'" not in log_text
            and axioms_allowed(axioms)
            and core_identity_unchanged
            and stack_identity_unchanged
        )
        artifacts = artifacts_after
        artifacts["lean_log"] = file_metadata(paths["lean_log"], lines=True)
        manifest = {
            "schema_version": 1,
            "status": (
                "PASS_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY"
                if success
                else "FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY_FAILED"
            ),
            "source": {
                "cnf": {
                    "name": SOURCE_CNF_NAME,
                    "bytes": SOURCE_CNF_BYTES,
                    "sha256": SOURCE_CNF_SHA256,
                    "variables": SOURCE_CNF_VARIABLES,
                    "clauses": SOURCE_CNF_CLAUSES,
                },
                "lrat": {
                    "name": SOURCE_LRAT_NAME,
                    "bytes": SOURCE_LRAT_BYTES,
                    "sha256": SOURCE_LRAT_SHA256,
                    "additions": SOURCE_LRAT_ADDITIONS,
                    "rat_additions": 0,
                },
                "run_report": verification["source_analysis"]["source_run_report"],
            },
            "dependency_core": verification["source_analysis"]["core"],
            "caps": verification["caps"],
            "artifacts": artifacts,
            "validation": {
                "rup_syntax": "ALL_399094_ADDITIONS_RUP_NO_RAT",
                "forward_hint_policy": "REJECTED_DURING_FULL_INDEX",
                "backward_closure": "FINAL_EMPTY_DEPENDENCY_CLOSURE",
                "mapping": verification["mapping"],
                "reduced_pair": verification["reduced_pair"],
                "replay_input_locks": {
                    "windows_share_mode": "FILE_SHARE_READ_ONLY",
                    "write_and_delete_sharing": False,
                    "locked_file_count": len(replay_inputs),
                },
                "post_replay_identity": {
                    "compact_artifacts_unchanged": core_identity_unchanged,
                    "lean_lratcatcher_stack_unchanged": stack_identity_unchanged,
                },
                "lean": {
                    "status": (
                        "LEAN_LRAT_REPLAY_PASS"
                        if success
                        else "LEAN_LRAT_REPLAY_FAILED"
                    ),
                    "theorem": LEAN_QUALIFIED_THEOREM,
                    "axioms": axioms,
                    "axioms_allowed": axioms_allowed(axioms),
                    "frozen_stack": stack_before,
                    "supervision": supervision,
                },
            },
            "formal_boundary": (
                "Lean proves UNSAT only for an exact compact ordered subsequence of "
                "the frozen F`GOW leaf CNF. S7 transport and composition into a "
                "cover6-d7 theorem or Ramsey bound remain separate obligations."
            ),
        }
        manifest_payload = (
            json.dumps(manifest, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8")
        _write_new(paths["manifest_partial"], manifest_payload)
        _publish_new(paths["manifest_partial"], paths["manifest"])
    return manifest


def tracked_paths() -> dict[str, Path]:
    result = {
        "cnf": TRACKED_DIRECTORY / CORE_CNF_NAME,
        "lrat": TRACKED_DIRECTORY / CORE_LRAT_NAME,
        "mapping": TRACKED_DIRECTORY / MAPPING_NAME,
        "reduction": TRACKED_DIRECTORY / REDUCTION_REPORT_NAME,
        "replay": TRACKED_DIRECTORY / REPLAY_NAME,
        "lean_log": TRACKED_DIRECTORY / LEAN_LOG_NAME,
        "manifest": TRACKED_DIRECTORY / MANIFEST_NAME,
        "gitattributes": TRACKED_DIRECTORY / TRACKED_GITATTRIBUTES_NAME,
        "milestone": TRACKED_MILESTONE_REPORT,
    }
    result.update(
        {
            f"{key}_partial": path.with_name(path.name + PARTIAL_SUFFIX)
            for key, path in tuple(result.items())
        }
    )
    return result


def _copy_new(source: Path, target: Path) -> dict[str, object]:
    digest = hashlib.sha256()
    size = lines = 0
    with (
        source.open("rb", buffering=8 * 1024 * 1024) as inp,
        target.open("xb") as out,
    ):
        for block in iter(lambda: inp.read(8 * 1024 * 1024), b""):
            out.write(block)
            digest.update(block)
            size += len(block)
            lines += block.count(b"\n")
        out.flush()
        os.fsync(out.fileno())
    return {
        "name": target.name.removesuffix(PARTIAL_SUFFIX),
        "bytes": size,
        "lines": lines,
        "sha256": digest.hexdigest().upper(),
    }


def tracked_replay_source() -> bytes:
    relative_root = Path("../../scripts/r45_d12_cover9_universal") / TRACKED_DIRECTORY.name
    return lean_source(relative_root / CORE_CNF_NAME, relative_root / CORE_LRAT_NAME)


def _assert_no_absolute_paths(payload: bytes, label: str) -> None:
    text_payload = payload.decode("utf-8")
    forbidden = (
        re.search(r"[A-Za-z]:[\\/]", text_payload),
        re.search(r"\\{2,}[^\\]", text_payload),
        re.search(r"/(?:home|tmp|Users|var)/", text_payload),
        "file://" in text_payload,
        "C:\\Users\\migra" in text_payload,
    )
    if any(forbidden):
        raise FgraveGowCoreError(f"{label} contains an absolute path")


def _expected_tracked_core_identity(key: str) -> tuple[str, int]:
    expected = {
        "cnf": (TRACKED_CORE_CNF_SHA256, TRACKED_CORE_CNF_BYTES),
        "lrat": (TRACKED_CORE_LRAT_SHA256, TRACKED_CORE_LRAT_BYTES),
        "mapping": (TRACKED_MAPPING_SHA256, TRACKED_MAPPING_BYTES),
    }
    return expected[key]


def publish_tracked(source_dir: Path, external_core_dir: Path) -> dict[str, object]:
    reject_reparse_between(HERE, REPOSITORY, "tracked artifact parent")
    if TRACKED_DIRECTORY.exists():
        raise FileExistsError(f"refusing existing tracked directory: {TRACKED_DIRECTORY}")
    if TRACKED_MILESTONE_REPORT.exists():
        raise FileExistsError(
            f"refusing existing tracked milestone report: {TRACKED_MILESTONE_REPORT}"
        )
    verification = verify_core(source_dir, external_core_dir)
    external_paths = output_paths(external_core_dir)
    external_manifest = file_metadata(external_paths["manifest"], lines=True)
    if (
        external_manifest["sha256"],
        external_manifest["bytes"],
    ) != (EXTERNAL_MANIFEST_SHA256, EXTERNAL_MANIFEST_BYTES):
        raise FgraveGowCoreError("external replay manifest identity mismatch")
    external_report = json.loads(
        external_paths["manifest"].read_text(encoding="utf-8")
    )
    if external_report.get("status") != "PASS_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY":
        raise FgraveGowCoreError("external compact core has no passing Lean replay")

    TRACKED_DIRECTORY.mkdir(exist_ok=False)
    paths = tracked_paths()
    copied: dict[str, dict[str, object]] = {}
    for key in ("cnf", "lrat", "mapping"):
        copied[key] = _copy_new(external_paths[key], paths[f"{key}_partial"])
        expected_hash, expected_bytes = _expected_tracked_core_identity(key)
        if (copied[key]["sha256"], copied[key]["bytes"]) != (
            expected_hash,
            expected_bytes,
        ):
            raise FgraveGowCoreError(f"tracked {key} copy identity mismatch")
        if int(copied[key]["bytes"]) >= MAX_TRACKED_FILE_BYTES:
            raise FgraveGowCoreError(
                f"tracked {key} exceeds the conservative 95 MiB Git cap"
            )

    replay_payload = tracked_replay_source()
    _assert_no_absolute_paths(replay_payload, "tracked Replay.lean")
    replay_metadata = _write_new(paths["replay_partial"], replay_payload)
    attributes_payload = (
        b"*.cnf binary\n"
        b"*.lrat binary\n"
        b"*.tsv binary\n"
        b"*.json -text\n"
        b"*.lean -text\n"
        b"*.log -text\n"
    )
    attributes_metadata = _write_new(
        paths["gitattributes_partial"], attributes_payload
    )

    partial_reduced = corelib.verify_reduced_pair(
        paths["cnf_partial"], paths["lrat_partial"]
    )
    partial_mapping = corelib.verify_clause_mapping(
        source_paths(source_dir)["cnf"],
        paths["cnf_partial"],
        paths["mapping_partial"],
        source_clause_label=MAPPING_SOURCE_LABEL,
    )
    caps = validate_compact_caps(
        TRACKED_CORE_INITIAL_CLAUSES,
        int(copied["cnf"]["bytes"]),
        int(copied["lrat"]["bytes"]),
    )
    _verify_core_linkage(
        verification["source_analysis"], partial_reduced, partial_mapping, caps
    )
    artifacts = {
        "cnf": {
            **copied["cnf"],
            "variables": SOURCE_CNF_VARIABLES,
            "clauses": TRACKED_CORE_INITIAL_CLAUSES,
        },
        "lrat": {
            **copied["lrat"],
            "additions": TRACKED_CORE_DERIVED_ADDITIONS,
            "deletion_actions": 8_283,
            "deleted_identifiers": 9_758,
        },
        "initial_clause_mapping": {
            **copied["mapping"],
            "rows": TRACKED_CORE_INITIAL_CLAUSES,
        },
        "replay_module": {
            "name": REPLAY_NAME,
            **{key: value for key, value in replay_metadata.items() if key != "name"},
        },
        "gitattributes": {
            "name": TRACKED_GITATTRIBUTES_NAME,
            **{
                key: value
                for key, value in attributes_metadata.items()
                if key != "name"
            },
        },
    }
    reduction = {
        "schema_version": 1,
        "status": "PASS_TRACKED_FGRAVEGOW_CORE_REPLAY_REQUIRED",
        "source": verification["source_analysis"]["input"],
        "source_run_report": verification["source_analysis"]["source_run_report"],
        "dependency_core": verification["source_analysis"]["core"],
        "caps": caps,
        "artifacts": artifacts,
        "reducer_implementation": {
            "algorithm": "all-RUP full index, backward closure, dense id remap v1",
            "reducer": file_metadata(Path(__file__)),
            "core_library": file_metadata(Path(corelib.__file__)),
        },
        "validation": {
            "external_certified_core_manifest": external_manifest,
            "mapping": partial_mapping,
            "reduced_pair": public_analysis(partial_reduced),
            "tracked_lean_replay": "PENDING",
        },
        "formal_boundary": (
            "portable tracked copy of the exact frozen F`GOW leaf core only; "
            "tracked-path Lean replay pending; no S7 orbit composition, "
            "cover6-d7 theorem, global gluing, or Ramsey bound"
        ),
    }
    reduction_payload = (
        json.dumps(reduction, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    _assert_no_absolute_paths(reduction_payload, "tracked reduction report")
    _write_new(paths["reduction_partial"], reduction_payload)
    for key in ("cnf", "lrat", "mapping", "replay", "gitattributes", "reduction"):
        _publish_new(paths[f"{key}_partial"], paths[key])
    return reduction


def _verify_tracked_reduction(
    reduction: dict[str, object], artifacts: dict[str, dict[str, object]]
) -> None:
    if reduction.get("status") != "PASS_TRACKED_FGRAVEGOW_CORE_REPLAY_REQUIRED":
        raise FgraveGowCoreError("tracked reduction status mismatch")
    claims = reduction.get("artifacts")
    if not isinstance(claims, dict):
        raise FgraveGowCoreError("tracked reduction artifacts table is malformed")
    mapping = {
        "cnf": "cnf",
        "lrat": "lrat",
        "initial_clause_mapping": "mapping",
        "replay_module": "replay",
        "gitattributes": "gitattributes",
    }
    for claim_key, actual_key in mapping.items():
        claim = claims.get(claim_key)
        if not isinstance(claim, dict):
            raise FgraveGowCoreError(f"tracked reduction misses {claim_key}")
        for field in ("name", "bytes", "lines", "sha256"):
            if claim.get(field) != artifacts[actual_key].get(field):
                raise FgraveGowCoreError(
                    f"tracked reduction claim {claim_key}.{field} differs"
                )
    implementation = reduction.get("reducer_implementation")
    if not isinstance(implementation, dict):
        raise FgraveGowCoreError("tracked reduction misses reducer implementation")
    current_code = {
        "reducer": file_metadata(Path(__file__)),
        "core_library": file_metadata(Path(corelib.__file__)),
    }
    for key, metadata in current_code.items():
        if implementation.get(key) != metadata:
            raise FgraveGowCoreError(f"tracked reduction {key} identity differs")


def verify_tracked(source_dir: Path) -> dict[str, object]:
    if not TRACKED_DIRECTORY.is_dir():
        raise FileNotFoundError(TRACKED_DIRECTORY)
    reject_reparse_between(TRACKED_DIRECTORY, REPOSITORY, "tracked artifact directory")
    paths = tracked_paths()
    analysis = analyze_exact(source_dir)
    reduced = corelib.verify_reduced_pair(paths["cnf"], paths["lrat"])
    mapping = corelib.verify_clause_mapping(
        source_paths(source_dir)["cnf"],
        paths["cnf"],
        paths["mapping"],
        source_clause_label=MAPPING_SOURCE_LABEL,
    )
    caps = validate_compact_caps(
        TRACKED_CORE_INITIAL_CLAUSES,
        paths["cnf"].stat().st_size,
        paths["lrat"].stat().st_size,
    )
    _verify_core_linkage(analysis, reduced, mapping, caps)
    for key in ("cnf", "lrat", "mapping"):
        observed_hash, observed_bytes = sha256_file(paths[key])
        if (observed_hash, observed_bytes) != _expected_tracked_core_identity(key):
            raise FgraveGowCoreError(f"tracked {key} frozen identity mismatch")
    if paths["replay"].read_bytes() != tracked_replay_source():
        raise FgraveGowCoreError("tracked Replay.lean payload mismatch")
    replay_payload = paths["replay"].read_bytes()
    reduction_payload = paths["reduction"].read_bytes()
    _assert_no_absolute_paths(replay_payload, "tracked Replay.lean")
    _assert_no_absolute_paths(reduction_payload, "tracked reduction report")
    expected_attributes = (
        b"*.cnf binary\n*.lrat binary\n*.tsv binary\n*.json -text\n"
        b"*.lean -text\n*.log -text\n"
    )
    if paths["gitattributes"].read_bytes() != expected_attributes:
        raise FgraveGowCoreError("tracked .gitattributes payload mismatch")
    artifacts = {
        key: file_metadata(paths[key], lines=True)
        for key in ("cnf", "lrat", "mapping", "reduction", "replay", "gitattributes")
    }
    reduction = json.loads(reduction_payload.decode("utf-8"))
    if not isinstance(reduction, dict):
        raise FgraveGowCoreError("tracked reduction is not a JSON object")
    _verify_tracked_reduction(reduction, artifacts)
    return {
        "status": "PASS_EXACT_TRACKED_FGRAVEGOW_CORE_REPLAY_REQUIRED",
        "source_analysis": public_analysis(analysis),
        "reduced_pair": public_analysis(reduced),
        "mapping": mapping,
        "caps": caps,
        "artifacts": artifacts,
    }


def _portable_stack(stack: dict[str, object]) -> dict[str, object]:
    executable = stack["lean_executable"]
    bin_tree = stack["toolchain_bin_tree"]
    return {
        "status": stack["status"],
        "lean_version": stack["lean_version"],
        "lean_executable": {
            "name": "lean.exe",
            "bytes": executable["bytes"],
            "sha256": executable["sha256"],
        },
        "toolchain_bin_tree": {
            key: value for key, value in bin_tree.items() if key != "path"
        },
        "standard_modules": stack["standard_modules"],
        "lratcatcher_source_files": stack["lratcatcher_source_files"],
        "lratcatcher_build_files": stack["lratcatcher_build_files"],
        "identity_scope": stack["identity_scope"],
        "toolchain_identifier": "leanprover/lean4:v4.30.0",
    }


def _portable_supervision(supervision: dict[str, object]) -> dict[str, object]:
    return {
        "command": ["lean.exe", REPLAY_NAME],
        "working_directory": "vendor/lrat-catcher",
        "environment_policy": {
            "inherited": False,
            "lean_path": "frozen LRATCatcher build recorded in frozen_stack",
            "path": "frozen Lean bin plus Windows System32",
            "temporary_directory": "external S: cache (not tracked)",
        },
        "returncode": supervision["returncode"],
        "stop_reason": supervision["stop_reason"],
        "wall_seconds": supervision["wall_seconds"],
        "peak_job_memory_bytes": supervision["peak_job_memory_bytes"],
        "job_memory_limit_bytes": supervision["job_memory_limit_bytes"],
        "wall_limit_seconds": supervision["wall_limit_seconds"],
        "log_limit_bytes": supervision["log_limit_bytes"],
        "job_object_assigned": supervision["job_object_assigned"],
        "launch_suspended_until_job_assignment": supervision[
            "launch_suspended_until_job_assignment"
        ],
        "job_memory_scope": supervision["job_memory_scope"],
        "kill_on_job_close": supervision["kill_on_job_close"],
        "launch_error": supervision["launch_error"],
    }


def _tracked_manifest_payload(
    verification: dict[str, object],
    artifacts: dict[str, dict[str, object]],
    stack: dict[str, object],
    supervision: dict[str, object],
    axioms: list[str],
    success: bool,
    identity_unchanged: bool,
) -> bytes:
    manifest = {
        "schema_version": 1,
        "status": (
            "PASS_TRACKED_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY"
            if success
            else "TRACKED_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY_FAILED"
        ),
        "source_fgravegow_leaf": {
            "cnf": {
                "name": SOURCE_CNF_NAME,
                "bytes": SOURCE_CNF_BYTES,
                "sha256": SOURCE_CNF_SHA256,
                "variables": SOURCE_CNF_VARIABLES,
                "clauses": SOURCE_CNF_CLAUSES,
            },
            "lrat": {
                "name": SOURCE_LRAT_NAME,
                "bytes": SOURCE_LRAT_BYTES,
                "sha256": SOURCE_LRAT_SHA256,
                "additions": SOURCE_LRAT_ADDITIONS,
                "rat_additions": 0,
            },
            "run_report": verification["source_analysis"]["source_run_report"],
            "external_core_manifest": {
                "name": MANIFEST_NAME,
                "bytes": EXTERNAL_MANIFEST_BYTES,
                "sha256": EXTERNAL_MANIFEST_SHA256,
                "storage": "external cache, not tracked",
            },
        },
        "selection": {
            "record": "F`GOW",
            "source_catalogue_index_zero_based": 5,
            "incremental_position_one_based": 6,
            "conditioned_level": 2,
        },
        "dependency_core": verification["source_analysis"]["core"],
        "caps": verification["caps"],
        "artifacts": artifacts,
        "validation": {
            "source_proof_syntax": "399094 RUP additions, zero RAT",
            "forward_hint_policy": "all forward hints rejected during full indexing",
            "backward_closure": "unique final empty-clause dependency closure",
            "mapping": verification["mapping"],
            "reduced_pair": verification["reduced_pair"],
            "post_replay_artifacts_unchanged": identity_unchanged,
            "lean": {
                "status": "LEAN_LRAT_REPLAY_PASS" if success else "LEAN_LRAT_REPLAY_FAILED",
                "theorem": LEAN_QUALIFIED_THEOREM,
                "axioms": axioms,
                "axioms_allowed": axioms_allowed(axioms),
                "frozen_stack": _portable_stack(stack),
                "supervision": _portable_supervision(supervision),
            },
        },
        "eol_policy": (
            "CNF, LRAT, and TSV are Git binary; JSON, Lean, and log are -text "
            "so frozen byte hashes are not rewritten"
        ),
        "formal_boundary": (
            "Lean proves UNSAT only for the exact tracked ordered-subsequence "
            "core of the frozen F`GOW leaf CNF. This does not prove encoder "
            "semantics, S7 orbit coverage/composition, a cover6-d7 theorem, "
            "global gluing, a Ramsey-number bound, or a major discovery."
        ),
    }
    payload = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")
    _assert_no_absolute_paths(payload, "tracked MANIFEST.json")
    return payload


def _milestone_payload(
    manifest: dict[str, object], manifest_metadata: dict[str, object]
) -> bytes:
    report = {
        "schema_version": 1,
        "status": (
            "PASS_MASTER7_R34_FGRAVEGOW_TRACKED_CORE_V1"
            if manifest["status"]
            == "PASS_TRACKED_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY"
            else "MASTER7_R34_FGRAVEGOW_TRACKED_CORE_V1_FAILED"
        ),
        "milestone": (
            "the exact F`GOW conditioned leaf has a compact tracked RUP core "
            "independently replayed by Lean/LRATCatcher"
        ),
        "artifact_directory": TRACKED_DIRECTORY.name,
        "source_fgravegow_leaf": manifest["source_fgravegow_leaf"],
        "selection": manifest["selection"],
        "dependency_core": manifest["dependency_core"],
        "artifacts": {
            **manifest["artifacts"],
            "manifest": manifest_metadata,
        },
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
            "This turns one previously solver-only F`GOW result into a small, "
            "portable, hash-frozen Lean-replayed certificate. It is a rigorous "
            "leaf checkpoint, not the remaining S7 composition theorem."
        ),
        "remaining": (
            "formalize and prove the relevant S7 transport/coverage and compose "
            "all required branches before any cover6-d7 or Ramsey claim"
        ),
        "formal_boundary": manifest["formal_boundary"],
    }
    payload = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
    _assert_no_absolute_paths(payload, "tracked milestone report")
    return payload


def replay_tracked(source_dir: Path, temporary_directory: Path) -> dict[str, object]:
    temporary_directory = require_absolute_s(
        temporary_directory, "tracked replay temporary directory"
    )
    if not temporary_directory.is_dir():
        raise FileNotFoundError(temporary_directory)
    reject_reparse_components(
        temporary_directory, "tracked replay temporary directory"
    )
    verification = verify_tracked(source_dir)
    paths = tracked_paths()
    for key in (
        "lean_log",
        "manifest",
        "milestone",
        "lean_log_partial",
        "manifest_partial",
        "milestone_partial",
    ):
        if paths[key].exists():
            raise FileExistsError(f"refusing existing tracked replay artifact: {paths[key]}")
    core_keys = ("cnf", "lrat", "mapping", "reduction", "replay", "gitattributes")
    replay_inputs = [paths[key] for key in core_keys] + frozen_replay_files()
    with WindowsReadLocks(replay_inputs):
        stack_before = verify_replay_stack()
        before = {key: file_metadata(paths[key], lines=True) for key in core_keys}
        if before != verification["artifacts"]:
            raise FgraveGowCoreError("tracked artifacts changed before replay lock")
        supervision = _lean_supervised(
            LEAN_EXE,
            paths["replay"],
            paths["lean_log_partial"],
            temporary_directory=temporary_directory,
        )
        _publish_new(paths["lean_log_partial"], paths["lean_log"])
        log_text = paths["lean_log"].read_text(encoding="utf-8", errors="replace")
        _assert_no_absolute_paths(
            paths["lean_log"].read_bytes(), "tracked Lean replay log"
        )
        axioms = parse_axioms(log_text)
        after = {key: file_metadata(paths[key], lines=True) for key in core_keys}
        stack_after = verify_replay_stack()
        identity_unchanged = before == after and stack_before == stack_after
        success = (
            supervision["stop_reason"] is None
            and supervision["returncode"] == 0
            and axioms_allowed(axioms)
            and "sorryAx" not in log_text
            and "declaration uses 'sorry'" not in log_text
            and identity_unchanged
        )
        artifacts = dict(after)
        artifacts["lean_log"] = file_metadata(paths["lean_log"], lines=True)
        manifest_payload = _tracked_manifest_payload(
            verification,
            artifacts,
            stack_before,
            supervision,
            axioms,
            success,
            identity_unchanged,
        )
        _write_new(paths["manifest_partial"], manifest_payload)
        _publish_new(paths["manifest_partial"], paths["manifest"])
        manifest = json.loads(manifest_payload.decode("utf-8"))
        manifest_metadata = file_metadata(paths["manifest"], lines=True)
        milestone_payload = _milestone_payload(manifest, manifest_metadata)
        _write_new(paths["milestone_partial"], milestone_payload)
        _publish_new(paths["milestone_partial"], paths["milestone"])
    return {
        "status": manifest["status"],
        "manifest": manifest_metadata,
        "milestone": file_metadata(paths["milestone"], lines=True),
        "lean": manifest["validation"]["lean"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        choices=(
            "analyze",
            "reduce",
            "verify-core",
            "replay",
            "publish-tracked",
            "verify-tracked",
            "replay-tracked",
        ),
        nargs="?",
        default="analyze",
    )
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--temporary-directory", type=Path)
    args = parser.parse_args()
    if args.command == "analyze":
        result = public_analysis(analyze_exact(args.source_dir))
    elif args.command == "reduce":
        if args.output_dir is None:
            parser.error("reduce requires --output-dir")
        result = reduce_exact(args.source_dir, args.output_dir)
    elif args.command == "verify-core":
        if args.output_dir is None:
            parser.error("verify-core requires --output-dir")
        result = verify_core(args.source_dir, args.output_dir)
    elif args.command == "replay":
        if args.output_dir is None:
            parser.error("replay requires --output-dir")
        result = replay_lean(args.source_dir, args.output_dir)
    elif args.command == "publish-tracked":
        if args.output_dir is None:
            parser.error("publish-tracked requires external --output-dir")
        result = publish_tracked(args.source_dir, args.output_dir)
    elif args.command == "verify-tracked":
        result = verify_tracked(args.source_dir)
    else:
        if args.temporary_directory is None:
            parser.error("replay-tracked requires --temporary-directory on S:")
        result = replay_tracked(args.source_dir, args.temporary_directory)
    print(json.dumps(result, indent=2, sort_keys=True))
    if (
        args.command in ("replay", "replay-tracked")
        and result.get("status")
        not in (
            "PASS_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY",
            "PASS_TRACKED_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY",
        )
    ):
        raise SystemExit(2)


if __name__ == "__main__":
    main()
