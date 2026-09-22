#!/usr/bin/env python3
"""Generate compact semantic witnesses for an R34/F7 dependency core.

The input is a compact core CNF plus ``core_clause_map.tsv`` as emitted by
the parameterised R34 reducer.  No materialised F7 formula, SAT solver, LRAT
proof, ``S:`` path, or assignment-space enumeration is used.  Every selected
clause is reconstructed in the exact order of Lean's ``branchSource``:

* the 699 degree-seven base clauses;
* K7 blocker instances from the packed conditioned-cube catalogues;
* projected K6 blocker instances from the packed catalogues;
* the 21 representative unit clauses from the frozen leaf registry.

For every retained K7 clause the generator records the canonical orbit
witness ``representative + 6 * permutationRank``.  For every retained K6
clause it first chooses the canonical full lift ``min (fixed, ones)`` and then
records that lift's orbit witness.  Codes are densely packed little-endian in
15 bits, exactly as consumed by
``R44Cover6Master7R34FgraveGowSemantics.lean``.

The default command is a read-only audit of the tracked F`GOW core.  ``emit``
uses exclusive creation and never overwrites an artifact.  ``verify``
rebuilds the expected bytes in memory and compares existing artifacts.
"""

from __future__ import annotations

import argparse
import bisect
import csv
import functools
import hashlib
import itertools
import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from . import audit_cover6_d7_min_center_source as source
from . import certify_cover6_conditioned_orbit_witnesses as witnesses
from . import cover6_d7_r34_leaf_registry as registry


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]

MASTER8_INDEXED_SOURCE = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master8IndexedSource.lean"
)
MASTER7_INDEXED_SOURCE = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master7R34IndexedSource.lean"
)
FGRAVEGOW_CORE_MODULE = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master7R34FgraveGowCore.lean"
)
FGRAVEGOW_SEMANTICS_MODULE = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master7R34FgraveGowSemantics.lean"
)
FGRAVEGOW_CORE_DIRECTORY = HERE / "master7_r34_fgravegow_core"

PAYLOAD_NAME = "MASTER7_R34_FGRAVEGOW_CORE_SEMANTIC_WITNESSES_V1.bin"
MANIFEST_NAME = "MASTER7_R34_FGRAVEGOW_CORE_SEMANTIC_PAYLOAD_V1.json"
PAYLOAD_PATH = HERE / PAYLOAD_NAME
MANIFEST_PATH = HERE / MANIFEST_NAME

SCHEMA_VERSION = 1
ALGORITHM = "cover6-d7-r34-selected-core-semantics-v1"
GLOBAL_VARIABLES = 66
BASE_CLAUSES = 699
ROOT_FREE_K7_CLAUSES = 4_127_760
ROOT_CONTAINING_K6_CLAUSES = 183_960
F7_CLAUSES = 4_312_419
BRANCH_CLAUSES = 4_312_440
UNIT_CLAUSES = 21
CUBE_DIGITS = 7
WITNESS_BITS = 15
WITNESS_CHUNK_SIZE = 1_800

BLOCK_COUNTS = {3: 15_480, 4: 15_480, 5: 10_200, 6: 4_680, 7: 2_520}
LOCAL_COUNTS = {2: 360, 3: 540, 4: 360, 5: 300}

D7_NEW_PAYLOAD_BYTES = 110_880
D7_NEW_PAYLOAD_SHA256 = (
    "D1C8FD62254BA0F4DE852F6817F1CA2BD68C12958F8C41AF733C732F321A0446"
)
D7_NEW_BLOCK_BYTES = 108_360
D7_NEW_BLOCK_SHA256 = (
    "C0CBF568B5D75FEF9FBD0D09545EE96F6932CEC480C2966AED22FCD61D763A58"
)
D7_NEW_LOCAL_BYTES = 2_520
D7_NEW_LOCAL_SHA256 = (
    "28D228113D7A70903E41389723892FFFF698C52989EAE80646F47E43C246B770"
)
FULL_K7_CUBE_PAYLOAD_SHA256 = (
    "50891F9AD69F4AA260835028BF750F7CD993DE6246178A46DA0D3D7CB21004F3"
)
FULL_K6_CUBE_PAYLOAD_SHA256 = (
    "9C040F9FBDF2A6FE1EF214FED5C084B5EBB19D6EADB5E722AB7B8C417F42F81F"
)

FGRAVEGOW_EXPECTED_COUNTS = {
    "base": 168,
    "root_free_k7": 3_227,
    "root_containing_k6": 2_396,
    "unit": 16,
}
FGRAVEGOW_EXPECTED_WITNESSES = 5_623
FGRAVEGOW_EXPECTED_PAYLOAD_CHARACTERS = 14_058
FGRAVEGOW_EXPECTED_PAYLOAD_SHA256 = (
    "2CD6F423E9053A83E65D093FFB33BDAB53AB42FB2A0ABAE334BF51D364E62E38"
)
FGRAVEGOW_CORE_INDICES_DEFINITION = "fgraveGowCoreZeroBasedIndices"
FGRAVEGOW_WITNESS_CHUNKS_DEFINITION = "d7CoreWitnessChunks"


class D7CoreSemanticPayloadError(ValueError):
    """Raised at the first layout, clause, witness, or artifact mismatch."""


Cube = tuple[int, int]
Witness = tuple[int, int]
Clause = tuple[int, ...]


@dataclass(frozen=True)
class ClauseRange:
    first: int
    last: int
    family: str
    vertices: tuple[int, ...]
    neighbour_count: int
    catalogue_count: int


@dataclass(frozen=True)
class ClauseLocation:
    family: str
    source_clause_id: int
    vertices: tuple[int, ...] = ()
    neighbour_count: int | None = None
    catalogue_index: int | None = None
    unit_position: int | None = None


@dataclass(frozen=True)
class CoreRow:
    core_clause_id: int
    source_clause_id: int
    clause_sha256: str
    clause: Clause
    raw: bytes


@dataclass(frozen=True)
class SemanticRow:
    core: CoreRow
    location: ClauseLocation
    cube: Cube | None = None
    full_lift: Cube | None = None
    lift_multiplicity: int | None = None
    witness: Witness | None = None


@dataclass(frozen=True)
class CatalogueBundle:
    block: dict[int, tuple[Cube, ...]]
    local: dict[int, tuple[Cube, ...]]
    metadata: dict[str, object]


@dataclass(frozen=True)
class SemanticBundle:
    payload: bytes
    manifest: dict[str, object]
    rows: tuple[SemanticRow, ...]


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def digest_lines(lines: Iterable[str]) -> str:
    return sha256_bytes("".join(lines).encode("ascii"))


def file_metadata(path: Path, *, lines: bool = False) -> dict[str, int | str]:
    digest = hashlib.sha256()
    size = 0
    line_count = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
            size += len(block)
            if lines:
                line_count += block.count(b"\n")
    result: dict[str, int | str] = {
        "name": path.name,
        "bytes": size,
        "sha256": digest.hexdigest().upper(),
    }
    if lines:
        result["lines"] = line_count
    return result


def mapping_label(spec: registry.LeafSpec) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", spec.slug).lower() + "_clause_id"


def select_leaf(slug: str) -> registry.LeafSpec:
    spec = registry.LEAF_BY_SLUG.get(slug)
    if spec is None:
        raise D7CoreSemanticPayloadError(f"unknown R34 leaf: {slug!r}")
    if spec.disposition == "EXCLUDED_DIRECT_MOTIF_ORACLE":
        raise D7CoreSemanticPayloadError(
            f"{slug} closes by the direct motif oracle and has no SAT core route"
        )
    return spec


def _require_payload(payload: str, entries: int, digest: str, label: str) -> str:
    if len(payload) != entries * CUBE_DIGITS:
        raise D7CoreSemanticPayloadError(
            f"{label} length changed: {len(payload)} != {entries * CUBE_DIGITS}"
        )
    if any(character not in witnesses.ALPHABET for character in payload):
        raise D7CoreSemanticPayloadError(f"{label} contains a non-alphabet character")
    observed = sha256_bytes(payload.encode("ascii"))
    if observed != digest:
        raise D7CoreSemanticPayloadError(
            f"{label} identity changed: {observed} != {digest}"
        )
    return payload


def _decode_sections(
    payload: str, counts: Sequence[tuple[int, int]], label: str
) -> dict[int, tuple[Cube, ...]]:
    result: dict[int, tuple[Cube, ...]] = {}
    offset = 0
    for neighbour_count, count in counts:
        characters = count * CUBE_DIGITS
        section = payload[offset : offset + characters]
        if len(section) != characters:
            raise D7CoreSemanticPayloadError(f"truncated {label} a={neighbour_count}")
        cubes = tuple(
            witnesses.decode_cube(section[index : index + CUBE_DIGITS])
            for index in range(0, len(section), CUBE_DIGITS)
        )
        if len(cubes) != count:
            raise D7CoreSemanticPayloadError(f"decoded {label} count changed")
        result[neighbour_count] = cubes
        offset += characters
    if offset != len(payload):
        raise D7CoreSemanticPayloadError(f"unexpected {label} payload suffix")
    return result


@functools.cache
def load_catalogues(
    new_payload_path: Path = source.D7_NEW_CUBE_PAYLOAD,
    master8_indexed_source: Path = MASTER8_INDEXED_SOURCE,
) -> CatalogueBundle:
    """Decode the exact packed catalogues used by Lean's branchSource."""

    try:
        new_bytes = new_payload_path.read_bytes()
    except OSError as error:
        raise D7CoreSemanticPayloadError(
            f"cannot read D7 packed cube asset: {new_payload_path}"
        ) from error
    if len(new_bytes) != D7_NEW_PAYLOAD_BYTES:
        raise D7CoreSemanticPayloadError("D7 packed cube asset byte count changed")
    if sha256_bytes(new_bytes) != D7_NEW_PAYLOAD_SHA256:
        raise D7CoreSemanticPayloadError("D7 packed cube asset SHA-256 changed")
    try:
        new_payload = new_bytes.decode("ascii")
    except UnicodeDecodeError as error:
        raise D7CoreSemanticPayloadError("D7 packed cube asset is not ASCII") from error

    new_block = _require_payload(
        new_payload[:D7_NEW_BLOCK_BYTES],
        BLOCK_COUNTS[3],
        D7_NEW_BLOCK_SHA256,
        "D7 K7/a=3 cube payload",
    )
    new_local = _require_payload(
        new_payload[D7_NEW_BLOCK_BYTES:],
        LOCAL_COUNTS[2],
        D7_NEW_LOCAL_SHA256,
        "D7 K6/a=2 cube payload",
    )

    try:
        reused_block, reused_local = witnesses.indexed_source_payloads(
            master8_indexed_source
        )
    except (OSError, witnesses.ConditionedWitnessError) as error:
        raise D7CoreSemanticPayloadError(
            "cannot validate the reused Master8 packed cube payloads"
        ) from error

    full_block = _require_payload(
        new_block + reused_block,
        sum(BLOCK_COUNTS.values()),
        FULL_K7_CUBE_PAYLOAD_SHA256,
        "full D7 K7 cube payload",
    )
    full_local = _require_payload(
        new_local + reused_local,
        sum(LOCAL_COUNTS.values()),
        FULL_K6_CUBE_PAYLOAD_SHA256,
        "full D7 projected K6 cube payload",
    )
    block = _decode_sections(full_block, tuple(BLOCK_COUNTS.items()), "K7")
    local = _decode_sections(full_local, tuple(LOCAL_COUNTS.items()), "K6")

    expected_block_counts = {key: len(value) for key, value in block.items()}
    expected_local_counts = {key: len(value) for key, value in local.items()}
    if expected_block_counts != BLOCK_COUNTS or expected_local_counts != LOCAL_COUNTS:
        raise D7CoreSemanticPayloadError("decoded catalogue counts changed")

    return CatalogueBundle(
        block,
        local,
        {
            "d7_new_cube_asset": file_metadata(new_payload_path),
            "master8_indexed_source": file_metadata(master8_indexed_source, lines=True),
            "full_k7": {
                "entries": sum(BLOCK_COUNTS.values()),
                "characters": len(full_block),
                "sha256": sha256_bytes(full_block.encode("ascii")),
                "section_counts": {str(key): value for key, value in BLOCK_COUNTS.items()},
            },
            "projected_k6": {
                "entries": sum(LOCAL_COUNTS.values()),
                "characters": len(full_local),
                "sha256": sha256_bytes(full_local.encode("ascii")),
                "section_counts": {str(key): value for key, value in LOCAL_COUNTS.items()},
            },
        },
    )


@functools.cache
def declarative_ranges() -> tuple[tuple[ClauseRange, ...], tuple[ClauseRange, ...]]:
    root_free: list[ClauseRange] = []
    next_id = BASE_CLAUSES + 1
    for vertices in itertools.combinations(range(1, 12), 7):
        neighbour_count = sum(vertex <= 7 for vertex in vertices)
        count = BLOCK_COUNTS.get(neighbour_count, 0)
        if count:
            root_free.append(
                ClauseRange(
                    next_id,
                    next_id + count - 1,
                    "root_free_k7",
                    vertices,
                    neighbour_count,
                    count,
                )
            )
        next_id += count
    if next_id - 1 != BASE_CLAUSES + ROOT_FREE_K7_CLAUSES:
        raise D7CoreSemanticPayloadError("K7 branchSource range arithmetic changed")

    root_containing: list[ClauseRange] = []
    for vertices in itertools.combinations(range(1, 12), 6):
        neighbour_count = sum(vertex <= 7 for vertex in vertices)
        count = LOCAL_COUNTS.get(neighbour_count, 0)
        if count:
            root_containing.append(
                ClauseRange(
                    next_id,
                    next_id + count - 1,
                    "root_containing_k6",
                    vertices,
                    neighbour_count,
                    count,
                )
            )
        next_id += count
    if next_id - 1 != F7_CLAUSES:
        raise D7CoreSemanticPayloadError("K6 branchSource range arithmetic changed")
    return tuple(root_free), tuple(root_containing)


def _range_location(source_clause_id: int, ranges: Sequence[ClauseRange]) -> ClauseLocation:
    ends = [item.last for item in ranges]
    position = bisect.bisect_left(ends, source_clause_id)
    if position == len(ranges):
        raise D7CoreSemanticPayloadError(
            f"source clause {source_clause_id} is outside its declarative range"
        )
    item = ranges[position]
    if source_clause_id < item.first:
        raise D7CoreSemanticPayloadError(
            f"source clause {source_clause_id} falls in a zero-width slice"
        )
    return ClauseLocation(
        item.family,
        source_clause_id,
        item.vertices,
        item.neighbour_count,
        source_clause_id - item.first,
    )


def classify_source_clause(source_clause_id: int) -> ClauseLocation:
    if not 1 <= source_clause_id <= BRANCH_CLAUSES:
        raise D7CoreSemanticPayloadError(
            f"branchSource clause id is out of range: {source_clause_id}"
        )
    if source_clause_id <= BASE_CLAUSES:
        return ClauseLocation("base", source_clause_id)
    root_free, root_containing = declarative_ranges()
    if source_clause_id <= BASE_CLAUSES + ROOT_FREE_K7_CLAUSES:
        return _range_location(source_clause_id, root_free)
    if source_clause_id <= F7_CLAUSES:
        return _range_location(source_clause_id, root_containing)
    return ClauseLocation(
        "unit",
        source_clause_id,
        unit_position=source_clause_id - F7_CLAUSES - 1,
    )


def instantiate(cube: Cube, vertices: Sequence[int]) -> Clause:
    variables = source.subset_variables(vertices)
    ones, fixed = cube
    if ones & ~fixed or fixed >> len(variables):
        raise D7CoreSemanticPayloadError("malformed cube for selected embedding")
    return tuple(
        -variables[position] if (ones >> position) & 1 else variables[position]
        for position in range(len(variables))
        if (fixed >> position) & 1
    )


def reconstruct_branch_clause(
    location: ClauseLocation,
    spec: registry.LeafSpec,
    catalogues: CatalogueBundle,
) -> tuple[Clause, Cube | None]:
    if location.family == "base":
        return source.base_clauses()[location.source_clause_id - 1], None
    if location.family in ("root_free_k7", "root_containing_k6"):
        if location.neighbour_count is None or location.catalogue_index is None:
            raise D7CoreSemanticPayloadError("conditioned clause lacks coordinates")
        family = (
            catalogues.block
            if location.family == "root_free_k7"
            else catalogues.local
        )
        try:
            cube = family[location.neighbour_count][location.catalogue_index]
        except (KeyError, IndexError) as error:
            raise D7CoreSemanticPayloadError(
                f"catalogue index is out of range at source clause "
                f"{location.source_clause_id}"
            ) from error
        return instantiate(cube, location.vertices), cube
    if location.family == "unit":
        if location.unit_position is None or not 0 <= location.unit_position < UNIT_CLAUSES:
            raise D7CoreSemanticPayloadError("unit clause position is out of range")
        return (spec.cube[location.unit_position],), None
    raise D7CoreSemanticPayloadError(f"unknown clause family: {location.family}")


def _read_mapping(path: Path, spec: registry.LeafSpec) -> list[tuple[int, int, str]]:
    with path.open("r", encoding="ascii", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        expected = ["core_clause_id", mapping_label(spec), "clause_sha256"]
        if reader.fieldnames != expected:
            raise D7CoreSemanticPayloadError(
                f"unexpected core mapping header: {reader.fieldnames!r} != {expected!r}"
            )
        result = []
        for expected_core_id, row in enumerate(reader, 1):
            try:
                core_id = int(row["core_clause_id"])
                source_id = int(row[mapping_label(spec)])
            except (TypeError, ValueError) as error:
                raise D7CoreSemanticPayloadError("non-integer core mapping field") from error
            digest = row["clause_sha256"]
            if core_id != expected_core_id:
                raise D7CoreSemanticPayloadError("core mapping ids are not consecutive")
            if not re.fullmatch(r"[0-9A-F]{64}", digest or ""):
                raise D7CoreSemanticPayloadError(
                    f"malformed clause digest at core row {core_id}"
                )
            if not 1 <= source_id <= BRANCH_CLAUSES:
                raise D7CoreSemanticPayloadError(
                    f"source id out of range at core row {core_id}"
                )
            result.append((core_id, source_id, digest))
    if not result:
        raise D7CoreSemanticPayloadError("empty core mapping")
    if any(left[1] >= right[1] for left, right in zip(result, result[1:])):
        raise D7CoreSemanticPayloadError(
            "core source ids are not strictly increasing in branchSource order"
        )
    return result


def _read_core_cnf(
    path: Path, mapping: Sequence[tuple[int, int, str]]
) -> tuple[CoreRow, ...]:
    expected_header = f"p cnf {GLOBAL_VARIABLES} {len(mapping)}\n".encode("ascii")
    with path.open("rb") as stream:
        header = stream.readline()
        if header != expected_header:
            raise D7CoreSemanticPayloadError(
                f"unexpected core CNF header: {header!r} != {expected_header!r}"
            )
        clauses: list[tuple[Clause, bytes]] = []
        for line_number, raw in enumerate(stream, 2):
            try:
                fields = tuple(map(int, raw.split()))
            except ValueError as error:
                raise D7CoreSemanticPayloadError(
                    f"non-integer core CNF row {line_number}"
                ) from error
            if len(fields) < 2 or fields[-1] != 0 or 0 in fields[:-1]:
                raise D7CoreSemanticPayloadError(
                    f"malformed core CNF row {line_number}"
                )
            clause = fields[:-1]
            if any(not 1 <= abs(literal) <= GLOBAL_VARIABLES for literal in clause):
                raise D7CoreSemanticPayloadError(
                    f"literal out of range at core CNF row {line_number}"
                )
            if raw != source.clause_line(clause):
                raise D7CoreSemanticPayloadError(
                    f"non-canonical core CNF row {line_number}"
                )
            clauses.append((clause, raw))
    if len(clauses) != len(mapping):
        raise D7CoreSemanticPayloadError(
            f"core CNF clause count changed: {len(clauses)} != {len(mapping)}"
        )

    result = []
    for (core_id, source_id, expected_digest), (clause, raw) in zip(
        mapping, clauses, strict=True
    ):
        observed_digest = sha256_bytes(raw)
        if observed_digest != expected_digest:
            raise D7CoreSemanticPayloadError(
                f"clause digest mismatch at core row {core_id}"
            )
        result.append(CoreRow(core_id, source_id, observed_digest, clause, raw))
    return tuple(result)


def read_core(core_directory: Path, spec: registry.LeafSpec) -> tuple[
    tuple[CoreRow, ...], dict[str, object]
]:
    base = spec.target_name.removesuffix(".cnf")
    cnf = core_directory / f"{base}_core.cnf"
    mapping_path = core_directory / "core_clause_map.tsv"
    if not core_directory.is_dir():
        raise D7CoreSemanticPayloadError(f"core directory is missing: {core_directory}")
    mapping = _read_mapping(mapping_path, spec)
    rows = _read_core_cnf(cnf, mapping)
    return rows, {
        "core_cnf": file_metadata(cnf, lines=True),
        "core_clause_mapping": file_metadata(mapping_path, lines=True),
    }


@functools.cache
def orbit_witness_index() -> dict[Cube, Witness]:
    try:
        result = witnesses.orbit_witness_index()
    except witnesses.ConditionedWitnessError as error:
        raise D7CoreSemanticPayloadError("cube orbit witness index failed") from error
    if len(result) != source.CUBE_COUNT:
        raise D7CoreSemanticPayloadError("cube orbit witness index size changed")
    return result


@functools.cache
def canonical_lifts(neighbour_count: int) -> dict[Cube, tuple[Cube, int, Witness]]:
    """Map projected cubes to min-(fixed,ones) full lifts and witnesses."""

    if neighbour_count not in LOCAL_COUNTS:
        raise D7CoreSemanticPayloadError(
            f"unsupported projected K6 neighbour count: {neighbour_count}"
        )
    grouped: dict[Cube, list[Cube]] = defaultdict(list)
    for full in orbit_witness_index():
        if source.compatible_with_root(full, neighbour_count):
            projected = (
                source.project_nonroot(full[0]),
                source.project_nonroot(full[1]),
            )
            grouped[projected].append(full)
    result: dict[Cube, tuple[Cube, int, Witness]] = {}
    for projected, candidates in grouped.items():
        ordered = tuple(sorted(candidates, key=lambda cube: (cube[1], cube[0])))
        chosen = ordered[0]
        witness = orbit_witness_index()[chosen]
        try:
            checked_witness, checked_full = witnesses.verify_projected_lift_witness(
                projected, neighbour_count, witness
            )
        except witnesses.ConditionedWitnessError as error:
            raise D7CoreSemanticPayloadError(
                "canonical projected K6 lift witness failed"
            ) from error
        if checked_witness != witness or checked_full != chosen:
            raise D7CoreSemanticPayloadError("canonical K6 lift verification changed")
        result[projected] = chosen, len(ordered), witness
    return result


def _extract_reference_payload(path: Path, definition: str) -> tuple[str, ...]:
    try:
        source_text = path.read_text(encoding="utf-8")
        chunks = witnesses.extract_lean_string_array(source_text, definition)
    except (OSError, witnesses.ConditionedWitnessError) as error:
        raise D7CoreSemanticPayloadError(
            f"cannot extract Lean witness table {definition}"
        ) from error
    if not chunks or any(not chunk for chunk in chunks):
        raise D7CoreSemanticPayloadError("Lean witness table contains an empty chunk")
    return chunks


def _verify_core_indices(
    rows: Sequence[CoreRow], path: Path, definition: str
) -> dict[str, object]:
    try:
        source_text = path.read_text(encoding="utf-8")
        observed = witnesses.extract_lean_nat_array(source_text, definition)
    except (OSError, witnesses.ConditionedWitnessError) as error:
        raise D7CoreSemanticPayloadError(
            f"cannot extract Lean core index table {definition}"
        ) from error
    expected = tuple(row.source_clause_id - 1 for row in rows)
    if observed != expected:
        raise D7CoreSemanticPayloadError(
            "Lean core index table differs from core_clause_map.tsv"
        )
    return {
        "module": file_metadata(path, lines=True),
        "definition": definition,
        "entries": len(observed),
        "zero_based_indices_sha256": digest_lines(f"{index}\n" for index in observed),
        "exactly_matches_mapping": True,
    }


def _family_summary(rows: Sequence[SemanticRow], family: str) -> dict[str, object]:
    selected = [row for row in rows if row.location.family == family]
    ids = [row.core.source_clause_id for row in selected]
    return {
        "retained_clauses": len(selected),
        "core_clause_id_span": (
            [selected[0].core.core_clause_id, selected[-1].core.core_clause_id]
            if selected
            else []
        ),
        "source_clause_id_span": [min(ids), max(ids)] if ids else [],
        "selected_source_clause_ids_sha256": digest_lines(
            f"{source_id}\n" for source_id in ids
        ),
        "clause_widths": {
            str(width): count
            for width, count in sorted(
                Counter(len(row.core.clause) for row in selected).items()
            )
        },
    }


def _semantic_view_digest(rows: Sequence[SemanticRow]) -> str:
    lines = []
    for row in rows:
        location = row.location
        fields = [
            str(row.core.core_clause_id),
            str(row.core.source_clause_id),
            location.family,
            ",".join(map(str, location.vertices)),
            "" if location.neighbour_count is None else str(location.neighbour_count),
            "" if location.catalogue_index is None else str(location.catalogue_index),
            row.core.clause_sha256,
        ]
        if row.cube is not None:
            fields.extend((f"{row.cube[0]:06X}", f"{row.cube[1]:06X}"))
        else:
            fields.extend(("", ""))
        if row.full_lift is not None:
            fields.extend((f"{row.full_lift[0]:06X}", f"{row.full_lift[1]:06X}"))
        else:
            fields.extend(("", ""))
        fields.extend(
            (
                "" if row.lift_multiplicity is None else str(row.lift_multiplicity),
                "" if row.witness is None else str(row.witness[0]),
                "" if row.witness is None else str(row.witness[1]),
            )
        )
        lines.append("\t".join(fields) + "\n")
    return digest_lines(lines)


def payload_chunks(payload: bytes, size: int = WITNESS_CHUNK_SIZE) -> tuple[str, ...]:
    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError as error:
        raise D7CoreSemanticPayloadError("witness payload is not ASCII") from error
    if size <= 0:
        raise D7CoreSemanticPayloadError("witness chunk size must be positive")
    return tuple(text[offset : offset + size] for offset in range(0, len(text), size))


def lean_table_source(
    payload: bytes, spec: registry.LeafSpec, counts: dict[str, int]
) -> bytes:
    """Render an optional pure-data Lean table for a future generic consumer."""

    safe = re.sub(r"[^A-Za-z0-9]", "", spec.slug)
    chunks = payload_chunks(payload)
    rows = "\n".join(f'  "{chunk}"' + ("," if index + 1 < len(chunks) else "")
                     for index, chunk in enumerate(chunks))
    return (
        f"namespace LRATCatcher.Tests.Cover6D7R34{safe}SemanticPayloadData\n\n"
        f"def catalogueIndex : Nat := {spec.source_catalogue_index_zero_based}\n"
        f"def familyCounts : Array Nat := #[{counts['base']}, "
        f"{counts['root_free_k7']}, {counts['root_containing_k6']}, "
        f"{counts['unit']}]\n"
        f"def witnessBits : Nat := {WITNESS_BITS}\n"
        f"def witnessChunks : Array String := #[\n{rows}\n]\n\n"
        f"end LRATCatcher.Tests.Cover6D7R34{safe}SemanticPayloadData\n"
    ).encode("utf-8")


def build_bundle(
    core_directory: Path = FGRAVEGOW_CORE_DIRECTORY,
    slug: str = "FgraveGOW",
    *,
    new_payload_path: Path = source.D7_NEW_CUBE_PAYLOAD,
    master8_indexed_source: Path = MASTER8_INDEXED_SOURCE,
    master7_indexed_source: Path = MASTER7_INDEXED_SOURCE,
    reference_core_module: Path | None = FGRAVEGOW_CORE_MODULE,
    reference_core_indices_definition: str | None = FGRAVEGOW_CORE_INDICES_DEFINITION,
    reference_semantics_module: Path | None = FGRAVEGOW_SEMANTICS_MODULE,
    reference_witness_definition: str | None = FGRAVEGOW_WITNESS_CHUNKS_DEFINITION,
) -> SemanticBundle:
    registry.audit_registry()
    spec = select_leaf(slug)
    catalogues = load_catalogues(new_payload_path, master8_indexed_source)
    core_rows, core_metadata = read_core(core_directory, spec)

    semantic_rows: list[SemanticRow] = []
    ordered_witnesses: list[Witness] = []
    lift_multiplicities: Counter[int] = Counter()
    for core in core_rows:
        location = classify_source_clause(core.source_clause_id)
        expected_clause, cube = reconstruct_branch_clause(location, spec, catalogues)
        if core.clause != expected_clause:
            raise D7CoreSemanticPayloadError(
                f"branchSource clause mismatch at core row {core.core_clause_id}, "
                f"source clause {core.source_clause_id}, family {location.family}"
            )
        full_lift: Cube | None = None
        lift_multiplicity: int | None = None
        witness: Witness | None = None
        if location.family == "root_free_k7":
            if cube is None:
                raise D7CoreSemanticPayloadError("K7 row lacks its cube")
            try:
                witness = orbit_witness_index()[cube]
                witnesses.verify_cube_witness(cube, witness)
            except (KeyError, witnesses.ConditionedWitnessError) as error:
                raise D7CoreSemanticPayloadError(
                    f"K7 orbit witness failed at core row {core.core_clause_id}"
                ) from error
            ordered_witnesses.append(witness)
        elif location.family == "root_containing_k6":
            if cube is None or location.neighbour_count is None:
                raise D7CoreSemanticPayloadError("K6 row lacks projected coordinates")
            try:
                full_lift, lift_multiplicity, witness = canonical_lifts(
                    location.neighbour_count
                )[cube]
            except KeyError as error:
                raise D7CoreSemanticPayloadError(
                    f"K6 projected cube lacks a canonical lift at core row "
                    f"{core.core_clause_id}"
                ) from error
            lift_multiplicities[lift_multiplicity] += 1
            ordered_witnesses.append(witness)
        semantic_rows.append(
            SemanticRow(
                core,
                location,
                cube,
                full_lift,
                lift_multiplicity,
                witness,
            )
        )

    counts = Counter(row.location.family for row in semantic_rows)
    expected_families = {"base", "root_free_k7", "root_containing_k6", "unit"}
    if set(counts) - expected_families:
        raise D7CoreSemanticPayloadError("unexpected semantic family in selected core")
    count_table = {family: counts[family] for family in (
        "base", "root_free_k7", "root_containing_k6", "unit"
    )}
    if count_table["root_free_k7"] + count_table["root_containing_k6"] != len(
        ordered_witnesses
    ):
        raise D7CoreSemanticPayloadError("selected witness count arithmetic changed")

    try:
        payload_text = witnesses.pack_witnesses(tuple(ordered_witnesses))
        decoded = witnesses.unpack_witnesses(payload_text, len(ordered_witnesses))
    except witnesses.ConditionedWitnessError as error:
        raise D7CoreSemanticPayloadError("dense witness packing failed") from error
    if decoded != tuple(ordered_witnesses):
        raise D7CoreSemanticPayloadError("dense witness round trip changed")
    payload = payload_text.encode("ascii")
    payload_sha256 = sha256_bytes(payload)

    core_index_reference: dict[str, object] | None = None
    if (reference_core_module is None) != (reference_core_indices_definition is None):
        raise D7CoreSemanticPayloadError("partial Lean core-index reference")
    if reference_core_module is not None and reference_core_indices_definition is not None:
        core_index_reference = _verify_core_indices(
            core_rows, reference_core_module, reference_core_indices_definition
        )

    witness_reference: dict[str, object] | None = None
    if (reference_semantics_module is None) != (reference_witness_definition is None):
        raise D7CoreSemanticPayloadError("partial Lean witness-table reference")
    if reference_semantics_module is not None and reference_witness_definition is not None:
        reference_chunks = _extract_reference_payload(
            reference_semantics_module, reference_witness_definition
        )
        reference_payload = "".join(reference_chunks).encode("ascii")
        if reference_payload != payload:
            raise D7CoreSemanticPayloadError(
                "generated witness payload differs from the Lean semantic table"
            )
        if reference_chunks != payload_chunks(payload):
            raise D7CoreSemanticPayloadError(
                "generated witness chunking differs from the Lean semantic table"
            )
        witness_reference = {
            "module": file_metadata(reference_semantics_module, lines=True),
            "definition": reference_witness_definition,
            "chunks": len(reference_chunks),
            "chunk_size": WITNESS_CHUNK_SIZE,
            "exactly_matches_generated_payload_and_chunks": True,
        }

    if slug == "FgraveGOW":
        if count_table != FGRAVEGOW_EXPECTED_COUNTS:
            raise D7CoreSemanticPayloadError(
                f"F`GOW taxonomy changed: {count_table} != "
                f"{FGRAVEGOW_EXPECTED_COUNTS}"
            )
        if len(ordered_witnesses) != FGRAVEGOW_EXPECTED_WITNESSES:
            raise D7CoreSemanticPayloadError("F`GOW witness count changed")
        if len(payload) != FGRAVEGOW_EXPECTED_PAYLOAD_CHARACTERS:
            raise D7CoreSemanticPayloadError("F`GOW witness payload length changed")
        if payload_sha256 != FGRAVEGOW_EXPECTED_PAYLOAD_SHA256:
            raise D7CoreSemanticPayloadError(
                f"F`GOW witness payload identity changed: {payload_sha256}"
            )

    unit_rows = [row for row in semantic_rows if row.location.family == "unit"]
    witness_stats = Counter(witness[0] for witness in ordered_witnesses)
    permutation_ranks = [witness[1] for witness in ordered_witnesses]
    lean_table = lean_table_source(payload, spec, count_table)
    generator_metadata = file_metadata(Path(__file__), lines=True)
    manifest: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "status": "PASS_EXACT_D7_R34_SELECTED_CORE_SEMANTIC_PAYLOAD",
        "algorithm": ALGORITHM,
        "selection": {
            "slug": spec.slug,
            "record": spec.record,
            "catalogue_index_zero_based": spec.source_catalogue_index_zero_based,
            "incremental_position_one_based": spec.incremental_position_one_based,
            "branch_source_clauses": BRANCH_CLAUSES,
            "representative_units": list(spec.cube),
        },
        "inputs": {
            **core_metadata,
            "master7_indexed_source": file_metadata(master7_indexed_source, lines=True),
            "catalogue_payloads": catalogues.metadata,
            "generator": generator_metadata,
        },
        "taxonomy": {
            "ordering": "strict branchSource clause-id order",
            "all_selected_clauses_equal_exact_python_reconstruction_of_branchSource": True,
            "selected_clauses": len(semantic_rows),
            "family_counts": count_table,
            "families": {
                family: _family_summary(semantic_rows, family)
                for family in ("base", "root_free_k7", "root_containing_k6", "unit")
            },
            "ordered_semantic_view_sha256": _semantic_view_digest(semantic_rows),
            "unit_tail": {
                "retained_positions_zero_based": [
                    row.location.unit_position for row in unit_rows
                ],
                "retained_literals": [row.core.clause[0] for row in unit_rows],
            },
        },
        "witness_payload": {
            "name": PAYLOAD_NAME if slug == "FgraveGOW" else None,
            "encoding": (
                "15-bit little-endian records packed into the alphabet "
                "0-9A-Za-z-_ ; code = representative + 6 * itertools-permutation-rank"
            ),
            "entries": len(ordered_witnesses),
            "characters": len(payload),
            "sha256": payload_sha256,
            "sections": {
                "root_free_k7": {
                    "entry_offset": 0,
                    "entries": count_table["root_free_k7"],
                },
                "root_containing_k6": {
                    "entry_offset": count_table["root_free_k7"],
                    "entries": count_table["root_containing_k6"],
                    "canonical_lift_order": "minimum (fixed, ones)",
                    "lift_multiplicity_counts": {
                        str(key): value for key, value in sorted(lift_multiplicities.items())
                    },
                },
            },
            "representative_counts": {
                str(index): witness_stats[index]
                for index in range(len(source.CUBE_REPRESENTATIVES))
            },
            "permutation_rank_span": (
                [min(permutation_ranks), max(permutation_ranks)]
                if permutation_ranks
                else []
            ),
            "distinct_witnesses": len(set(ordered_witnesses)),
            "round_trip_exact": True,
        },
        "lean_consumer_contract": {
            "raw_payload_is_ascii_include_str_compatible": True,
            "logical_chunk_size": WITNESS_CHUNK_SIZE,
            "logical_chunks": len(payload_chunks(payload)),
            "rendered_pure_data_module_sha256": sha256_bytes(lean_table),
            "core_index_reference": core_index_reference,
            "witness_table_reference": witness_reference,
        },
        "scope": (
            "Exact selected-core taxonomy, branchSource clause reconstruction, and "
            "orbit/full-lift witness generation only. No solver or S: access; no LRAT "
            "checking; no S7 catalogue composition, cover6-d7 theorem, global gluing, "
            "Ramsey-number bound, or discovery claim."
        ),
    }
    return SemanticBundle(payload, manifest, tuple(semantic_rows))


def manifest_bytes(manifest: dict[str, object]) -> bytes:
    return (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_new(path: Path, payload: bytes) -> None:
    if not path.parent.is_dir():
        raise D7CoreSemanticPayloadError(
            f"output parent directory does not exist: {path.parent}"
        )
    try:
        with path.open("xb") as stream:
            stream.write(payload)
    except FileExistsError:
        raise FileExistsError(f"refusing to overwrite generated artifact: {path}")


def emit(
    bundle: SemanticBundle,
    payload_path: Path = PAYLOAD_PATH,
    manifest_path: Path = MANIFEST_PATH,
    lean_table_path: Path | None = None,
) -> dict[str, object]:
    outputs = [(payload_path, bundle.payload), (manifest_path, manifest_bytes(bundle.manifest))]
    if lean_table_path is not None:
        spec = select_leaf(str(bundle.manifest["selection"]["slug"]))
        counts = bundle.manifest["taxonomy"]["family_counts"]
        outputs.append((lean_table_path, lean_table_source(bundle.payload, spec, counts)))
    existing = [path for path, _payload in outputs if path.exists()]
    if existing:
        raise FileExistsError(
            "refusing to overwrite generated artifacts: " + ", ".join(map(str, existing))
        )
    written: list[Path] = []
    try:
        for path, payload in outputs:
            write_new(path, payload)
            written.append(path)
    except BaseException:
        for path in reversed(written):
            path.unlink()
        raise
    return {
        "status": "EMITTED_NEW_D7_R34_CORE_SEMANTIC_ARTIFACTS",
        "artifacts": [file_metadata(path, lines=path.suffix != ".bin") for path in written],
    }


def verify_artifacts(
    bundle: SemanticBundle,
    payload_path: Path = PAYLOAD_PATH,
    manifest_path: Path = MANIFEST_PATH,
    lean_table_path: Path | None = None,
) -> dict[str, object]:
    expected = [(payload_path, bundle.payload), (manifest_path, manifest_bytes(bundle.manifest))]
    if lean_table_path is not None:
        spec = select_leaf(str(bundle.manifest["selection"]["slug"]))
        counts = bundle.manifest["taxonomy"]["family_counts"]
        expected.append((lean_table_path, lean_table_source(bundle.payload, spec, counts)))
    for path, payload in expected:
        if path.read_bytes() != payload:
            raise D7CoreSemanticPayloadError(
                f"generated artifact differs from deterministic rebuild: {path}"
            )
    return {
        "status": "PASS_TRACKED_D7_R34_CORE_SEMANTIC_ARTIFACTS_EXACT",
        "artifacts": [file_metadata(path, lines=path.suffix != ".bin") for path, _ in expected],
    }


def parse_cli(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", default="audit", choices=("audit", "emit", "verify"))
    parser.add_argument("--leaf", default="FgraveGOW")
    parser.add_argument("--core-directory", type=Path)
    parser.add_argument("--payload", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--lean-table", type=Path)
    parser.add_argument("--without-lean-references", action="store_true")
    args = parser.parse_args(argv)

    if args.leaf == "FgraveGOW":
        args.core_directory = args.core_directory or FGRAVEGOW_CORE_DIRECTORY
        args.payload = args.payload or PAYLOAD_PATH
        args.manifest = args.manifest or MANIFEST_PATH
    else:
        missing = [
            flag
            for flag, value in (
                ("--core-directory", args.core_directory),
                ("--payload", args.payload),
                ("--manifest", args.manifest),
            )
            if value is None
        ]
        if missing:
            parser.error(
                "non-FgraveGOW leaves require explicit " + ", ".join(missing)
            )
        if not args.without_lean_references:
            parser.error(
                "non-FgraveGOW leaves require --without-lean-references until their "
                "instantiated Lean index/witness modules exist"
            )
    return args


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_cli(argv)

    reference_core = None if args.without_lean_references else FGRAVEGOW_CORE_MODULE
    reference_indices = (
        None if args.without_lean_references else FGRAVEGOW_CORE_INDICES_DEFINITION
    )
    reference_semantics = (
        None if args.without_lean_references else FGRAVEGOW_SEMANTICS_MODULE
    )
    reference_witness = (
        None if args.without_lean_references else FGRAVEGOW_WITNESS_CHUNKS_DEFINITION
    )
    bundle = build_bundle(
        args.core_directory,
        args.leaf,
        reference_core_module=reference_core,
        reference_core_indices_definition=reference_indices,
        reference_semantics_module=reference_semantics,
        reference_witness_definition=reference_witness,
    )
    if args.command == "audit":
        result = bundle.manifest
    elif args.command == "emit":
        result = emit(bundle, args.payload, args.manifest, args.lean_table)
    else:
        result = verify_artifacts(bundle, args.payload, args.manifest, args.lean_table)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
