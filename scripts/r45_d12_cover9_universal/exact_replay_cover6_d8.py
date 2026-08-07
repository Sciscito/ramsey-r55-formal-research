#!/usr/bin/env python3
"""Standalone exact replay of the frozen cover6 degree-eight CNFs.

The program imports no project generator.  From the six graph6 records and
six partial-cube representatives it separately reconstructs the ordered
3,367,437-clause degree-eight DIMACS stream.  It can then simplify the frozen
source under each second-centre assignment, deduplicate the residual clauses,
add the 21 explicit units, and compare the sorted result line by line with the
13 frozen residuals.

No SAT solver or proof checker is invoked and no large file is written.  The
full replay reads artifacts only from an absolute S: directory and processes
one residual at a time.
"""

from __future__ import annotations

import argparse
import functools
import gc
import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path, PureWindowsPath
from typing import Iterable, Iterator, Sequence


LOCAL_ORDER = 7
LOCAL_EDGES = 21
LOCAL_FULL = (1 << LOCAL_EDGES) - 1
GLOBAL_ORDER = 12
GLOBAL_VARIABLES = 66
DEGREE = 8

HERE = Path(__file__).resolve().parent
COVER_TSV = HERE.parent / "r45_d12_complement_closed_minimum" / "cover6_complement_closed.tsv"
DEFAULT_ARTIFACT_ROOT = Path(
    r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover5-closed-universal"
)
SOURCE_NAME = "cover6_closed_block_degree_d8.cnf"
RESIDUAL_DIRECTORY = "cover6_closed_two_center_d8"

COVER_TSV_SHA256 = "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
COVER_RECORDS = ("F@h^g", "FKDhw", "FG`Xo", "FdW}w", "FHFLw", "FIIXw")
COVER_ORBIT_SIZES = (5_040, 5_040, 2_520, 2_520, 5_040, 5_040)
LABELLED_MASK_COUNT = 25_200
LABELLED_MASK_SHA256 = "04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7"

CUBE_REPRESENTATIVES = (
    (0x3, 0xDF677),
    (0x3E6BE, 0x1BE6BE),
    (0x84AE, 0x18FDFE),
    (0x8CF5, 0x1B8FFD),
    (0x897E, 0x15FDFE),
    (0x84ED, 0x1DF5EF),
)
CUBE_ORBIT_SIZES = (2_520, 2_520, 5_040, 5_040, 5_040, 5_040)
CUBE_COUNT = 25_200
CUBE_WIDTHS = {15: 5_040, 16: 10_080, 17: 10_080}
CUBE_SHA256 = "0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D"
R44_ASSIGNMENT_COUNT = 923_012

BLOCK_COUNTS = (2_520, 4_680, 10_200, 15_480, 15_480, 10_200, 4_680, 2_520)
LOCAL_COUNTS = (0, 300, 360, 540, 360, 300, 0)
SOURCE_CLAUSES = 3_367_437
SOURCE_BYTES = 189_298_232
SOURCE_SHA256 = "64E411A23778972A85DE7C8613A1977F98115E2EC3C9B1711D129932A4ECBB5A"

CASES = (
    (0, 2), (0, 3),
    (1, 1), (1, 2), (1, 3),
    (2, 0), (2, 1), (2, 2), (2, 3),
    (3, 0), (3, 1), (3, 2), (3, 3),
)

# Clauses, bytes, SHA-256: explicit expectations copied from the frozen
# checkpoint.  Code separation reduces accidental coupling, but these shared
# constants do not constitute a low-common-mode independent derivation.
RESIDUALS: dict[tuple[int, int], tuple[int, int, str]] = {
    (0, 2): (1_583_681, 85_636_007, "3FB10F899BE8887090DF7C9A440F04765AAC8FF05E803AFA1265C626AC0EC423"),
    (0, 3): (1_553_085, 84_743_919, "2D03534CE14E55C20C96AEB2015D05BA83BA8FAAB1022B101BAC1A4EE0E68AE8"),
    (1, 1): (1_558_127, 84_437_459, "2A18FFC8600C7E955A4ACC85EF1A15EEBA1181B97D9F0950093E4422C7C588D4"),
    (1, 2): (1_531_509, 83_727_795, "FF45ADE6E6B0C1D82ABA5FA79E759CD9BE509836842D6BC70BAA111CC97DF1D4"),
    (1, 3): (1_518_153, 83_431_811, "2337D8B2AAEFF130E4B838D602973DB63AB5EBA918FA684FD4B65D1FF25722D2"),
    (2, 0): (1_527_527, 83_021_526, "59FE553DBB88E433F8B853B2CEBFF6AECFA2748CEAD9C5B76DA1963C800EC905"),
    (2, 1): (1_506_520, 82_549_815, "2BD3AEE53473C6EAC92F9A1AC67D9996A934C8269904BCA1044F0AD878A58F17"),
    (2, 2): (1_494_714, 82_333_115, "75ACAFD7F236EC1DDA666772B7E807D816AEC0B2A699C32B6E7EC2C724D90006"),
    (2, 3): (1_494_540, 82_494_602, "EF30A1487D03AD23580BAE0A66666AE5D67D0F02597749FCAF30DA1F7CA8640D"),
    (3, 0): (1_476_640, 81_164_828, "49BEF032975CDAB73B6B63EDA21C387839B07389E5FCC5F8338C1EC8C4A8132E"),
    (3, 1): (1_467_869, 81_082_995, "3D577F1F24C05115221601D21CB03D1FA5CFF25E15F00B751E47FA3B0BA45940"),
    (3, 2): (1_467_823, 81_265_278, "B8940A85F2881BA8EFE3783C5948D124C5BC0BFC30F31595C1DF133DE50F44C1"),
    (3, 3): (1_477_475, 81_762_901, "DDBE87B5B39D03BB9ACE059FC996D5B4437D8CEA65994FBAFCCF3BE4877D0719"),
}

Cube = tuple[int, int]
Clause = tuple[int, ...]


class ExactReplayError(ValueError):
    """Raised at the first semantic or byte-level mismatch."""


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def require_ssd(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise ExactReplayError(f"artifact root must be absolute on S:, got {path}")
    return path


def local_edge(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < LOCAL_ORDER:
        raise ValueError("not an edge of the local K7")
    return right * (right - 1) // 2 + left


def global_edge(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < GLOBAL_ORDER:
        raise ValueError("not an edge of K12")
    return left * (2 * GLOBAL_ORDER - left - 1) // 2 + right - left


def decode_graph6(record: str) -> int:
    if len(record) != 5 or ord(record[0]) != LOCAL_ORDER + 63:
        raise ExactReplayError(f"invalid order-seven graph6 record: {record!r}")
    bits: list[int] = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ExactReplayError(f"invalid graph6 payload: {record!r}")
        bits.extend((value >> shift) & 1 for shift in range(5, -1, -1))
    if any(bits[LOCAL_EDGES:]):
        raise ExactReplayError(f"nonzero graph6 padding: {record!r}")
    return sum(bit << position for position, bit in enumerate(bits[:LOCAL_EDGES]))


def read_cover_records() -> tuple[str, ...]:
    digest = file_sha256(COVER_TSV)
    if digest != COVER_TSV_SHA256:
        raise ExactReplayError(f"cover TSV SHA-256 mismatch: {digest}")
    records = []
    for line_number, raw in enumerate(COVER_TSV.read_text(encoding="ascii").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise ExactReplayError(f"malformed cover TSV row {line_number}")
        records.append(fields[1])
    result = tuple(records)
    if result != COVER_RECORDS:
        raise ExactReplayError(f"cover records changed: {result}")
    return result


@functools.cache
def permutation_maps() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            local_edge(permutation[left], permutation[right])
            for right in range(1, LOCAL_ORDER)
            for left in range(right)
        )
        for permutation in itertools.permutations(range(LOCAL_ORDER))
    )


def transform(mask: int, mapping: Sequence[int]) -> int:
    result = 0
    for target, source in enumerate(mapping):
        result |= ((mask >> source) & 1) << target
    return result


def graph_orbit(mask: int) -> frozenset[int]:
    return frozenset(transform(mask, mapping) for mapping in permutation_maps())


def cube_orbit(cube: Cube) -> frozenset[Cube]:
    ones, fixed = cube
    return frozenset(
        (transform(ones, mapping), transform(fixed, mapping))
        for mapping in permutation_maps()
    )


def masks_digest(masks: Iterable[int]) -> str:
    payload = "".join(f"{mask:06X}\n" for mask in sorted(masks)).encode("ascii")
    return hashlib.sha256(payload).hexdigest().upper()


def cubes_digest(cubes: Iterable[Cube]) -> str:
    payload = "".join(
        f"{ones:06X}\t{fixed:06X}\n"
        for ones, fixed in sorted(cubes, key=lambda cube: (cube[1], cube[0]))
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest().upper()


@functools.cache
def forbidden_masks() -> frozenset[int]:
    pieces = tuple(graph_orbit(decode_graph6(record)) for record in read_cover_records())
    sizes = tuple(map(len, pieces))
    if sizes != COVER_ORBIT_SIZES:
        raise ExactReplayError(f"cover orbit sizes changed: {sizes}")
    if any(pieces[left] & pieces[right] for left in range(6) for right in range(left)):
        raise ExactReplayError("cover motif orbits overlap")
    result = frozenset().union(*pieces)
    if len(result) != LABELLED_MASK_COUNT or masks_digest(result) != LABELLED_MASK_SHA256:
        raise ExactReplayError("labelled cover closure changed")
    if {LOCAL_FULL ^ mask for mask in result} != result:
        raise ExactReplayError("labelled cover is not complement-closed")
    return result


@functools.cache
def reduced_cubes() -> tuple[Cube, ...]:
    pieces = tuple(cube_orbit(cube) for cube in CUBE_REPRESENTATIVES)
    sizes = tuple(map(len, pieces))
    if sizes != CUBE_ORBIT_SIZES:
        raise ExactReplayError(f"cube orbit sizes changed: {sizes}")
    result = frozenset().union(*pieces)
    if len(result) != CUBE_COUNT:
        raise ExactReplayError(f"cube count changed: {len(result)}")
    if any(ones & ~fixed or fixed & ~LOCAL_FULL for ones, fixed in result):
        raise ExactReplayError("malformed cube")
    if {(fixed ^ ones, fixed) for ones, fixed in result} != result:
        raise ExactReplayError("cube family is not complement-closed")
    widths = Counter(fixed.bit_count() for _ones, fixed in result)
    if dict(sorted(widths.items())) != CUBE_WIDTHS or cubes_digest(result) != CUBE_SHA256:
        raise ExactReplayError("cube closure changed")
    return tuple(sorted(result, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))


def completions(cube: Cube) -> Iterator[int]:
    ones, fixed = cube
    remaining = LOCAL_FULL ^ fixed
    while True:
        yield ones | remaining
        if remaining == 0:
            break
        remaining = (remaining - 1) & (LOCAL_FULL ^ fixed)


@functools.cache
def local_four_cliques() -> tuple[int, ...]:
    return tuple(
        sum(
            1 << local_edge(left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(LOCAL_ORDER), 4)
    )


@functools.cache
def r44_flags() -> bytearray:
    flags = bytearray(1 << LOCAL_EDGES)
    cliques = local_four_cliques()
    count = 0
    for mask in range(1 << LOCAL_EDGES):
        if all((mask & clique) not in (0, clique) for clique in cliques):
            flags[mask] = 1
            count += 1
    if count != R44_ASSIGNMENT_COUNT:
        raise ExactReplayError(f"local R(4,4) assignment count changed: {count}")
    return flags


@functools.cache
def validate_local_exactness() -> dict[str, int | bool]:
    valid = r44_flags()
    target = forbidden_masks()
    covered: set[int] = set()
    for cube in reduced_cubes():
        for mask in completions(cube):
            if not valid[mask]:
                continue
            if mask not in target:
                raise ExactReplayError(f"cube rejects a non-motif R(4,4) mask: {mask:#x}")
            covered.add(mask)
    if covered != target:
        raise ExactReplayError(f"cubes miss {len(target - covered)} motif masks")
    return {
        "checked_assignments": 1 << LOCAL_EDGES,
        "r44_assignments": sum(valid),
        "motif_assignments": len(target),
        "cube_rejected_r44_assignments": len(covered),
        "exact": True,
    }


def triangle_masks(vertices: range) -> tuple[int, ...]:
    return tuple(
        sum(1 << local_edge(left, right) for left, right in itertools.combinations(triple, 2))
        for triple in itertools.combinations(vertices, 3)
    )


@functools.cache
def block_conditioned_cubes() -> tuple[tuple[Cube, ...], ...]:
    result = []
    forbidden = forbidden_masks()
    for neighbour_count in range(8):
        positive = triangle_masks(range(neighbour_count))
        negative = triangle_masks(range(neighbour_count, 7))
        target = tuple(sorted(
            mask for mask in forbidden
            if all((mask & triangle) != triangle for triangle in positive)
            and all((mask & triangle) != 0 for triangle in negative)
        ))
        index = {mask: item for item, mask in enumerate(target)}
        by_coverage: dict[frozenset[int], Cube] = {}
        for cube in reduced_cubes():
            covered = frozenset(
                item for mask in completions(cube)
                if (item := index.get(mask)) is not None
            )
            if not covered:
                continue
            previous = by_coverage.get(covered)
            if previous is None or (cube[1].bit_count(), cube[1], cube[0]) < (
                previous[1].bit_count(), previous[1], previous[0]
            ):
                by_coverage[covered] = cube
        selected = tuple(sorted(
            by_coverage.values(), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])
        ))
        if len(selected) != BLOCK_COUNTS[neighbour_count]:
            raise ExactReplayError(
                f"block-conditioned count a={neighbour_count} changed: {len(selected)}"
            )
        if {mask for mask in target if any((mask & fixed) == ones for ones, fixed in selected)} != set(target):
            raise ExactReplayError(f"block-conditioned cover misses a={neighbour_count}")
        result.append(selected)
    return tuple(result)


def project_nonroot(mask: int) -> int:
    result = 0
    for right in range(2, 7):
        for left in range(1, right):
            if (mask >> local_edge(left, right)) & 1:
                result |= 1 << local_edge(left - 1, right - 1)
    return result


@functools.cache
def local_conditioned_cubes() -> tuple[tuple[Cube, ...], ...]:
    root_edges = tuple(local_edge(0, vertex) for vertex in range(1, 7))
    result = []
    for neighbour_count in range(7):
        target = tuple(sorted({
            project_nonroot(mask)
            for mask in forbidden_masks()
            if all(
                bool((mask >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_edges, 1)
            )
        }))
        index = {mask: item for item, mask in enumerate(target)}
        restricted: set[Cube] = set()
        for ones, fixed in reduced_cubes():
            if all(
                not ((fixed >> position) & 1)
                or bool((ones >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_edges, 1)
            ):
                restricted.add((project_nonroot(ones), project_nonroot(fixed)))
        candidates = []
        for ones, fixed in restricted:
            coverage = frozenset(index[mask] for mask in target if (mask & fixed) == ones)
            if coverage:
                candidates.append((coverage, ones, fixed))
        active = set(range(len(target)))
        selected: list[Cube] = []
        while active:
            coverage, ones, fixed = max(
                candidates,
                key=lambda item: (
                    len(active & item[0]), -item[2].bit_count(), -item[2], -item[1]
                ),
            )
            newly = active & coverage
            if not newly:
                raise ExactReplayError(f"local greedy cover stuck at a={neighbour_count}")
            selected.append((ones, fixed))
            active -= newly
        ordered = tuple(sorted(
            set(selected), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])
        ))
        if len(ordered) != LOCAL_COUNTS[neighbour_count]:
            raise ExactReplayError(
                f"local-conditioned count a={neighbour_count} changed: {len(ordered)}"
            )
        result.append(ordered)
    return tuple(result)


def base_clauses() -> tuple[Clause, ...]:
    clauses: list[Clause] = []
    for vertices in itertools.combinations(range(1, 12), 4):
        edges = tuple(global_edge(left, right) for left, right in itertools.combinations(vertices, 2))
        clauses.append(tuple(-edge for edge in edges))
        clauses.append(edges)
    for vertices in itertools.combinations(range(1, DEGREE + 1), 3):
        clauses.append(tuple(
            -global_edge(left, right) for left, right in itertools.combinations(vertices, 2)
        ))
    for vertices in itertools.combinations(range(DEGREE + 1, 12), 3):
        clauses.append(tuple(
            global_edge(left, right) for left, right in itertools.combinations(vertices, 2)
        ))
    if len(clauses) != 717 or any(abs(literal) <= 11 for clause in clauses for literal in clause):
        raise ExactReplayError("degree-eight base clauses changed")
    return tuple(clauses)


def subset_variables(vertices: Sequence[int]) -> tuple[int, ...]:
    return tuple(
        global_edge(vertices[left], vertices[right])
        for right in range(1, len(vertices))
        for left in range(right)
    )


def instantiate(cube: Cube, variables: Sequence[int]) -> Clause:
    ones, fixed = cube
    return tuple(
        -variables[position] if (ones >> position) & 1 else variables[position]
        for position in range(len(variables))
        if (fixed >> position) & 1
    )


def expected_source_clauses() -> Iterator[Clause]:
    yield from base_clauses()
    blocks = block_conditioned_cubes()
    for vertices in itertools.combinations(range(1, 12), 7):
        neighbours = sum(vertex <= DEGREE for vertex in vertices)
        variables = subset_variables(vertices)
        for cube in blocks[neighbours]:
            yield instantiate(cube, variables)
    locals_ = local_conditioned_cubes()
    for vertices in itertools.combinations(range(1, 12), 6):
        neighbours = sum(vertex <= DEGREE for vertex in vertices)
        variables = subset_variables(vertices)
        for cube in locals_[neighbours]:
            yield instantiate(cube, variables)


def clause_line(clause: Sequence[int]) -> bytes:
    return (" ".join(map(str, clause)) + (" " if clause else "") + "0\n").encode("ascii")


def compare_formula(
    path: Path,
    clauses: Iterable[Clause],
    expected_count: int,
    *,
    expected_bytes: int | None = None,
    expected_sha256: str | None = None,
) -> dict[str, int | str]:
    """Strictly compare a DIMACS file to a separately produced sequence."""
    digest = hashlib.sha256()
    size = 0
    lines = 0
    header = f"p cnf {GLOBAL_VARIABLES} {expected_count}\n".encode("ascii")
    with path.open("rb") as stream:
        observed = stream.readline()
        digest.update(observed)
        size += len(observed)
        lines += 1
        if observed != header:
            raise ExactReplayError(f"DIMACS header mismatch in {path.name}")
        count = 0
        for count, clause in enumerate(clauses, 1):
            expected = clause_line(clause)
            observed = stream.readline()
            digest.update(observed)
            size += len(observed)
            lines += 1
            if observed != expected:
                raise ExactReplayError(
                    f"clause mismatch in {path.name} at DIMACS line {lines}: "
                    f"expected {expected[:160]!r}, observed {observed[:160]!r}"
                )
        if count != expected_count:
            raise ExactReplayError(f"expected-clause count mismatch: {count} != {expected_count}")
        extra = stream.readline()
        if extra:
            raise ExactReplayError(f"unexpected extra clause in {path.name} at line {lines + 1}")
    observed_sha = digest.hexdigest().upper()
    if expected_bytes is not None and size != expected_bytes:
        raise ExactReplayError(f"byte count mismatch in {path.name}: {size} != {expected_bytes}")
    if expected_sha256 is not None and observed_sha != expected_sha256:
        raise ExactReplayError(f"SHA-256 mismatch in {path.name}: {observed_sha}")
    return {"clauses": expected_count, "bytes": size, "sha256": observed_sha, "lines": lines}


def verify_source(artifact_root: Path) -> dict[str, object]:
    artifact_root = require_ssd(artifact_root)
    result = compare_formula(
        artifact_root / SOURCE_NAME,
        expected_source_clauses(),
        SOURCE_CLAUSES,
        expected_bytes=SOURCE_BYTES,
        expected_sha256=SOURCE_SHA256,
    )
    return {
        "status": "PASS",
        "scope": "standalone ordered reconstruction and byte-for-byte comparison",
        "formula": result,
        "local_inputs": {
            "cover_tsv_sha256": file_sha256(COVER_TSV),
            "labelled_masks": len(forbidden_masks()),
            "labelled_mask_sha256": masks_digest(forbidden_masks()),
            "cubes": len(reduced_cubes()),
            "cube_sha256": cubes_digest(reduced_cubes()),
            "local_exactness": validate_local_exactness(),
            "block_conditioned_counts": [len(items) for items in block_conditioned_cubes()],
            "local_conditioned_counts": [len(items) for items in local_conditioned_cubes()],
        },
    }


def parse_source(path: Path) -> Iterator[Clause]:
    digest = hashlib.sha256()
    with path.open("rb", buffering=8 * 1024 * 1024) as stream:
        header = stream.readline()
        digest.update(header)
        if header != f"p cnf {GLOBAL_VARIABLES} {SOURCE_CLAUSES}\n".encode("ascii"):
            raise ExactReplayError("frozen source header mismatch during reduction")
        count = 0
        for line_number, raw in enumerate(stream, 2):
            digest.update(raw)
            values = tuple(map(int, raw.split()))
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ExactReplayError(f"malformed source clause at line {line_number}")
            clause = values[:-1]
            if any(not 1 <= abs(literal) <= GLOBAL_VARIABLES for literal in clause):
                raise ExactReplayError(f"source literal out of range at line {line_number}")
            if any(abs(literal) <= 11 for literal in clause):
                raise ExactReplayError(f"root variable survives source conditioning at line {line_number}")
            count += 1
            yield clause
        if count != SOURCE_CLAUSES:
            raise ExactReplayError(f"source clause count changed: {count}")
    observed_sha = digest.hexdigest().upper()
    if observed_sha != SOURCE_SHA256:
        raise ExactReplayError(f"source SHA-256 changed during reduction: {observed_sha}")


def second_assignment(p: int, q: int) -> dict[int, bool]:
    if (p, q) not in CASES:
        raise ValueError(f"unsupported degree-eight case: {(p, q)}")
    result = {
        global_edge(1, vertex): vertex <= p + 1
        for vertex in range(2, DEGREE + 1)
    }
    result.update({
        global_edge(1, vertex): vertex <= DEGREE + q
        for vertex in range(DEGREE + 1, 12)
    })
    if set(result) != set(range(12, 22)):
        raise ExactReplayError("second-centre variables are not exactly 12..21")
    return result


def exact_units(p: int, q: int) -> tuple[int, ...]:
    assignment = {variable: variable <= DEGREE for variable in range(1, 12)}
    assignment.update(second_assignment(p, q))
    if set(assignment) != set(range(1, 22)):
        raise ExactReplayError("branch units are not exactly variables 1..21")
    return tuple(variable if assignment[variable] else -variable for variable in range(1, 22))


def encode_clause(clause: Sequence[int]) -> int:
    positive = 0
    negative = 0
    for literal in clause:
        variable = abs(literal)
        if not 1 <= variable <= GLOBAL_VARIABLES:
            raise ExactReplayError(f"literal out of range: {literal}")
        bit = 1 << (variable - 1)
        if literal > 0:
            if positive & bit or negative & bit:
                raise ExactReplayError(f"duplicate or tautological literal: {literal}")
            positive |= bit
        else:
            if negative & bit or positive & bit:
                raise ExactReplayError(f"duplicate or tautological literal: {literal}")
            negative |= bit
    return positive | (negative << GLOBAL_VARIABLES)


def decode_clause(key: int) -> Clause:
    positive = key & ((1 << GLOBAL_VARIABLES) - 1)
    negative = key >> GLOBAL_VARIABLES
    if positive & negative:
        raise ExactReplayError("encoded clause is tautological")
    return tuple(
        variable if positive & (1 << (variable - 1)) else -variable
        for variable in range(1, GLOBAL_VARIABLES + 1)
        if (positive | negative) & (1 << (variable - 1))
    )


def simplify_clause(clause: Sequence[int], assignment: dict[int, bool]) -> Clause | None:
    remaining = []
    for literal in clause:
        value = assignment.get(abs(literal))
        if value is None:
            remaining.append(literal)
        elif value == (literal > 0):
            return None
    return tuple(remaining)


def reduce_clauses(
    clauses: Iterable[Clause], p: int, q: int
) -> tuple[set[int], dict[str, int]]:
    assignment = second_assignment(p, q)
    keys: set[int] = set()
    parsed = 0
    satisfied = 0
    surviving = 0
    false_literals_removed = 0
    for clause in clauses:
        parsed += 1
        reduced = simplify_clause(clause, assignment)
        if reduced is None:
            satisfied += 1
            continue
        surviving += 1
        false_literals_removed += sum(abs(literal) in assignment for literal in clause)
        keys.add(encode_clause(reduced))
    unique = len(keys)
    unit_keys = {encode_clause((literal,)) for literal in exact_units(p, q)}
    if keys & unit_keys:
        raise ExactReplayError(f"residual p={p},q={q} already contains an exact branch unit")
    keys.update(unit_keys)
    return keys, {
        "source_clauses": parsed,
        "satisfied_clauses_removed": satisfied,
        "surviving_before_deduplication": surviving,
        "exact_duplicates_removed": surviving - unique,
        "false_second_center_literals_removed": false_literals_removed,
        "unique_residual_clauses": unique,
        "exact_unit_clauses_added": len(unit_keys),
        "output_clauses": len(keys),
    }


def build_residual_keys(source: Path, p: int, q: int) -> tuple[set[int], dict[str, int]]:
    keys, metrics = reduce_clauses(parse_source(source), p, q)
    if metrics["source_clauses"] != SOURCE_CLAUSES:
        raise ExactReplayError("source clause count changed during residual construction")
    return keys, metrics


def reduction_metrics_all(source: Path) -> list[dict[str, int]]:
    """Recompute all non-set reduction counters in one source pass.

    Exact unique counts come from the already byte-compared residual sizes:
    every residual contains exactly 21 new unit clauses and the full replay
    checks that none duplicates a reduced source clause.
    """
    assignments = tuple(second_assignment(p, q) for p, q in CASES)
    satisfied = [0] * len(CASES)
    surviving = [0] * len(CASES)
    false_removed = [0] * len(CASES)
    parsed = 0
    for clause in parse_source(source):
        parsed += 1
        assigned_literals = tuple(
            literal for literal in clause if 12 <= abs(literal) <= 21
        )
        for index, assignment in enumerate(assignments):
            if any(
                assignment[abs(literal)] == (literal > 0)
                for literal in assigned_literals
            ):
                satisfied[index] += 1
            else:
                surviving[index] += 1
                false_removed[index] += len(assigned_literals)
    rows = []
    for index, (p, q) in enumerate(CASES):
        output = RESIDUALS[(p, q)][0]
        unique = output - 21
        rows.append({
            "p": p,
            "q": q,
            "source_clauses": parsed,
            "satisfied_clauses_removed": satisfied[index],
            "surviving_before_deduplication": surviving[index],
            "exact_duplicates_removed": surviving[index] - unique,
            "false_second_center_literals_removed": false_removed[index],
            "unique_residual_clauses": unique,
            "exact_unit_clauses_added": 21,
            "output_clauses": output,
        })
    return rows


def residual_name(p: int, q: int) -> str:
    return f"cover6_closed_d8_two_center_p{p}_q{q}.cnf"


def verify_residual(artifact_root: Path, p: int, q: int) -> dict[str, object]:
    artifact_root = require_ssd(artifact_root)
    source = artifact_root / SOURCE_NAME
    keys, metrics = build_residual_keys(source, p, q)
    expected_count, expected_bytes, expected_sha = RESIDUALS[(p, q)]
    if len(keys) != expected_count:
        raise ExactReplayError(
            f"standalone residual count p={p},q={q}: {len(keys)} != {expected_count}"
        )
    path = artifact_root / RESIDUAL_DIRECTORY / residual_name(p, q)
    formula = compare_formula(
        path,
        (decode_clause(key) for key in sorted(keys)),
        expected_count,
        expected_bytes=expected_bytes,
        expected_sha256=expected_sha,
    )
    return {
        "status": "PASS",
        "p": p,
        "q": q,
        "exact_unit_literals": list(exact_units(p, q)),
        "reduction": metrics,
        "formula": formula,
        "scope": "standalone simplify/deduplicate/unit reconstruction and byte-for-byte comparison",
    }


def preflight() -> dict[str, object]:
    exactness = validate_local_exactness()
    blocks = block_conditioned_cubes()
    locals_ = local_conditioned_cubes()
    total = len(base_clauses())
    total += sum(
        math.comb(DEGREE, neighbours)
        * math.comb(11 - DEGREE, 7 - neighbours)
        * len(blocks[neighbours])
        for neighbours in range(8)
        if neighbours <= DEGREE and 7 - neighbours <= 11 - DEGREE
    )
    total += sum(
        math.comb(DEGREE, neighbours)
        * math.comb(11 - DEGREE, 6 - neighbours)
        * len(locals_[neighbours])
        for neighbours in range(7)
        if neighbours <= DEGREE and 6 - neighbours <= 11 - DEGREE
    )
    if total != SOURCE_CLAUSES:
        raise ExactReplayError(f"standalone source clause arithmetic changed: {total}")
    return {
        "status": "PASS",
        "implementation": (
            "standalone stdlib reimplementation; imports no project generator; "
            "shares frozen primitive constants with the production checkpoint"
        ),
        "cover_tsv_sha256": file_sha256(COVER_TSV),
        "records": list(read_cover_records()),
        "labelled_masks": len(forbidden_masks()),
        "mask_sha256": masks_digest(forbidden_masks()),
        "cubes": len(reduced_cubes()),
        "cube_sha256": cubes_digest(reduced_cubes()),
        "local_exactness": exactness,
        "block_conditioned_counts": [len(items) for items in blocks],
        "local_conditioned_counts": [len(items) for items in locals_],
        "source_clauses": total,
        "cases": [list(case) for case in CASES],
        "scope": "deterministic reconstruction preflight; no artifact read, SAT, LRAT, or Lean claim",
    }


def parse_case(value: str) -> tuple[int, int]:
    try:
        left, right = value.split(",")
        case = int(left), int(right)
    except (TypeError, ValueError) as error:
        raise argparse.ArgumentTypeError("case must have spelling p,q") from error
    if case not in CASES:
        raise argparse.ArgumentTypeError(f"unsupported degree-eight case: {case}")
    return case


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("preflight", "source", "metrics", "residual", "all")
    )
    parser.add_argument("--artifact-root", type=Path, default=DEFAULT_ARTIFACT_ROOT)
    parser.add_argument(
        "--case", dest="cases", action="append", type=parse_case,
        help="residual case p,q; repeat as needed (default: all 13)",
    )
    args = parser.parse_args()
    if args.command == "preflight":
        result: object = preflight()
    elif args.command == "source":
        result = verify_source(args.artifact_root)
    elif args.command == "metrics":
        source_path = require_ssd(args.artifact_root) / SOURCE_NAME
        result = {
            "status": "COUNTERS_RECOMPUTED_WITH_DERIVED_UNIQUE_COUNTS",
            "source_sha256": SOURCE_SHA256,
            "cases": reduction_metrics_all(source_path),
            "scope": (
                "satisfaction and literal-removal counters are recomputed; unique and duplicate "
                "counts are derived from frozen output sizes previously checked by full replay"
            ),
        }
    else:
        selected = tuple(args.cases or CASES)
        source_result = verify_source(args.artifact_root) if args.command == "all" else None
        rows = []
        for index, (p, q) in enumerate(selected, 1):
            print(f"exact replay residual {index}/{len(selected)}: p={p}, q={q}", flush=True)
            rows.append(verify_residual(args.artifact_root, p, q))
            gc.collect()
        result = {
            "status": "PASS",
            "source": source_result,
            "residuals": rows,
            "cases_checked": len(rows),
            "proof_scope": (
                "exact finite CNF reconstruction only; no SAT, LRAT, Lean bridge, "
                "or cover6-d8 theorem is claimed"
            ),
        }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
