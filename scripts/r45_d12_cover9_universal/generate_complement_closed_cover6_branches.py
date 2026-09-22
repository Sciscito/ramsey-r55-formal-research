#!/usr/bin/env python3
"""Generate universal degree branches for the complement-closed cover6.

The local target consists of three exact complement pairs of order-seven
R(4,4) motifs.  Six frozen S7 cube orbits are checked exhaustively against all
2^21 local assignments before any K12 formula is written.  Heavy artifacts
are accepted only below an absolute ``S:`` path.

Generation alone proves neither UNSAT nor the still-external catalogue cover.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
import os
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

from . import generate_degree_branch as degree_branch
from . import generate_universal as universal


HERE = Path(__file__).resolve().parent
COVER_PATH = HERE.parent / "r45_d12_complement_closed_minimum" / "cover6_complement_closed.tsv"

N = 7
EDGE_COUNT = 21
LIMIT = 1 << EDGE_COUNT
FULL = LIMIT - 1
DEGREES = (6, 7, 8)
Cube = tuple[int, int]
Clause = tuple[int, ...]

EXPECTED_COVER_SHA256 = "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
EXPECTED_RECORDS = ("F@h^g", "FKDhw", "FG`Xo", "FdW}w", "FHFLw", "FIIXw")
EXPECTED_ORBIT_SIZES = (5_040, 5_040, 2_520, 2_520, 5_040, 5_040)
EXPECTED_LABELLED_MASKS = 25_200
EXPECTED_MASK_SHA256 = "04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7"
EXPECTED_R44 = 923_012

# For each complement pair, take the greedy minimum cube from the first TSV
# record and the exact complement orbit.  This convention removes the only
# otherwise arbitrary orientation choice and makes the family syntactically
# complement-closed.
CUBE_REPRESENTATIVES = (
    (0x3, 0xDF677),
    (0x3E6BE, 0x1BE6BE),
    (0x84AE, 0x18FDFE),
    (0x8CF5, 0x1B8FFD),
    (0x897E, 0x15FDFE),
    (0x84ED, 0x1DF5EF),
)
EXPECTED_CUBE_ORBIT_SIZES = (2_520, 2_520, 5_040, 5_040, 5_040, 5_040)
EXPECTED_CUBES = 25_200
EXPECTED_CUBE_WIDTHS = {15: 5_040, 16: 10_080, 17: 10_080}
EXPECTED_CUBE_SHA256 = "0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D"

BLOCK_CONDITIONED_COUNTS = (2_520, 4_680, 10_200, 15_480, 15_480, 10_200, 4_680, 2_520)
LOCAL_CONDITIONED_COUNTS = (0, 300, 360, 540, 360, 300, 0)
EXPECTED_CLAUSE_COUNTS = {
    6: 4_858_890,
    7: 4_312_419,
    8: 3_367_437,
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def decode_graph6(record: str) -> int:
    if len(record) != 5 or ord(record[0]) - 63 != N:
        raise ValueError(f"invalid order-seven graph6 record: {record!r}")
    result = 0
    position = 0
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 payload: {record!r}")
        for shift in range(5, -1, -1):
            bit = value >> shift & 1
            if position < EDGE_COUNT:
                result |= bit << position
            elif bit:
                raise ValueError(f"nonzero graph6 padding: {record!r}")
            position += 1
    return result


def read_records() -> tuple[str, ...]:
    digest = sha256(COVER_PATH)
    if digest != EXPECTED_COVER_SHA256:
        raise ValueError(f"cover6 SHA-256 mismatch: {digest}")
    records = []
    for line_number, raw in enumerate(COVER_PATH.read_text(encoding="ascii").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise ValueError(f"invalid cover6 row {line_number}: {raw!r}")
        records.append(fields[1])
    result = tuple(records)
    if result != EXPECTED_RECORDS:
        raise ValueError(f"cover6 records changed: {result}")
    return result


@functools.cache
def edge_maps() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            universal.edge_position(permutation[left], permutation[right])
            for right in range(1, N)
            for left in range(right)
        )
        for permutation in itertools.permutations(range(N))
    )


def relabel(mask: int, edge_map: Sequence[int]) -> int:
    result = 0
    for target, source in enumerate(edge_map):
        result |= ((mask >> source) & 1) << target
    return result


def orbit(mask: int) -> frozenset[int]:
    return frozenset(relabel(mask, edge_map) for edge_map in edge_maps())


def cube_orbit(cube: Cube) -> frozenset[Cube]:
    ones, fixed = cube
    return frozenset((relabel(ones, edge_map), relabel(fixed, edge_map)) for edge_map in edge_maps())


def mask_payload(masks: Iterable[int]) -> bytes:
    return "".join(f"{mask:06X}\n" for mask in sorted(masks)).encode("ascii")


def cube_payload(cubes: Iterable[Cube]) -> bytes:
    return "".join(
        f"{ones:06X}\t{fixed:06X}\n"
        for ones, fixed in sorted(cubes, key=lambda cube: (cube[1], cube[0]))
    ).encode("ascii")


def digest_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


@functools.cache
def forbidden_masks() -> frozenset[int]:
    orbits = tuple(orbit(decode_graph6(record)) for record in read_records())
    sizes = tuple(map(len, orbits))
    if sizes != EXPECTED_ORBIT_SIZES:
        raise RuntimeError(f"cover6 orbit sizes changed: {sizes}")
    result = frozenset().union(*orbits)
    if len(result) != EXPECTED_LABELLED_MASKS:
        raise RuntimeError(f"cover6 labelled closure changed: {len(result)}")
    if {FULL ^ mask for mask in result} != result:
        raise RuntimeError("cover6 target is not complement-closed")
    digest = digest_bytes(mask_payload(result))
    if digest != EXPECTED_MASK_SHA256:
        raise RuntimeError(f"cover6 mask closure SHA-256 changed: {digest}")
    return result


@functools.cache
def reduced_cubes() -> tuple[Cube, ...]:
    orbits = tuple(cube_orbit(cube) for cube in CUBE_REPRESENTATIVES)
    sizes = tuple(map(len, orbits))
    if sizes != EXPECTED_CUBE_ORBIT_SIZES:
        raise RuntimeError(f"cover6 cube orbit sizes changed: {sizes}")
    cubes = frozenset().union(*orbits)
    if len(cubes) != EXPECTED_CUBES:
        raise RuntimeError(f"cover6 cube closure changed: {len(cubes)}")
    if any(ones & ~fixed or fixed & ~FULL for ones, fixed in cubes):
        raise RuntimeError("malformed cover6 cube")
    if {(fixed ^ ones, fixed) for ones, fixed in cubes} != cubes:
        raise RuntimeError("cover6 cubes are not complement-closed")
    widths = Counter(fixed.bit_count() for _ones, fixed in cubes)
    if dict(sorted(widths.items())) != EXPECTED_CUBE_WIDTHS:
        raise RuntimeError(f"cover6 cube widths changed: {dict(widths)}")
    digest = digest_bytes(cube_payload(cubes))
    if digest != EXPECTED_CUBE_SHA256:
        raise RuntimeError(f"cover6 cube SHA-256 changed: {digest}")
    return tuple(sorted(cubes, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))


@functools.cache
def clique_masks() -> tuple[int, ...]:
    return tuple(
        sum(1 << universal.edge_position(left, right) for left, right in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(N), 4)
    )


@functools.cache
def r44_flags() -> bytearray:
    valid = bytearray(b"\x01") * LIMIT
    for clique in clique_masks():
        free = FULL ^ clique
        completion = free
        while True:
            valid[completion] = 0
            valid[clique | completion] = 0
            if completion == 0:
                break
            completion = (completion - 1) & free
    if sum(valid) != EXPECTED_R44:
        raise RuntimeError(f"local R(4,4) count changed: {sum(valid)}")
    return valid


def matching_assignments(cube: Cube) -> Iterable[int]:
    ones, fixed = cube
    free = FULL ^ fixed
    completion = free
    while True:
        yield ones | completion
        if completion == 0:
            break
        completion = (completion - 1) & free


@functools.cache
def validate_local_reduction() -> dict[str, object]:
    valid = r44_flags()
    forbidden = forbidden_masks()
    covered: set[int] = set()
    for cube in reduced_cubes():
        for mask in matching_assignments(cube):
            if not valid[mask]:
                continue
            if mask not in forbidden:
                raise RuntimeError(f"unsafe cover6 cube at mask {mask:#x}")
            covered.add(mask)
    if covered != forbidden:
        raise RuntimeError(f"cover6 cubes miss {len(forbidden - covered)} masks")
    return {
        "status": "PASS",
        "checked_assignments": LIMIT,
        "r44_assignments": sum(valid),
        "forbidden_assignments": len(forbidden),
        "rejected_r44_assignments": len(covered),
        "exact_on_local_r44": True,
    }


def triangle_masks(vertices: range) -> tuple[int, ...]:
    return tuple(
        sum(1 << universal.edge_position(left, right) for left, right in itertools.combinations(triple, 2))
        for triple in itertools.combinations(vertices, 3)
    )


def block_forbidden_masks(neighbour_count: int) -> tuple[int, ...]:
    if not 0 <= neighbour_count <= 7:
        raise ValueError("local block size must lie in 0..7")
    positive = triangle_masks(range(neighbour_count))
    negative = triangle_masks(range(neighbour_count, 7))
    return tuple(sorted(
        mask for mask in forbidden_masks()
        if all((mask & triangle) != triangle for triangle in positive)
        and all((mask & triangle) != 0 for triangle in negative)
    ))


@functools.cache
def block_conditioned_cubes() -> tuple[tuple[Cube, ...], ...]:
    result = []
    for neighbour_count in range(8):
        target = block_forbidden_masks(neighbour_count)
        index = {mask: item for item, mask in enumerate(target)}
        by_coverage: dict[frozenset[int], Cube] = {}
        for ones, fixed in reduced_cubes():
            covered = frozenset(
                item for mask in matching_assignments((ones, fixed))
                if (item := index.get(mask)) is not None
            )
            if not covered:
                continue
            previous = by_coverage.get(covered)
            if previous is None or (fixed.bit_count(), fixed, ones) < (
                previous[1].bit_count(), previous[1], previous[0]
            ):
                by_coverage[covered] = (ones, fixed)
        selected = tuple(sorted(by_coverage.values(), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))
        if len(selected) != BLOCK_CONDITIONED_COUNTS[neighbour_count]:
            raise RuntimeError(f"block-conditioned count a={neighbour_count} changed: {len(selected)}")
        rejected = {mask for mask in target if any((mask & fixed) == ones for ones, fixed in selected)}
        if rejected != set(target):
            raise RuntimeError(f"block-conditioned cover misses a={neighbour_count}")
        result.append(selected)
    return tuple(result)


def project_nonroot(mask: int) -> int:
    result = 0
    for right in range(2, 7):
        for left in range(1, right):
            if (mask >> universal.edge_position(left, right)) & 1:
                result |= 1 << universal.edge_position(left - 1, right - 1)
    return result


@functools.cache
def conditioned_local_cubes() -> tuple[tuple[Cube, ...], ...]:
    root_positions = tuple(universal.edge_position(0, vertex) for vertex in range(1, 7))
    result = []
    for neighbour_count in range(7):
        target = tuple(sorted({
            project_nonroot(mask)
            for mask in forbidden_masks()
            if all(
                bool((mask >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_positions, 1)
            )
        }))
        index = {mask: item for item, mask in enumerate(target)}
        restricted: set[Cube] = set()
        for ones, fixed in reduced_cubes():
            if all(
                not ((fixed >> position) & 1)
                or bool((ones >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_positions, 1)
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
                key=lambda item: (len(active & item[0]), -item[2].bit_count(), -item[2], -item[1]),
            )
            newly_covered = active & coverage
            if not newly_covered:
                raise RuntimeError(f"conditioned local cover stuck at a={neighbour_count}")
            selected.append((ones, fixed))
            active -= newly_covered
        ordered = tuple(sorted(set(selected), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))
        if len(ordered) != LOCAL_CONDITIONED_COUNTS[neighbour_count]:
            raise RuntimeError(f"conditioned local count a={neighbour_count} changed: {len(ordered)}")
        rejected = {mask for mask in target if any((mask & fixed) == ones for ones, fixed in ordered)}
        if rejected != set(target):
            raise RuntimeError(f"conditioned local cover misses a={neighbour_count}")
        result.append(ordered)
    return tuple(result)


def clause_count(degree: int) -> int:
    if degree not in DEGREES:
        raise ValueError(f"degree must be one of {DEGREES}")
    root_free = sum(
        math.comb(degree, neighbours)
        * math.comb(11 - degree, 7 - neighbours)
        * BLOCK_CONDITIONED_COUNTS[neighbours]
        for neighbours in range(8)
        if neighbours <= degree and 7 - neighbours <= 11 - degree
    )
    root_containing = sum(
        math.comb(degree, neighbours)
        * math.comb(11 - degree, 6 - neighbours)
        * LOCAL_CONDITIONED_COUNTS[neighbours]
        for neighbours in range(7)
        if neighbours <= degree and 6 - neighbours <= 11 - degree
    )
    total = len(degree_branch.simplified_base_clauses(degree)) + root_free + root_containing
    if total != EXPECTED_CLAUSE_COUNTS[degree]:
        raise RuntimeError(f"cover6 degree-{degree} clause count changed: {total}")
    return total


def generate(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    validate_local_reduction()
    total = clause_count(degree)
    name = f"cover6_closed_block_degree_d{degree}.cnf"
    manifest_name = f"cover6_closed_block_degree_d{degree}_manifest.json"
    target = output / name
    manifest_path = output / manifest_name
    output.mkdir(parents=True, exist_ok=True)
    for path in (target, manifest_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace cover6 artifact: {path}")
    partial = output / f"{name}.{os.getpid()}.partial"
    blocks = block_conditioned_cubes()
    locals_ = conditioned_local_cubes()
    counts = Counter()
    widths: Counter[int] = Counter()
    try:
        with partial.open("xb", buffering=8 * 1024 * 1024) as stream:
            writer = degree_branch.HashedWriter(stream)
            writer.block(f"p cnf 66 {total}\n".encode("ascii"))
            base = degree_branch.simplified_base_clauses(degree)
            writer.clause_block(base)
            counts["base"] += len(base)
            widths.update(map(len, base))
            for vertices in itertools.combinations(range(1, 12), 7):
                neighbours = sum(vertex <= degree for vertex in vertices)
                variables = universal.subset_variables(vertices)
                clauses = tuple(universal.instantiate_cube_blocker(cube, variables) for cube in blocks[neighbours])
                writer.clause_block(clauses)
                counts["root_free"] += len(clauses)
                widths.update(map(len, clauses))
            for vertices in itertools.combinations(range(1, 12), 6):
                neighbours = sum(vertex <= degree for vertex in vertices)
                variables = degree_branch.six_subset_variables(vertices)
                clauses = tuple(degree_branch.instantiate(cube, variables) for cube in locals_[neighbours])
                writer.clause_block(clauses)
                counts["root_containing"] += len(clauses)
                widths.update(map(len, clauses))
            if writer.clauses != total:
                raise RuntimeError(f"written clause mismatch: {writer.clauses} != {total}")
            formula = {
                "name": name,
                "bytes": writer.bytes,
                "sha256": writer.digest.hexdigest().upper(),
                "variables": 66,
                "clauses": writer.clauses,
            }
        os.replace(partial, target)
    finally:
        if partial.exists():
            partial.unlink()
    manifest = {
        "schema_version": 1,
        "status": "UNCERTIFIED_COMPLEMENT_CLOSED_COVER6_DEGREE_TARGET",
        "scope": "Catalogue-independent residual K12 CNF; generation proves no UNSAT.",
        "degree": degree,
        "complementary_degree": 11 - degree,
        "source": {"name": COVER_PATH.name, "sha256": sha256(COVER_PATH), "records": list(read_records())},
        "local_target": {
            "labelled_masks": len(forbidden_masks()),
            "mask_sha256": EXPECTED_MASK_SHA256,
            "cubes": len(reduced_cubes()),
            "cube_sha256": EXPECTED_CUBE_SHA256,
            "closed_under_complement": True,
            "exact_on_local_r44": True,
        },
        "files": {"formula": formula},
        "counts": {
            "base": counts["base"],
            "root_free": counts["root_free"],
            "root_containing": counts["root_containing"],
            "total": total,
            "widths": dict(sorted(widths.items())),
        },
        "root_assignment_semantics": [
            variable if value else -variable
            for variable, value in degree_branch.root_assignment(degree).items()
        ],
        "formal_bridge_status": "not yet formalized in Lean",
        "proof_status": "no solver proof",
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    return manifest


def verify(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    manifest_path = output / f"cover6_closed_block_degree_d{degree}_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    metadata = manifest["files"]["formula"]
    path = output / metadata["name"]
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    if (digest, size, lines) != (metadata["sha256"], metadata["bytes"], clause_count(degree) + 1):
        raise ValueError("cover6 formula hash, size, or line count mismatch")
    return {"status": "PASS", "degree": degree, "sha256": digest, "bytes": size, "lines": lines}


def preflight() -> dict[str, object]:
    exact = validate_local_reduction()
    blocks = block_conditioned_cubes()
    locals_ = conditioned_local_cubes()
    return {
        "status": "PASS",
        "scope": "local exactness and deterministic counts only; no K12 CNF and no solver",
        "source_sha256": sha256(COVER_PATH),
        "records": list(read_records()),
        "labelled_masks": len(forbidden_masks()),
        "mask_sha256": EXPECTED_MASK_SHA256,
        "cubes": len(reduced_cubes()),
        "cube_sha256": EXPECTED_CUBE_SHA256,
        "cube_widths": EXPECTED_CUBE_WIDTHS,
        "closed_under_complement": True,
        "local_exactness": exact,
        "block_conditioned_counts": [len(items) for items in blocks],
        "local_conditioned_counts": [len(items) for items in locals_],
        "degree_clause_counts": {str(degree): clause_count(degree) for degree in DEGREES},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("preflight", "generate", "verify"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--degree", type=int, choices=DEGREES)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    else:
        if args.output is None or args.degree is None:
            parser.error("generate/verify require --output and --degree")
        result = generate(args.output, args.degree) if args.command == "generate" else verify(args.output, args.degree)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
