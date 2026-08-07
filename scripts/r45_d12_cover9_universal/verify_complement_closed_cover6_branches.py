#!/usr/bin/env python3
"""Independent stdlib verifier for the complement-closed cover6 reduction.

This file deliberately imports no project module.  It rebuilds graph6 masks,
S7 actions, R(4,4) validity, cube coverage, both conditioned reductions, and
the three global clause counts from frozen primitive data.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path, PureWindowsPath
from typing import Iterable, Sequence


N = 7
EDGE_COUNT = 21
LIMIT = 1 << EDGE_COUNT
FULL = LIMIT - 1
SOURCE = Path(__file__).resolve().parent.parent / "r45_d12_complement_closed_minimum" / "cover6_complement_closed.tsv"
SOURCE_SHA256 = "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
RECORDS = ("F@h^g", "FKDhw", "FG`Xo", "FdW}w", "FHFLw", "FIIXw")
ORBIT_SIZES = (5_040, 5_040, 2_520, 2_520, 5_040, 5_040)
MASK_COUNT = 25_200
MASK_SHA256 = "04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7"
R44_COUNT = 923_012
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
BLOCK_COUNTS = (2_520, 4_680, 10_200, 15_480, 15_480, 10_200, 4_680, 2_520)
LOCAL_COUNTS = (0, 300, 360, 540, 360, 300, 0)
DEGREE_COUNTS = {6: 4_858_890, 7: 4_312_419, 8: 3_367_437}

# Frozen after deterministic generation and the first independent full parse.
EXPECTED_FORMULAS: dict[int, tuple[int, str]] = {
    8: (189_298_232, "64E411A23778972A85DE7C8613A1977F98115E2EC3C9B1711D129932A4ECBB5A"),
}
Cube = tuple[int, int]


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def edge_index(left: int, right: int) -> int:
    if left == right:
        raise ValueError("loops are not edges")
    if left > right:
        left, right = right, left
    if left < 0 or right >= N:
        raise ValueError("edge endpoint out of range")
    return right * (right - 1) // 2 + left


def global_variable(left: int, right: int, order: int = 12) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < order:
        raise ValueError("global edge endpoint out of range")
    return left * (2 * order - left - 1) // 2 + right - left


def decode(record: str) -> int:
    if len(record) != 5 or ord(record[0]) != N + 63:
        raise ValueError(f"bad graph6 record: {record!r}")
    bits = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"bad graph6 payload: {record!r}")
        bits.extend((value >> shift) & 1 for shift in range(5, -1, -1))
    if any(bits[EDGE_COUNT:]):
        raise ValueError(f"nonzero graph6 padding: {record!r}")
    return sum(bit << position for position, bit in enumerate(bits[:EDGE_COUNT]))


def read_records() -> tuple[str, ...]:
    if file_sha256(SOURCE) != SOURCE_SHA256:
        raise ValueError("cover6 TSV hash mismatch")
    rows = []
    for raw in SOURCE.read_text(encoding="ascii").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        order, record = line.split("\t")
        if order != "7":
            raise ValueError("non-order-seven cover row")
        rows.append(record)
    result = tuple(rows)
    if result != RECORDS:
        raise ValueError(f"cover6 records changed: {result}")
    return result


@functools.cache
def permutation_maps() -> tuple[tuple[int, ...], ...]:
    maps = []
    for permutation in itertools.permutations(range(N)):
        maps.append(tuple(
            edge_index(permutation[left], permutation[right])
            for right in range(1, N)
            for left in range(right)
        ))
    return tuple(maps)


def transform(mask: int, mapping: Sequence[int]) -> int:
    return sum(((mask >> source) & 1) << target for target, source in enumerate(mapping))


def graph_orbit(mask: int) -> frozenset[int]:
    return frozenset(transform(mask, mapping) for mapping in permutation_maps())


def transformed_cubes(cube: Cube) -> frozenset[Cube]:
    ones, fixed = cube
    return frozenset((transform(ones, mapping), transform(fixed, mapping)) for mapping in permutation_maps())


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
def forbidden() -> frozenset[int]:
    pieces = tuple(graph_orbit(decode(record)) for record in read_records())
    if tuple(map(len, pieces)) != ORBIT_SIZES:
        raise ValueError("cover6 orbit sizes changed")
    if any(pieces[left] & pieces[right] for left in range(6) for right in range(left)):
        raise ValueError("cover6 motif orbits overlap")
    result = frozenset().union(*pieces)
    if len(result) != MASK_COUNT or masks_digest(result) != MASK_SHA256:
        raise ValueError("cover6 labelled closure changed")
    if {FULL ^ mask for mask in result} != result:
        raise ValueError("cover6 labelled target is not complement-closed")
    for pair in range(0, 6, 2):
        if {FULL ^ mask for mask in pieces[pair]} != pieces[pair + 1]:
            raise ValueError(f"records {pair}/{pair + 1} are not exact complements")
    return result


@functools.cache
def cubes() -> frozenset[Cube]:
    pieces = tuple(transformed_cubes(cube) for cube in CUBE_REPRESENTATIVES)
    if tuple(map(len, pieces)) != CUBE_ORBIT_SIZES:
        raise ValueError("cover6 cube orbit sizes changed")
    result = frozenset().union(*pieces)
    if len(result) != CUBE_COUNT:
        raise ValueError("cover6 cube count changed")
    if any(ones & ~fixed or fixed & ~FULL for ones, fixed in result):
        raise ValueError("malformed cover6 cube")
    if {(fixed ^ ones, fixed) for ones, fixed in result} != result:
        raise ValueError("cover6 cube family is not complement-closed")
    widths = Counter(fixed.bit_count() for _ones, fixed in result)
    if dict(sorted(widths.items())) != CUBE_WIDTHS:
        raise ValueError("cover6 cube widths changed")
    if cubes_digest(result) != CUBE_SHA256:
        raise ValueError("cover6 cube closure hash changed")
    return result


@functools.cache
def four_cliques() -> tuple[int, ...]:
    return tuple(
        sum(1 << edge_index(left, right) for left, right in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(N), 4)
    )


@functools.cache
def r44_flags() -> bytearray:
    result = bytearray(LIMIT)
    cliques = four_cliques()
    count = 0
    for mask in range(LIMIT):
        if all((mask & clique) not in (0, clique) for clique in cliques):
            result[mask] = 1
            count += 1
    if count != R44_COUNT:
        raise ValueError(f"independent R(4,4) count changed: {count}")
    return result


def completions(cube: Cube) -> Iterable[int]:
    ones, fixed = cube
    remaining = FULL ^ fixed
    while True:
        yield ones | remaining
        if remaining == 0:
            break
        remaining = (remaining - 1) & (FULL ^ fixed)


def validate_exactness() -> dict[str, int | bool]:
    valid = r44_flags()
    target = forbidden()
    covered: set[int] = set()
    for cube in cubes():
        for mask in completions(cube):
            if valid[mask]:
                if mask not in target:
                    raise ValueError(f"unsafe independent cube at {mask:#x}")
                covered.add(mask)
    if covered != target:
        raise ValueError(f"independent cubes miss {len(target - covered)} masks")
    return {
        "checked_assignments": LIMIT,
        "r44_assignments": sum(valid),
        "forbidden_assignments": len(target),
        "rejected_r44_assignments": len(covered),
        "exact": True,
    }


def triangles(vertices: range) -> tuple[int, ...]:
    return tuple(
        sum(1 << edge_index(left, right) for left, right in itertools.combinations(triple, 2))
        for triple in itertools.combinations(vertices, 3)
    )


def block_counts() -> tuple[int, ...]:
    result = []
    for neighbour_count in range(8):
        positive = triangles(range(neighbour_count))
        negative = triangles(range(neighbour_count, 7))
        target = tuple(sorted(
            mask for mask in forbidden()
            if all((mask & triangle) != triangle for triangle in positive)
            and all((mask & triangle) != 0 for triangle in negative)
        ))
        lookup = {mask: index for index, mask in enumerate(target)}
        coverages: dict[int, Cube] = {}
        for ones, fixed in cubes():
            coverage = 0
            for mask in completions((ones, fixed)):
                index = lookup.get(mask)
                if index is not None:
                    coverage |= 1 << index
            if not coverage:
                continue
            old = coverages.get(coverage)
            if old is None or (fixed.bit_count(), fixed, ones) < (old[1].bit_count(), old[1], old[0]):
                coverages[coverage] = (ones, fixed)
        union = 0
        for coverage in coverages:
            union |= coverage
        if union != (1 << len(target)) - 1:
            raise ValueError(f"independent block slice misses a={neighbour_count}")
        result.append(len(coverages))
    observed = tuple(result)
    if observed != BLOCK_COUNTS:
        raise ValueError(f"independent block counts changed: {observed}")
    return observed


def project(mask: int) -> int:
    result = 0
    for right in range(2, 7):
        for left in range(1, right):
            if (mask >> edge_index(left, right)) & 1:
                result |= 1 << edge_index(left - 1, right - 1)
    return result


def local_counts() -> tuple[int, ...]:
    root_edges = tuple(edge_index(0, vertex) for vertex in range(1, 7))
    observed = []
    for neighbour_count in range(7):
        target = tuple(sorted({
            project(mask)
            for mask in forbidden()
            if all(
                bool((mask >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_edges, 1)
            )
        }))
        lookup = {mask: index for index, mask in enumerate(target)}
        projected_cubes = set()
        for ones, fixed in cubes():
            compatible = all(
                not ((fixed >> position) & 1)
                or bool((ones >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_edges, 1)
            )
            if compatible:
                projected_cubes.add((project(ones), project(fixed)))
        candidates = []
        for ones, fixed in projected_cubes:
            coverage = 0
            for mask in target:
                if (mask & fixed) == ones:
                    coverage |= 1 << lookup[mask]
            if coverage:
                candidates.append((coverage, ones, fixed))
        active = (1 << len(target)) - 1
        selected: set[Cube] = set()
        while active:
            coverage, ones, fixed = max(
                candidates,
                key=lambda item: ((active & item[0]).bit_count(), -item[2].bit_count(), -item[2], -item[1]),
            )
            newly = active & coverage
            if not newly:
                raise ValueError(f"independent greedy cover stuck at a={neighbour_count}")
            selected.add((ones, fixed))
            active &= ~coverage
        observed.append(len(selected))
    result = tuple(observed)
    if result != LOCAL_COUNTS:
        raise ValueError(f"independent local counts changed: {result}")
    return result


def base_clause_count(degree: int) -> int:
    return 2 * math.comb(11, 4) + math.comb(degree, 3) + math.comb(11 - degree, 3)


def degree_clause_count(degree: int) -> int:
    if degree not in DEGREE_COUNTS:
        raise ValueError("degree must be 6, 7, or 8")
    blocks = BLOCK_COUNTS
    locals_ = LOCAL_COUNTS
    root_free = sum(
        math.comb(degree, neighbours) * math.comb(11 - degree, 7 - neighbours) * blocks[neighbours]
        for neighbours in range(8)
        if neighbours <= degree and 7 - neighbours <= 11 - degree
    )
    root_containing = sum(
        math.comb(degree, neighbours) * math.comb(11 - degree, 6 - neighbours) * locals_[neighbours]
        for neighbours in range(7)
        if neighbours <= degree and 6 - neighbours <= 11 - degree
    )
    total = base_clause_count(degree) + root_free + root_containing
    if total != DEGREE_COUNTS[degree]:
        raise ValueError(f"independent degree-{degree} count changed: {total}")
    return total


def require_ssd(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise ValueError(f"formula directory must be absolute on S:, got {path}")
    return path


def verify_formula(output: Path, degree: int) -> dict[str, object]:
    output = require_ssd(output)
    expected_count = degree_clause_count(degree)
    manifest_path = output / f"cover6_closed_block_degree_d{degree}_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("degree") != degree:
        raise ValueError("manifest degree mismatch")
    local = manifest.get("local_target", {})
    if local.get("mask_sha256") != MASK_SHA256 or local.get("cube_sha256") != CUBE_SHA256:
        raise ValueError("manifest local reduction mismatch")
    metadata = manifest["files"]["formula"]
    if metadata.get("variables") != 66 or metadata.get("clauses") != expected_count:
        raise ValueError("manifest formula dimensions mismatch")
    formula = output / metadata["name"]
    digest = hashlib.sha256()
    size = 0
    lines = 0
    clauses = 0
    with formula.open("rb") as stream:
        for raw in stream:
            digest.update(raw)
            size += len(raw)
            lines += 1
            if lines == 1:
                if raw != f"p cnf 66 {expected_count}\n".encode("ascii"):
                    raise ValueError("independent DIMACS header mismatch")
                continue
            values = tuple(map(int, raw.split()))
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError(f"malformed clause line {lines}")
            literals = values[:-1]
            if any(not 1 <= abs(literal) <= 66 for literal in literals):
                raise ValueError(f"literal out of range at line {lines}")
            if len(set(literals)) != len(literals) or any(-literal in literals for literal in literals):
                raise ValueError(f"duplicate/tautological clause at line {lines}")
            clauses += 1
    observed_hash = digest.hexdigest().upper()
    if (clauses, lines, size, observed_hash) != (
        expected_count,
        expected_count + 1,
        metadata["bytes"],
        metadata["sha256"],
    ):
        raise ValueError("formula count, size, or digest mismatch")
    frozen = EXPECTED_FORMULAS.get(degree)
    if frozen is not None and (size, observed_hash) != frozen:
        raise ValueError("formula differs from independently frozen artifact")
    return {
        "status": "PASS",
        "degree": degree,
        "clauses": clauses,
        "bytes": size,
        "sha256": observed_hash,
        "frozen_artifact_checked": frozen is not None,
    }


def preflight() -> dict[str, object]:
    exact = validate_exactness()
    blocks = block_counts()
    locals_ = local_counts()
    return {
        "status": "PASS",
        "implementation": "standalone stdlib; imports no project module",
        "source_sha256": file_sha256(SOURCE),
        "records": list(read_records()),
        "labelled_masks": len(forbidden()),
        "mask_sha256": masks_digest(forbidden()),
        "cubes": len(cubes()),
        "cube_sha256": cubes_digest(cubes()),
        "cube_widths": dict(sorted(Counter(fixed.bit_count() for _ones, fixed in cubes()).items())),
        "closed_under_complement": True,
        "local_exactness": exact,
        "block_conditioned_counts": list(blocks),
        "local_conditioned_counts": list(locals_),
        "degree_clause_counts": {str(degree): degree_clause_count(degree) for degree in sorted(DEGREE_COUNTS)},
        "scope": "local exactness and clause arithmetic; no catalogue, SAT, LRAT, or Lean claim",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", default="preflight", choices=("preflight", "formula"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--degree", type=int, choices=tuple(DEGREE_COUNTS))
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    else:
        if args.output is None or args.degree is None:
            parser.error("formula verification requires --output and --degree")
        result = verify_formula(args.output, args.degree)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
