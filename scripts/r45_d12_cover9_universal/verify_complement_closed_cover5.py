#!/usr/bin/env python3
"""Independent exhaustive verifier for the complement-closed cover5 cubes.

This module intentionally imports no project code.  It rebuilds graph6
adjacency rows, S7 actions, local R(4,4) validity, and cube matching using an
implementation separate from the generator.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from array import array
from collections import Counter
from typing import Iterable, Sequence


N = 7
EDGE_COUNT = 21
LIMIT = 1 << EDGE_COUNT
FULL = LIMIT - 1
Cube = tuple[int, int]

RECORDS = ("F@h^g", "FCUrO", "FDLmW", "FG`Xo", "FdW}w")
CUBE_REPRESENTATIVES = (
    (0x3, 0xDF677),
    (0x3E6BE, 0x1BE6BE),
    (0x84AE, 0x19F5BF),
    (0x8DBC, 0x1DCDFE),
    (0x3AFE2, 0x17FFF7),
    (0x88EC, 0x1BEFFF),
)

EXPECTED_R44 = 923_012
EXPECTED_RAW = 17_640
EXPECTED_INTERSECTION = 5_040
EXPECTED_CLOSED = 30_240
EXPECTED_CLASSES = 8
EXPECTED_CUBES = 20_160
EXPECTED_WIDTHS = {15: 5_040, 16: 10_080, 19: 5_040}
EXPECTED_ORBIT_SIZES = (2_520, 2_520, 5_040, 5_040, 2_520, 2_520)
EXPECTED_RAW_SHA256 = "7D9C82BAA06CC6FB778ED24643E63E58D50594F13D11D4D49E8E0BE14DE578E2"
EXPECTED_CLOSED_SHA256 = (
    "DC2CBCDA3F5D51BE6141B975AA440E51D9F85D6CF1337E4597EDADDF445E227A"
)
EXPECTED_CUBE_SHA256 = "5E965F8913D4F35391D1C1A3D4890122A19D8D711E4329806B108A39B609EDB7"


PAIRS = tuple((left, right) for right in range(1, N) for left in range(right))
PAIR_INDEX = {pair: index for index, pair in enumerate(PAIRS)}
PERMUTATIONS = tuple(itertools.permutations(range(N)))


def decode_rows(record: str) -> tuple[int, ...]:
    if len(record) != 5 or ord(record[0]) - 63 != N:
        raise ValueError(f"invalid graph6 record: {record!r}")
    payload: list[int] = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 character: {record!r}")
        payload.extend(value >> shift & 1 for shift in range(5, -1, -1))
    if any(payload[EDGE_COUNT:]):
        raise ValueError(f"nonzero graph6 padding: {record!r}")
    rows = [0] * N
    for bit, (left, right) in zip(payload, PAIRS):
        if bit:
            rows[left] |= 1 << right
            rows[right] |= 1 << left
    return tuple(rows)


def rows_to_mask(rows: Sequence[int]) -> int:
    return sum(
        1 << position
        for position, (left, right) in enumerate(PAIRS)
        if rows[left] >> right & 1
    )


def permuted_rows_mask(rows: Sequence[int], permutation: Sequence[int]) -> int:
    result = 0
    for target, (left, right) in enumerate(PAIRS):
        if rows[permutation[left]] >> permutation[right] & 1:
            result |= 1 << target
    return result


def permuted_bits(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    for target, (left, right) in enumerate(PAIRS):
        source = tuple(sorted((permutation[left], permutation[right])))
        result |= (mask >> PAIR_INDEX[source] & 1) << target
    return result


def graph_orbit_from_rows(rows: Sequence[int]) -> frozenset[int]:
    return frozenset(permuted_rows_mask(rows, permutation) for permutation in PERMUTATIONS)


def graph_orbit_from_mask(mask: int) -> frozenset[int]:
    return frozenset(permuted_bits(mask, permutation) for permutation in PERMUTATIONS)


def cube_orbit(cube: Cube) -> frozenset[Cube]:
    ones, fixed = cube
    return frozenset(
        (permuted_bits(ones, permutation), permuted_bits(fixed, permutation))
        for permutation in PERMUTATIONS
    )


def k4_masks() -> tuple[int, ...]:
    masks: list[int] = []
    for vertices in itertools.combinations(range(N), 4):
        mask = 0
        for edge in itertools.combinations(vertices, 2):
            mask |= 1 << PAIR_INDEX[tuple(sorted(edge))]
        masks.append(mask)
    return tuple(masks)


def exhaustive_r44_flags() -> bytearray:
    cliques = k4_masks()
    valid = bytearray(LIMIT)
    for mask in range(LIMIT):
        for clique in cliques:
            intersection = mask & clique
            if intersection == 0 or intersection == clique:
                break
        else:
            valid[mask] = 1
    if sum(valid) != EXPECTED_R44:
        raise ValueError(f"independent R(4,4) count mismatch: {sum(valid)}")
    return valid


def matching_masks(cube: Cube) -> Iterable[int]:
    ones, fixed = cube
    if ones & ~fixed or fixed & ~FULL:
        raise ValueError(f"malformed cube: {cube}")
    free = FULL ^ fixed
    completion = free
    while True:
        yield ones | completion
        if completion == 0:
            break
        completion = (completion - 1) & free


def mask_digest(masks: Iterable[int]) -> str:
    digest = hashlib.sha256()
    for mask in sorted(masks):
        digest.update(f"{mask:06X}\n".encode("ascii"))
    return digest.hexdigest().upper()


def cube_digest(cubes: Iterable[Cube]) -> str:
    digest = hashlib.sha256()
    for ones, fixed in sorted(cubes, key=lambda cube: (cube[1], cube[0])):
        digest.update(f"{ones:06X}\t{fixed:06X}\n".encode("ascii"))
    return digest.hexdigest().upper()


def verify(
    cube_representatives: Sequence[Cube] = CUBE_REPRESENTATIVES,
) -> dict[str, object]:
    raw_orbits = tuple(graph_orbit_from_rows(decode_rows(record)) for record in RECORDS)
    raw = frozenset().union(*raw_orbits)
    complemented = frozenset(FULL ^ mask for mask in raw)
    closed = raw | complemented
    seed_orbits = raw_orbits + tuple(
        graph_orbit_from_mask(FULL ^ rows_to_mask(decode_rows(record)))
        for record in RECORDS
    )
    unique_classes = {orbit for orbit in seed_orbits}
    if len(raw) != EXPECTED_RAW or len(complemented) != EXPECTED_RAW:
        raise ValueError("independent raw closure count mismatch")
    if len(raw & complemented) != EXPECTED_INTERSECTION:
        raise ValueError("independent raw/complement intersection mismatch")
    if len(closed) != EXPECTED_CLOSED or len(unique_classes) != EXPECTED_CLASSES:
        raise ValueError("independent complement closure mismatch")
    if closed != {FULL ^ mask for mask in closed}:
        raise ValueError("forbidden target is not complement-closed")
    if mask_digest(raw) != EXPECTED_RAW_SHA256:
        raise ValueError("independent raw closure SHA-256 mismatch")
    if mask_digest(closed) != EXPECTED_CLOSED_SHA256:
        raise ValueError("independent complement closure SHA-256 mismatch")

    orbits = tuple(cube_orbit(cube) for cube in cube_representatives)
    orbit_sizes = tuple(map(len, orbits))
    cubes = frozenset().union(*orbits)
    widths = Counter(fixed.bit_count() for _ones, fixed in cubes)
    if orbit_sizes != EXPECTED_ORBIT_SIZES:
        raise ValueError(f"independent cube orbit sizes changed: {orbit_sizes}")
    if len(cubes) != EXPECTED_CUBES or dict(widths) != EXPECTED_WIDTHS:
        raise ValueError("independent cube closure count or widths mismatch")
    if cube_digest(cubes) != EXPECTED_CUBE_SHA256:
        raise ValueError("independent cube closure SHA-256 mismatch")
    if cubes != {(fixed ^ ones, fixed) for ones, fixed in cubes}:
        raise ValueError("independent cube closure is not complement-closed")

    valid = exhaustive_r44_flags()
    coverage = array("I", [0]) * LIMIT
    for cube in cubes:
        for mask in matching_masks(cube):
            if valid[mask]:
                if mask not in closed:
                    raise ValueError(f"cube unsafely covers allowed mask {mask:#x}")
                coverage[mask] += 1

    mismatches = 0
    for mask in range(LIMIT):
        expected = bool(valid[mask]) and mask in closed
        mismatches += expected != (coverage[mask] != 0)
    if mismatches:
        raise ValueError(f"independent exhaustive equivalence has {mismatches} mismatches")

    unique_witness_cubes = 0
    for cube in cubes:
        if any(valid[mask] and coverage[mask] == 1 for mask in matching_masks(cube)):
            unique_witness_cubes += 1
    if unique_witness_cubes != EXPECTED_CUBES:
        raise ValueError("independent cube-deletion audit found a removable cube")

    return {
        "schema_version": 1,
        "status": "PASS",
        "scope": {
            "self_complementary_local_target": True,
            "checked_assignments": LIMIT,
            "k12_formula_generated": False,
            "solver_invoked": False,
            "unsat_claimed": False,
            "global_minimality_claimed": False,
        },
        "complement_closure": {
            "raw_masks": len(raw),
            "complement_masks": len(complemented),
            "intersection": len(raw & complemented),
            "closed_masks": len(closed),
            "isomorphism_classes": len(unique_classes),
            "raw_sha256": mask_digest(raw),
            "closed_sha256": mask_digest(closed),
        },
        "cube_closure": {
            "representatives": len(cube_representatives),
            "orbit_sizes": list(orbit_sizes),
            "cubes": len(cubes),
            "widths": dict(sorted(widths.items())),
            "sha256": cube_digest(cubes),
            "complement_closed": True,
            "exact_on_r44": True,
            "unique_witness_cubes": unique_witness_cubes,
            "deletion_irredundant": True,
        },
        "exhaustive": {
            "assignments": LIMIT,
            "r44_assignments": sum(valid),
            "forbidden_r44_assignments": len(closed),
            "rejected_r44_assignments": sum(
                bool(valid[mask]) and coverage[mask] != 0 for mask in range(LIMIT)
            ),
        },
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
