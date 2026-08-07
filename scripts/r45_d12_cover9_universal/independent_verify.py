#!/usr/bin/env python3
"""Independent local verifier for the reduced cover9 clauses.

This intentionally does not import the generator.  It uses an adjacency-row
representation for graph6 and rebuilds both permutation closures from first
principles.  The public ``verify`` function accepts cube representatives so
tests can demonstrate that a one-bit corruption is rejected.
"""

from __future__ import annotations

import itertools
from typing import Sequence


RECORDS = ("FiIXw", "FANbw", "F@Y]w", "FqhXw", "FFhmw", "FqHXw", "FQl~_", "FIiZw", "Fqoxw")
EXPECTED_FORBIDDEN = 26_460
EXPECTED_R44 = 923_012
EXPECTED_CUBES = 15_120
N = 7
EDGE_COUNT = 21


def pairs() -> tuple[tuple[int, int], ...]:
    return tuple((left, right) for right in range(1, N) for left in range(right))


PAIRS = pairs()
PAIR_INDEX = {edge: index for index, edge in enumerate(PAIRS)}


def decode_rows(record: str) -> tuple[int, ...]:
    if len(record) != 5 or ord(record[0]) - 63 != N:
        raise ValueError(f"bad graph6 record: {record!r}")
    payload = []
    for char in record[1:]:
        value = ord(char) - 63
        if not 0 <= value < 64:
            raise ValueError("bad graph6 character")
        payload.extend((value >> bit) & 1 for bit in range(5, -1, -1))
    if any(payload[EDGE_COUNT:]):
        raise ValueError("non-zero graph6 padding")
    rows = [0] * N
    for bit, (left, right) in zip(payload, PAIRS):
        if bit:
            rows[left] |= 1 << right
            rows[right] |= 1 << left
    return tuple(rows)


def permuted_mask(rows: Sequence[int], permutation: Sequence[int]) -> int:
    result = 0
    for target_position, (left, right) in enumerate(PAIRS):
        source_left = permutation[left]
        source_right = permutation[right]
        if (rows[source_left] >> source_right) & 1:
            result |= 1 << target_position
    return result


def permute_bits(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    for target_position, (left, right) in enumerate(PAIRS):
        source = tuple(sorted((permutation[left], permutation[right])))
        if (mask >> PAIR_INDEX[source]) & 1:
            result |= 1 << target_position
    return result


def clique_masks() -> tuple[int, ...]:
    return tuple(
        sum(1 << PAIR_INDEX[tuple(sorted(edge))] for edge in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(N), 4)
    )


def verify(cube_representatives: Sequence[tuple[int, int]]) -> dict[str, int | str]:
    permutations = tuple(itertools.permutations(range(N)))
    forbidden = {
        permuted_mask(decode_rows(record), permutation)
        for record in RECORDS
        for permutation in permutations
    }
    if len(forbidden) != EXPECTED_FORBIDDEN:
        raise ValueError("independent forbidden closure count mismatch")
    cubes = {
        (permute_bits(ones, permutation), permute_bits(fixed, permutation))
        for ones, fixed in cube_representatives
        for permutation in permutations
    }
    if len(cubes) != EXPECTED_CUBES:
        raise ValueError(f"independent reduced cube count mismatch: {len(cubes)}")

    local_cliques = clique_masks()
    valid = bytearray(1 << EDGE_COUNT)
    valid_count = 0
    for mask in range(1 << EDGE_COUNT):
        if all((mask & clique) not in (0, clique) for clique in local_cliques):
            valid[mask] = 1
            valid_count += 1
    if valid_count != EXPECTED_R44:
        raise ValueError("independent local R(4,4) count mismatch")

    rejected: set[int] = set()
    full = (1 << EDGE_COUNT) - 1
    for ones, fixed in cubes:
        if ones & ~fixed:
            raise ValueError("malformed cube")
        free = full ^ fixed
        completion = free
        while True:
            assignment = ones | completion
            if valid[assignment]:
                if assignment not in forbidden:
                    raise ValueError("reduced cube unsafely rejects an allowed assignment")
                rejected.add(assignment)
            if completion == 0:
                break
            completion = (completion - 1) & free
    if rejected != forbidden:
        raise ValueError(f"reduced cubes miss {len(forbidden - rejected)} forbidden assignments")
    return {
        "status": "PASS",
        "checked_assignments": 1 << EDGE_COUNT,
        "r44_assignments": valid_count,
        "forbidden_assignments": len(forbidden),
        "reduced_cubes": len(cubes),
    }

def verify_conditioned_slices(
    conditioned: Sequence[Sequence[tuple[int, int]]],
) -> dict[str, object]:
    """Independently check all 7 * 2^15 root-conditioned assignments."""
    if len(conditioned) != 7:
        raise ValueError("expected seven root-neighbour slices")
    permutations = tuple(itertools.permutations(range(N)))
    forbidden = {
        permuted_mask(decode_rows(record), permutation)
        for record in RECORDS
        for permutation in permutations
    }
    local_cliques = clique_masks()
    pairs6 = tuple((left, right) for right in range(1, 6) for left in range(right))
    counts = []
    for neighbour_count, cubes in enumerate(conditioned):
        expected: set[int] = set()
        rejected: set[int] = set()
        for mask6 in range(1 << 15):
            lifted = 0
            for vertex in range(1, 7):
                if vertex <= neighbour_count:
                    lifted |= 1 << PAIR_INDEX[(0, vertex)]
            for position6, (left, right) in enumerate(pairs6):
                if (mask6 >> position6) & 1:
                    lifted |= 1 << PAIR_INDEX[(left + 1, right + 1)]
            valid = all((lifted & clique) not in (0, clique) for clique in local_cliques)
            if valid and lifted in forbidden:
                expected.add(mask6)
            if valid and any((mask6 & fixed) == ones for ones, fixed in cubes):
                rejected.add(mask6)
        if rejected != expected:
            raise ValueError(
                f"conditioned slice {neighbour_count} differs: "
                f"missing={len(expected - rejected)}, extra={len(rejected - expected)}"
            )
        counts.append(len(expected))
    if counts != [0, 60, 240, 576, 612, 300, 0]:
        raise ValueError(f"conditioned forbidden slice counts changed: {counts}")
    return {
        "status": "PASS",
        "checked_assignments": 7 * (1 << 15),
        "forbidden_slice_counts": counts,
        "conditioned_cube_counts": [len(cubes) for cubes in conditioned],
    }
