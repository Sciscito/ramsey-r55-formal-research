#!/usr/bin/env python3
"""Standalone, read-only audit of the frozen cover9 d8/p2/q0 CNF.

This file deliberately imports only the Python standard library.  It does not
read the project generators and it never writes a CNF.  Starting with the nine
frozen graph6 records, it independently rebuilds

* their labelled S_7 closure;
* the six reduced-cube S_7 closures and their exhaustive 2^21 safety proof;
* all 990 K_12 R(4,4) clauses and the canonical degree-eight root slice;
* the root-block triangle conditioning and the root-containing slices;
* the p=2, q=0 second-centre restriction and global exact deduplication.

The resulting clauses are sorted exactly as in the published DIMACS artifact,
but are only hashed in memory.  If a CNF path is supplied, every expected line
is compared byte-for-byte while it is hashed; the file is never copied.
Optional LRAT and Lean replay paths are checked against their frozen hashes.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
import sys
from collections import Counter
from pathlib import Path
from typing import Callable, Iterable, Iterator, Mapping, Sequence


ORDER = 12
LOCAL_ORDER = 7
LOCAL_EDGE_COUNT = 21
VARIABLE_COUNT = 66
ROOT_DEGREE = 8

COVER_RECORDS = (
    "FiIXw",
    "FANbw",
    "F@Y]w",
    "FqhXw",
    "FFhmw",
    "FqHXw",
    "FQl~_",
    "FIiZw",
    "Fqoxw",
)
EXPECTED_RAW_ORBIT_COUNTS = (5_040, 2_520, 5_040, 2_520, 2_520, 2_520, 2_520, 2_520, 1_260)
EXPECTED_RAW_FORBIDDEN = 26_460

# A cube (ones, fixed) matches m exactly when m & fixed == ones.
REDUCED_CUBE_REPRESENTATIVES = (
    (0x2964E, 0x39EDF),
    (0x3EF43, 0x3EF73),
    (0x3846A, 0x3EEEF),
    (0x2AF9C, 0x7BFDE),
    (0x3AFE1, 0x7BFFF),
    (0x1C75C, 0x7DFFF),
)
EXPECTED_REDUCED_ORBIT_COUNTS = (1_260, 2_520, 2_520, 2_520, 1_260, 5_040)
EXPECTED_REDUCED_CUBES = 15_120
EXPECTED_REDUCED_WIDTHS = {14: 3_780, 15: 2_520, 16: 2_520, 18: 6_300}
EXPECTED_LOCAL_R44 = 923_012
EXPECTED_LOCAL_ALLOWED = 896_552

EXPECTED_BLOCK_CUBE_COUNTS = (2_520, 5_760, 9_960, 11_448, 9_396, 5_040, 1_260, 0)
EXPECTED_RESTRICTED_CUBE_COUNTS = (0, 210, 384, 666, 1_080, 1_530, 2_160)
EXPECTED_CONDITIONED_CUBE_COUNTS = (0, 30, 216, 414, 432, 150, 0)
EXPECTED_CONDITIONED_FORBIDDEN_COUNTS = (0, 60, 240, 576, 612, 300, 0)

EXPECTED_BASE_CLAUSES = 990
EXPECTED_ROOT_BASE_CLAUSES = 717
EXPECTED_ROOT_FREE_CLAUSES = 1_610_280
EXPECTED_ROOT_CONTAINING_CLAUSES = 139_104
EXPECTED_ROOT_SOURCE_CLAUSES = 1_750_101

EXPECTED_FINAL_CLAUSES = 758_924
EXPECTED_FINAL_BYTES = 44_764_698
EXPECTED_FINAL_LINES = 758_925
EXPECTED_FINAL_SHA256 = "D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315"
EXPECTED_REDUCTION = {
    "source_clauses": 1_750_101,
    "satisfied_clauses_removed": 991_056,
    "surviving_before_deduplication": 759_045,
    "exact_duplicates_removed": 121,
    "false_literals_removed": 71_264,
}
EXPECTED_FINAL_WIDTHS = {
    1: 1,
    3: 91,
    5: 90,
    6: 2_760,
    7: 660,
    8: 4_500,
    9: 7_992,
    10: 12_990,
    11: 20_340,
    12: 25_350,
    13: 6_300,
    14: 124_710,
    15: 131_040,
    16: 100_800,
    18: 321_300,
}

EXPECTED_LRAT_BYTES = 10_683_195
EXPECTED_LRAT_SHA256 = "4C65A4480E9BDD8B0F526DE496A774795905C23DD1067D1B4574D267388403C5"
EXPECTED_LRAT_FINAL_CLAUSE_ID = 859_522
EXPECTED_REPLAY_LEAN_SHA256 = "D7A98BA64EB493E1F81C8EEFE479C0843DC83E484D28B99AD7A9E307B9887B86"
EXPECTED_REPLAY_LOG_SHA256 = "73918BAA31F9D53A327BAD3FA44537D6F78348E8100966D028D4B81F621AC8C3"
EXPECTED_REPLAY_JSON_SHA256 = "CB95B0D3F20546508B8CE97811062F8FD325AEBC0296378F0A79A9B6A2FCBED3"
EXPECTED_REPLAY_STATUS = "LEAN_LRAT_REPLAY_SUCCEEDED"
EXPECTED_THEOREM = (
    "LRATCatcher.Tests.R45D12Cover9UniversalP2Q0Replay."
    "cover9_d8_two_center_p2_q0_unsat"
)

Cube = tuple[int, int]
Clause = tuple[int, ...]
Progress = Callable[[str], None]

LOCAL_PAIRS = tuple((left, right) for right in range(1, LOCAL_ORDER) for left in range(right))
LOCAL_PAIR_INDEX = {pair: index for index, pair in enumerate(LOCAL_PAIRS)}
SIX_PAIRS = tuple((left, right) for right in range(1, 6) for left in range(right))
POSITIVE_LITERAL = tuple(range(VARIABLE_COUNT + 1))
NEGATIVE_LITERAL = tuple(-value for value in range(VARIABLE_COUNT + 1))

FAMILY_BASE = 1
FAMILY_ROOT_FREE = 2
FAMILY_ROOT_CONTAINING = 4
FAMILY_NAMES = {
    FAMILY_BASE: "base_r44",
    FAMILY_ROOT_FREE: "root_free_block_motif",
    FAMILY_ROOT_CONTAINING: "root_containing_motif",
}


class AuditError(ValueError):
    """Raised when an independently reconstructed invariant changes."""


def _require(observed: object, expected: object, label: str) -> None:
    if observed != expected:
        raise AuditError(f"{label}: observed {observed!r}, expected {expected!r}")


def edge_var(order: int, left: int, right: int) -> int:
    """One-based row-major DIMACS variable for an unordered edge."""
    if left > right:
        left, right = right, left
    if not 0 <= left < right < order:
        raise AuditError(f"not an edge of K_{order}: {(left, right)}")
    return left * (2 * order - left - 1) // 2 + right - left


def decode_graph6_rows(record: str) -> tuple[int, ...]:
    """Decode one short order-seven graph6 record into adjacency rows."""
    if len(record) != 5 or ord(record[0]) - 63 != LOCAL_ORDER:
        raise AuditError(f"invalid order-seven graph6 record: {record!r}")
    payload: list[int] = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise AuditError(f"invalid graph6 payload character in {record!r}")
        payload.extend((value >> bit) & 1 for bit in range(5, -1, -1))
    if any(payload[LOCAL_EDGE_COUNT:]):
        raise AuditError(f"non-zero graph6 padding in {record!r}")
    rows = [0] * LOCAL_ORDER
    for bit, (left, right) in zip(payload, LOCAL_PAIRS):
        if bit:
            rows[left] |= 1 << right
            rows[right] |= 1 << left
    return tuple(rows)


def permuted_rows_mask(rows: Sequence[int], permutation: Sequence[int]) -> int:
    """Relabel adjacency rows; permutation maps target vertices to sources."""
    result = 0
    for target_position, (left, right) in enumerate(LOCAL_PAIRS):
        source_left = permutation[left]
        source_right = permutation[right]
        if (rows[source_left] >> source_right) & 1:
            result |= 1 << target_position
    return result


def permuted_bit_mask(mask: int, permutation: Sequence[int]) -> int:
    """Relabel a 21-bit graph/cube support independently of adjacency rows."""
    result = 0
    for target_position, (left, right) in enumerate(LOCAL_PAIRS):
        source_left = permutation[left]
        source_right = permutation[right]
        if source_left > source_right:
            source_left, source_right = source_right, source_left
        if (mask >> LOCAL_PAIR_INDEX[(source_left, source_right)]) & 1:
            result |= 1 << target_position
    return result


def build_raw_forbidden(
    permutations: Sequence[Sequence[int]] | None = None,
) -> tuple[frozenset[int], tuple[int, ...]]:
    """Build the nine individual S_7 orbits and their exact union."""
    group = (
        tuple(itertools.permutations(range(LOCAL_ORDER)))
        if permutations is None
        else tuple(permutations)
    )
    orbits = tuple(
        frozenset(permuted_rows_mask(decode_graph6_rows(record), permutation) for permutation in group)
        for record in COVER_RECORDS
    )
    counts = tuple(map(len, orbits))
    _require(counts, EXPECTED_RAW_ORBIT_COUNTS, "nine graph6 orbit sizes")
    union = frozenset().union(*orbits)
    _require(len(union), EXPECTED_RAW_FORBIDDEN, "nine-orbit union size")
    return union, counts


def build_reduced_cubes(
    permutations: Sequence[Sequence[int]] | None = None,
) -> tuple[tuple[Cube, ...], tuple[int, ...]]:
    """Build the six frozen cube-representative S_7 closures."""
    group = (
        tuple(itertools.permutations(range(LOCAL_ORDER)))
        if permutations is None
        else tuple(permutations)
    )
    orbits = tuple(
        frozenset(
            (permuted_bit_mask(ones, permutation), permuted_bit_mask(fixed, permutation))
            for permutation in group
        )
        for ones, fixed in REDUCED_CUBE_REPRESENTATIVES
    )
    counts = tuple(map(len, orbits))
    _require(counts, EXPECTED_REDUCED_ORBIT_COUNTS, "six reduced-cube orbit sizes")
    union = frozenset().union(*orbits)
    _require(len(union), EXPECTED_REDUCED_CUBES, "reduced-cube union size")
    if any(ones & ~fixed for ones, fixed in union):
        raise AuditError("a reduced cube fixes a one outside its support")
    ordered = tuple(sorted(union, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))
    return ordered, counts


def local_k4_masks() -> tuple[int, ...]:
    return tuple(
        sum(1 << LOCAL_PAIR_INDEX[pair] for pair in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(LOCAL_ORDER), 4)
    )


def is_local_r44(mask: int, clique_masks: Sequence[int]) -> bool:
    for clique in clique_masks:
        intersection = mask & clique
        if intersection == 0 or intersection == clique:
            return False
    return True


def audit_local_reduction(forbidden: frozenset[int], cubes: Sequence[Cube]) -> dict[str, object]:
    """Check every one of the 2^21 local assignments, without a solver."""
    limit = 1 << LOCAL_EDGE_COUNT
    full = limit - 1
    matched = bytearray(limit)
    widths = Counter()
    supports = Counter()
    for ones, fixed in cubes:
        if ones & ~fixed:
            raise AuditError("malformed reduced cube")
        widths[fixed.bit_count()] += 1
        vertices: set[int] = set()
        for position, (left, right) in enumerate(LOCAL_PAIRS):
            if (fixed >> position) & 1:
                vertices.update((left, right))
        supports[len(vertices)] += 1
        free = full ^ fixed
        completion = free
        while True:
            matched[ones | completion] = 1
            if completion == 0:
                break
            completion = (completion - 1) & free
    _require(dict(sorted(widths.items())), EXPECTED_REDUCED_WIDTHS, "reduced cube widths")
    _require(dict(supports), {LOCAL_ORDER: EXPECTED_REDUCED_CUBES}, "reduced cube vertex supports")

    cliques = local_k4_masks()
    _require(len(cliques), math.comb(LOCAL_ORDER, 4), "local K4-mask count")
    r44_count = 0
    rejected_under_r44 = 0
    first_difference: int | None = None
    for mask in range(limit):
        if not is_local_r44(mask, cliques):
            continue
        r44_count += 1
        expected = mask in forbidden
        observed = bool(matched[mask])
        if observed:
            rejected_under_r44 += 1
        if expected != observed and first_difference is None:
            first_difference = mask
    if first_difference is not None:
        raise AuditError(
            "unsafe/incomplete local reduction at assignment "
            f"0x{first_difference:06X}"
        )
    _require(r44_count, EXPECTED_LOCAL_R44, "local R(4,4) assignment count")
    _require(rejected_under_r44, EXPECTED_RAW_FORBIDDEN, "safe reduced rejection count")
    _require(r44_count - rejected_under_r44, EXPECTED_LOCAL_ALLOWED, "local allowed count")
    return {
        "checked_assignments": limit,
        "r44_assignments": r44_count,
        "raw_forbidden_assignments": len(forbidden),
        "reduced_rejected_assignments_under_r44": rejected_under_r44,
        "allowed_assignments_under_r44": r44_count - rejected_under_r44,
        "reduced_cube_widths": dict(sorted(widths.items())),
        "all_cubes_use_all_seven_vertices": True,
        "exact_modulo_local_r44": True,
    }


def triangle_masks(vertices: Iterable[int]) -> tuple[int, ...]:
    chosen = tuple(vertices)
    return tuple(
        sum(1 << LOCAL_PAIR_INDEX[pair] for pair in itertools.combinations(triple, 2))
        for triple in itertools.combinations(chosen, 3)
    )


def block_targets(forbidden: frozenset[int], neighbour_count: int) -> tuple[int, ...]:
    if not 0 <= neighbour_count <= LOCAL_ORDER:
        raise AuditError("invalid block-neighbour count")
    positive_triangles = triangle_masks(range(neighbour_count))
    negative_triangles = triangle_masks(range(neighbour_count, LOCAL_ORDER))
    return tuple(
        sorted(
            mask
            for mask in forbidden
            if all((mask & triangle) != triangle for triangle in positive_triangles)
            and all((mask & triangle) != 0 for triangle in negative_triangles)
        )
    )


def _cube_completion_hits(cube: Cube, index: Mapping[int, int], full: int) -> tuple[int, ...]:
    ones, fixed = cube
    free = full ^ fixed
    completion = free
    covered: list[int] = []
    while True:
        item = index.get(ones | completion)
        if item is not None:
            covered.append(item)
        if completion == 0:
            break
        completion = (completion - 1) & free
    return tuple(covered)


def build_block_conditioned_cubes(
    forbidden: frozenset[int], cubes: Sequence[Cube]
) -> tuple[tuple[tuple[Cube, ...], ...], dict[str, object]]:
    """Rebuild the root-free block slices from audited universal cubes."""
    full = (1 << LOCAL_EDGE_COUNT) - 1
    cube_set = set(cubes)
    slices: list[tuple[Cube, ...]] = []
    target_counts: list[int] = []
    useful_coverage_counts: list[int] = []
    for neighbour_count in range(LOCAL_ORDER + 1):
        target = block_targets(forbidden, neighbour_count)
        target_counts.append(len(target))
        index = {mask: item for item, mask in enumerate(target)}
        by_coverage: dict[tuple[int, ...], Cube] = {}
        for cube in cubes:
            coverage = _cube_completion_hits(cube, index, full)
            if not coverage:
                continue
            old = by_coverage.get(coverage)
            if old is None or (cube[1].bit_count(), cube[1], cube[0]) < (
                old[1].bit_count(),
                old[1],
                old[0],
            ):
                by_coverage[coverage] = cube
        selected = tuple(
            sorted(by_coverage.values(), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
        )
        _require(
            len(selected),
            EXPECTED_BLOCK_CUBE_COUNTS[neighbour_count],
            f"block-conditioned cube count a={neighbour_count}",
        )
        if any(cube not in cube_set for cube in selected):
            raise AuditError("block conditioning introduced a non-universal cube")
        rejected: set[int] = set()
        for cube in selected:
            for item in _cube_completion_hits(cube, index, full):
                rejected.add(item)
        _require(len(rejected), len(target), f"block-conditioned coverage a={neighbour_count}")
        useful_coverage_counts.append(len(by_coverage))
        slices.append(selected)
    return tuple(slices), {
        "target_forbidden_counts": target_counts,
        "distinct_useful_coverage_sets": useful_coverage_counts,
        "selected_cube_counts": list(map(len, slices)),
        "all_selected_cubes_are_audited_universal_cubes": True,
        "every_block_target_is_covered": True,
    }


def project_nonroot(mask: int) -> int:
    """Project local vertices 1..6 to graph6 positions on vertices 0..5."""
    result = 0
    for target_position, (left, right) in enumerate(SIX_PAIRS):
        source_position = LOCAL_PAIR_INDEX[(left + 1, right + 1)]
        if (mask >> source_position) & 1:
            result |= 1 << target_position
    return result


def build_root_conditioned_cubes(
    forbidden: frozenset[int], cubes: Sequence[Cube]
) -> tuple[tuple[tuple[Cube, ...], ...], dict[str, object]]:
    """Restrict local vertex 0, then deterministically cover each exact slice."""
    root_positions = tuple(LOCAL_PAIR_INDEX[(0, vertex)] for vertex in range(1, LOCAL_ORDER))
    restricted_slices: list[tuple[Cube, ...]] = []
    for neighbour_count in range(LOCAL_ORDER):
        restricted: set[Cube] = set()
        for ones, fixed in cubes:
            consistent = True
            for vertex, position in enumerate(root_positions, 1):
                if (fixed >> position) & 1:
                    actual = vertex <= neighbour_count
                    if bool((ones >> position) & 1) != actual:
                        consistent = False
                        break
            if not consistent:
                continue
            projected_ones = project_nonroot(ones)
            projected_fixed = project_nonroot(fixed)
            restricted.add((projected_ones, projected_fixed))
        ordered = tuple(
            sorted(restricted, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
        )
        _require(
            len(ordered),
            EXPECTED_RESTRICTED_CUBE_COUNTS[neighbour_count],
            f"root-restricted cube count a={neighbour_count}",
        )
        restricted_slices.append(ordered)

    selected_slices: list[tuple[Cube, ...]] = []
    forbidden_counts: list[int] = []
    full6 = (1 << len(SIX_PAIRS)) - 1
    clique_masks = local_k4_masks()
    for neighbour_count, candidates in enumerate(restricted_slices):
        projected = tuple(
            sorted(
                {
                    project_nonroot(mask)
                    for mask in forbidden
                    if all(
                        bool((mask >> position) & 1) == (vertex <= neighbour_count)
                        for vertex, position in enumerate(root_positions, 1)
                    )
                }
            )
        )
        forbidden_counts.append(len(projected))
        index = {mask: item for item, mask in enumerate(projected)}
        covered_candidates: list[tuple[frozenset[int], int, int]] = []
        for ones, fixed in candidates:
            coverage = frozenset(
                index[mask] for mask in projected if (mask & fixed) == ones
            )
            if coverage:
                covered_candidates.append((coverage, ones, fixed))
        active = set(range(len(projected)))
        chosen: list[Cube] = []
        while active:
            coverage, ones, fixed = max(
                covered_candidates,
                key=lambda item: (
                    len(active & item[0]),
                    -item[2].bit_count(),
                    -item[2],
                    -item[1],
                ),
            )
            newly_covered = active & coverage
            if not newly_covered:
                raise AuditError(f"root-conditioned greedy cover stuck at a={neighbour_count}")
            chosen.append((ones, fixed))
            active -= newly_covered
        selected = tuple(
            sorted(set(chosen), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
        )
        _require(
            len(selected),
            EXPECTED_CONDITIONED_CUBE_COUNTS[neighbour_count],
            f"root-conditioned cube count a={neighbour_count}",
        )
        if any(cube not in set(candidates) for cube in selected):
            raise AuditError("root conditioning introduced a cube without a restricted preimage")

        # Exhaustively check all 2^15 completions in this fixed root slice.
        rejected = bytearray(1 << len(SIX_PAIRS))
        for ones, fixed in selected:
            free = full6 ^ fixed
            completion = free
            while True:
                rejected[ones | completion] = 1
                if completion == 0:
                    break
                completion = (completion - 1) & free
        expected_count = 0
        rejected_valid_count = 0
        for mask6 in range(1 << len(SIX_PAIRS)):
            lifted = 0
            for vertex, position in enumerate(root_positions, 1):
                if vertex <= neighbour_count:
                    lifted |= 1 << position
            for position6, (left, right) in enumerate(SIX_PAIRS):
                if (mask6 >> position6) & 1:
                    lifted |= 1 << LOCAL_PAIR_INDEX[(left + 1, right + 1)]
            if not is_local_r44(lifted, clique_masks):
                continue
            expected = lifted in forbidden
            observed = bool(rejected[mask6])
            if expected:
                expected_count += 1
            if observed:
                rejected_valid_count += 1
            if expected != observed:
                raise AuditError(
                    f"root-conditioned slice differs at a={neighbour_count}, mask=0x{mask6:04X}"
                )
        _require(expected_count, len(projected), f"root-conditioned forbidden count a={neighbour_count}")
        _require(rejected_valid_count, expected_count, f"safe conditioned rejection a={neighbour_count}")
        selected_slices.append(selected)

    _require(
        tuple(forbidden_counts),
        EXPECTED_CONDITIONED_FORBIDDEN_COUNTS,
        "root-conditioned forbidden slice counts",
    )
    return tuple(selected_slices), {
        "restricted_cube_counts": list(map(len, restricted_slices)),
        "forbidden_assignment_counts": forbidden_counts,
        "selected_cube_counts": list(map(len, selected_slices)),
        "checked_assignments": LOCAL_ORDER * (1 << len(SIX_PAIRS)),
        "all_selected_cubes_have_audited_restricted_preimages": True,
        "exact_modulo_local_r44_in_every_root_slice": True,
    }


def ramsey_clauses(order: int = ORDER) -> Iterator[Clause]:
    """Generate exactly the two K4 blockers for every four-subset."""
    four_sets = tuple(itertools.combinations(range(order), 4))
    for vertices in four_sets:
        yield tuple(
            NEGATIVE_LITERAL[edge_var(order, left, right)]
            for left, right in itertools.combinations(vertices, 2)
        )
    for vertices in four_sets:
        yield tuple(
            POSITIVE_LITERAL[edge_var(order, left, right)]
            for left, right in itertools.combinations(vertices, 2)
        )


def root_assignment() -> dict[int, bool]:
    return {
        edge_var(ORDER, 0, vertex): vertex <= ROOT_DEGREE
        for vertex in range(1, ORDER)
    }


def second_center_assignment() -> dict[int, bool]:
    """The p=2,q=0 assignment at vertex 1 in the d=8 root slice."""
    assignment = {
        edge_var(ORDER, 1, vertex): vertex <= 3
        for vertex in range(2, 9)
    }
    assignment.update(
        {edge_var(ORDER, 1, vertex): False for vertex in range(9, ORDER)}
    )
    return assignment


def restrict_clause(clause: Sequence[int], assignment: Mapping[int, bool]) -> Clause | None:
    """Restrict a clause while preserving the order of untouched literals."""
    result: list[int] = []
    for literal in clause:
        value = assignment.get(abs(literal))
        if value is None:
            result.append(literal)
        elif value == (literal > 0):
            return None
    return tuple(result)


def canonical_restriction(clause: Sequence[int], assignment: Mapping[int, bool]) -> Clause | None:
    """Restrict, then use the exact final abs/sign literal ordering."""
    simplified = restrict_clause(clause, assignment)
    if simplified is None:
        return None
    return tuple(sorted(simplified, key=lambda literal: (abs(literal), literal < 0)))


def _validate_canonical_clause(clause: Clause, assigned_variables: frozenset[int]) -> None:
    if not clause:
        raise AuditError("an authorized source produced an empty final clause")
    previous = 0
    for literal in clause:
        variable = abs(literal)
        if not 1 <= variable <= VARIABLE_COUNT:
            raise AuditError(f"literal outside 1..{VARIABLE_COUNT}: {literal}")
        if variable <= previous:
            raise AuditError(f"duplicate, tautological, or noncanonical clause: {clause!r}")
        if variable in assigned_variables:
            raise AuditError(f"assigned variable survived simplification: {variable}")
        previous = variable


def subset_variables(vertices: Sequence[int]) -> tuple[int, ...]:
    if len(vertices) != LOCAL_ORDER or tuple(sorted(vertices)) != tuple(vertices):
        raise AuditError("expected seven increasing vertices")
    return tuple(edge_var(ORDER, vertices[left], vertices[right]) for left, right in LOCAL_PAIRS)


def six_subset_variables(vertices: Sequence[int]) -> tuple[int, ...]:
    if len(vertices) != 6 or tuple(sorted(vertices)) != tuple(vertices):
        raise AuditError("expected six increasing vertices")
    return tuple(edge_var(ORDER, vertices[left], vertices[right]) for left, right in SIX_PAIRS)


def blocker_clause(cube: Cube, variables: Sequence[int]) -> Clause:
    ones, fixed = cube
    if ones & ~fixed or fixed >> len(variables):
        raise AuditError("cube is malformed for this variable map")
    return tuple(
        NEGATIVE_LITERAL[variable] if (ones >> position) & 1 else POSITIVE_LITERAL[variable]
        for position, variable in enumerate(variables)
        if (fixed >> position) & 1
    )


def build_root_base_clauses() -> tuple[Clause, ...]:
    source = tuple(ramsey_clauses())
    _require(len(source), EXPECTED_BASE_CLAUSES, "K12 R(4,4) clause count")
    root = root_assignment()
    restricted = tuple(
        simplified
        for clause in source
        if (simplified := restrict_clause(clause, root)) is not None
    )
    if any(not clause for clause in restricted):
        raise AuditError("degree-eight root assignment already contradicts K12 R(4,4)")
    _require(len(restricted), EXPECTED_ROOT_BASE_CLAUSES, "degree-eight base clause count")

    # Derive the same clauses a second way from the neighbour/non-neighbour blocks.
    structural: list[Clause] = []
    for vertices in itertools.combinations(range(1, ORDER), 4):
        edges = tuple(edge_var(ORDER, left, right) for left, right in itertools.combinations(vertices, 2))
        structural.append(tuple(NEGATIVE_LITERAL[edge] for edge in edges))
        structural.append(tuple(POSITIVE_LITERAL[edge] for edge in edges))
    for vertices in itertools.combinations(range(1, ROOT_DEGREE + 1), 3):
        structural.append(
            tuple(
                NEGATIVE_LITERAL[edge_var(ORDER, left, right)]
                for left, right in itertools.combinations(vertices, 2)
            )
        )
    for vertices in itertools.combinations(range(ROOT_DEGREE + 1, ORDER), 3):
        structural.append(
            tuple(
                POSITIVE_LITERAL[edge_var(ORDER, left, right)]
                for left, right in itertools.combinations(vertices, 2)
            )
        )
    _require(set(restricted), set(structural), "root-base structural reconstruction")
    _require(len(set(restricted)), len(restricted), "root-base duplicate check")
    return restricted


def build_final_clause_provenance(
    block_cubes: Sequence[Sequence[Cube]],
    root_cubes: Sequence[Sequence[Cube]],
) -> tuple[dict[Clause, int], dict[str, object]]:
    """Enumerate only authorized sources, restrict them, and record every preimage."""
    second = second_center_assignment()
    root_variables = frozenset(root_assignment())
    second_variables = frozenset(second)
    all_assigned = root_variables | second_variables
    provenance: dict[Clause, int] = {}
    source_counts = Counter()
    satisfied_counts = Counter()
    surviving_counts = Counter()
    false_literal_counts = Counter()

    def emit(source_clause: Clause, family: int) -> None:
        source_counts[family] += 1
        if not source_clause:
            raise AuditError("empty authorized source clause")
        if any(abs(literal) in root_variables for literal in source_clause):
            raise AuditError("root variable survived the degree-eight source construction")
        simplified = canonical_restriction(source_clause, second)
        if simplified is None:
            satisfied_counts[family] += 1
            return
        _validate_canonical_clause(simplified, all_assigned)
        surviving_counts[family] += 1
        false_literal_counts[family] += len(source_clause) - len(simplified)
        provenance[simplified] = provenance.get(simplified, 0) | family

    for clause in build_root_base_clauses():
        emit(clause, FAMILY_BASE)

    block_sets = tuple(set(slice_) for slice_ in block_cubes)
    root_sets = tuple(set(slice_) for slice_ in root_cubes)
    for vertices in itertools.combinations(range(1, ORDER), LOCAL_ORDER):
        neighbour_count = sum(vertex <= ROOT_DEGREE for vertex in vertices)
        variables = subset_variables(vertices)
        for cube in block_cubes[neighbour_count]:
            if cube not in block_sets[neighbour_count]:
                raise AuditError("unrecognized block cube")
            emit(blocker_clause(cube, variables), FAMILY_ROOT_FREE)

    for vertices in itertools.combinations(range(1, ORDER), 6):
        neighbour_count = sum(vertex <= ROOT_DEGREE for vertex in vertices)
        variables = six_subset_variables(vertices)
        for cube in root_cubes[neighbour_count]:
            if cube not in root_sets[neighbour_count]:
                raise AuditError("unrecognized root-conditioned cube")
            emit(blocker_clause(cube, variables), FAMILY_ROOT_CONTAINING)

    expected_source_families = {
        FAMILY_BASE: EXPECTED_ROOT_BASE_CLAUSES,
        FAMILY_ROOT_FREE: EXPECTED_ROOT_FREE_CLAUSES,
        FAMILY_ROOT_CONTAINING: EXPECTED_ROOT_CONTAINING_CLAUSES,
    }
    _require(dict(source_counts), expected_source_families, "authorized source-family counts")
    source_total = sum(source_counts.values())
    satisfied_total = sum(satisfied_counts.values())
    surviving_total = sum(surviving_counts.values())
    false_literals_total = sum(false_literal_counts.values())
    reduction = {
        "source_clauses": source_total,
        "satisfied_clauses_removed": satisfied_total,
        "surviving_before_deduplication": surviving_total,
        "exact_duplicates_removed": surviving_total - len(provenance),
        "false_literals_removed": false_literals_total,
    }
    _require(reduction, EXPECTED_REDUCTION, "p=2,q=0 reduction accounting")
    _require(len(provenance), EXPECTED_FINAL_CLAUSES, "final authorized clause count")
    if any(origin == 0 for origin in provenance.values()):
        raise AuditError("a final clause lacks an authorized source preimage")

    origin_presence = {
        name: sum(1 for origin in provenance.values() if origin & family)
        for family, name in FAMILY_NAMES.items()
    }
    multiple_origins = sum(1 for origin in provenance.values() if origin.bit_count() > 1)
    return provenance, {
        "source_family_counts": {
            FAMILY_NAMES[family]: source_counts[family] for family in FAMILY_NAMES
        },
        "satisfied_by_second_assignment": {
            FAMILY_NAMES[family]: satisfied_counts[family] for family in FAMILY_NAMES
        },
        "surviving_preimages": {
            FAMILY_NAMES[family]: surviving_counts[family] for family in FAMILY_NAMES
        },
        "false_literals_removed": {
            FAMILY_NAMES[family]: false_literal_counts[family] for family in FAMILY_NAMES
        },
        "reduction": reduction,
        "unique_final_clauses_by_origin_presence": origin_presence,
        "unique_final_clauses_with_multiple_origin_families": multiple_origins,
        "every_final_clause_has_an_authorized_preimage": True,
        "no_clause_injection_possible_in_enumeration": True,
    }


def _hash_path(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
            size += len(block)
    return digest.hexdigest().upper(), size


def hash_ordered_formula(
    provenance: Mapping[Clause, int], external_cnf: Path | None = None
) -> dict[str, object]:
    """Hash exact DIMACS bytes in memory and optionally compare an existing file."""
    ordered = sorted(provenance)
    _require(len(ordered), EXPECTED_FINAL_CLAUSES, "ordered final clause count")
    widths = Counter(map(len, ordered))
    _require(dict(sorted(widths.items())), EXPECTED_FINAL_WIDTHS, "final clause widths")

    digest = hashlib.sha256()
    size = 0
    lines = 0
    external_stream = external_cnf.open("rb", buffering=8 * 1024 * 1024) if external_cnf else None
    external_digest = hashlib.sha256() if external_stream else None
    external_size = 0

    def consume(expected: bytes, line_number: int) -> None:
        nonlocal size, lines, external_size
        digest.update(expected)
        size += len(expected)
        lines += 1
        if external_stream is None or external_digest is None:
            return
        observed = external_stream.readline()
        external_digest.update(observed)
        external_size += len(observed)
        if observed != expected:
            raise AuditError(
                f"external CNF differs from authorized reconstruction at line {line_number}"
            )

    try:
        consume(f"p cnf {VARIABLE_COUNT} {len(ordered)}\n".encode("ascii"), 1)
        for line_number, clause in enumerate(ordered, 2):
            if provenance[clause] == 0:
                raise AuditError(f"clause {line_number - 1} has no authorized provenance")
            consume((" ".join(map(str, clause)) + " 0\n").encode("ascii"), line_number)
        if external_stream is not None:
            trailing = external_stream.read(1)
            if trailing:
                if external_digest is not None:
                    external_digest.update(trailing)
                external_size += 1
                raise AuditError("external CNF contains trailing bytes/clauses")
    finally:
        if external_stream is not None:
            external_stream.close()

    reconstructed = {
        "variables": VARIABLE_COUNT,
        "clauses": len(ordered),
        "lines": lines,
        "bytes": size,
        "sha256": digest.hexdigest().upper(),
        "widths": dict(sorted(widths.items())),
    }
    _require(reconstructed["lines"], EXPECTED_FINAL_LINES, "reconstructed line count")
    _require(reconstructed["bytes"], EXPECTED_FINAL_BYTES, "reconstructed byte count")
    _require(reconstructed["sha256"], EXPECTED_FINAL_SHA256, "reconstructed SHA-256")

    external: dict[str, object] | None = None
    if external_cnf is not None and external_digest is not None:
        external = {
            "path": str(external_cnf),
            "bytes": external_size,
            "lines": lines,
            "sha256": external_digest.hexdigest().upper(),
            "byte_for_byte_equal_to_authorized_reconstruction": True,
        }
        _require(external_size, EXPECTED_FINAL_BYTES, "external CNF byte count")
        _require(external["sha256"], EXPECTED_FINAL_SHA256, "external CNF SHA-256")
    return {"reconstructed": reconstructed, "external": external}


def _verify_lrat(path: Path) -> dict[str, object]:
    digest, size = _hash_path(path)
    _require(size, EXPECTED_LRAT_BYTES, "LRAT byte count")
    _require(digest, EXPECTED_LRAT_SHA256, "LRAT SHA-256")
    with path.open("rb") as stream:
        stream.seek(max(0, size - 65_536))
        tail = stream.read()
    nonempty = [line for line in tail.splitlines() if line.strip()]
    if not nonempty:
        raise AuditError("LRAT has no final action")
    tokens = nonempty[-1].split()
    if len(tokens) < 4 or tokens[1] != b"0" or tokens[-1] != b"0":
        raise AuditError("LRAT does not end with an empty-clause addition")
    final_clause_id = int(tokens[0])
    _require(final_clause_id, EXPECTED_LRAT_FINAL_CLAUSE_ID, "LRAT final clause id")
    return {
        "path": str(path),
        "bytes": size,
        "sha256": digest,
        "final_clause_id": final_clause_id,
        "ends_with_empty_clause_addition": True,
    }


def _verify_hashed_artifact(path: Path, expected_sha256: str, label: str) -> dict[str, object]:
    digest, size = _hash_path(path)
    _require(digest, expected_sha256, f"{label} SHA-256")
    return {"path": str(path), "bytes": size, "sha256": digest}


def verify_optional_certificates(
    *,
    lrat: Path | None = None,
    replay_lean: Path | None = None,
    replay_log: Path | None = None,
    replay_json: Path | None = None,
) -> dict[str, object]:
    """Hash optional proof artifacts; this function performs no replay."""
    result: dict[str, object] = {}
    if lrat is not None:
        result["lrat"] = _verify_lrat(lrat)
    if replay_lean is not None:
        lean = _verify_hashed_artifact(replay_lean, EXPECTED_REPLAY_LEAN_SHA256, "Lean source")
        text = replay_lean.read_text(encoding="utf-8")
        if EXPECTED_THEOREM.rsplit(".", 1)[-1] not in text:
            raise AuditError("frozen theorem name is absent from Lean replay source")
        lean["contains_frozen_theorem_name"] = True
        result["replay_lean"] = lean
    if replay_log is not None:
        log = _verify_hashed_artifact(replay_log, EXPECTED_REPLAY_LOG_SHA256, "Lean replay log")
        text = replay_log.read_text(encoding="utf-8", errors="replace")
        if EXPECTED_THEOREM not in text or "lrat_reflect_trim: trimmed" not in text:
            raise AuditError("Lean replay log lacks its success witnesses")
        log["contains_success_witnesses"] = True
        result["replay_log"] = log
    if replay_json is not None:
        report = _verify_hashed_artifact(replay_json, EXPECTED_REPLAY_JSON_SHA256, "Lean replay report")
        payload = json.loads(replay_json.read_text(encoding="utf-8"))
        _require(payload.get("status"), EXPECTED_REPLAY_STATUS, "Lean replay report status")
        _require(payload.get("theorem"), EXPECTED_THEOREM, "Lean replay report theorem")
        inputs = payload.get("inputs", {})
        _require(inputs.get("cnf", {}).get("sha256"), EXPECTED_FINAL_SHA256, "replay input CNF hash")
        _require(inputs.get("lrat", {}).get("sha256"), EXPECTED_LRAT_SHA256, "replay input LRAT hash")
        report["status"] = payload["status"]
        report["theorem"] = payload["theorem"]
        result["replay_json"] = report
    return result


def run_audit(
    *,
    cnf: Path | None = None,
    lrat: Path | None = None,
    replay_lean: Path | None = None,
    replay_log: Path | None = None,
    replay_json: Path | None = None,
    progress: Progress | None = None,
) -> dict[str, object]:
    """Run the complete from-principles audit and return a JSON-ready report."""
    announce = progress or (lambda _message: None)
    announce("building the nine graph6 S7 closures and six cube closures")
    permutations = tuple(itertools.permutations(range(LOCAL_ORDER)))
    _require(len(permutations), math.factorial(LOCAL_ORDER), "S7 size")
    forbidden, raw_orbits = build_raw_forbidden(permutations)
    cubes, reduced_orbits = build_reduced_cubes(permutations)

    announce("checking the local reduction on all 2^21 assignments")
    local = audit_local_reduction(forbidden, cubes)

    announce("rebuilding block-triangle and root-containing conditioned cubes")
    block_cubes, block = build_block_conditioned_cubes(forbidden, cubes)
    conditioned_cubes, conditioned = build_root_conditioned_cubes(forbidden, cubes)

    announce("enumerating the degree-eight source and p=2,q=0 authorized preimages")
    provenance, semantic = build_final_clause_provenance(block_cubes, conditioned_cubes)

    announce("sorting and hashing 758924 clauses without writing a CNF")
    formula = hash_ordered_formula(provenance, cnf)

    announce("checking optional LRAT/replay identities")
    certificates = verify_optional_certificates(
        lrat=lrat,
        replay_lean=replay_lean,
        replay_log=replay_log,
        replay_json=replay_json,
    )
    return {
        "status": "PASS",
        "scope": "independent read-only reconstruction of cover9 d8/p2/q0",
        "implementation": {
            "stdlib_only": True,
            "imports_project_generators": False,
            "writes_cnf_or_proof_artifacts": False,
            "uses_sat_solver": False,
            "permutation_group_size": len(permutations),
        },
        "cover9": {
            "records": list(COVER_RECORDS),
            "raw_orbit_counts": list(raw_orbits),
            "raw_labelled_union": len(forbidden),
            "reduced_representatives": [
                {"ones": f"0x{ones:X}", "fixed": f"0x{fixed:X}"}
                for ones, fixed in REDUCED_CUBE_REPRESENTATIVES
            ],
            "reduced_orbit_counts": list(reduced_orbits),
            "reduced_cube_union": len(cubes),
        },
        "local_reduction": local,
        "degree_eight_root": {
            "root_assignment": [
                variable if value else -variable
                for variable, value in root_assignment().items()
            ],
            "base_r44_clauses_before_restriction": EXPECTED_BASE_CLAUSES,
            "base_r44_clauses_after_restriction": EXPECTED_ROOT_BASE_CLAUSES,
            "block_conditioning": block,
            "root_containing_conditioning": conditioned,
            "source_clause_count": EXPECTED_ROOT_SOURCE_CLAUSES,
        },
        "second_center": {
            "p": 2,
            "q": 0,
            "assignment": [
                variable if value else -variable
                for variable, value in second_center_assignment().items()
            ],
            "semantic_authorization": semantic,
        },
        "formula": formula,
        "certificates": certificates,
        "conclusion": (
            "Every reconstructed final clause has at least one audited semantic "
            "preimage; its exact ordered DIMACS stream has the frozen clause count, "
            "byte count, and SHA-256.  Any supplied CNF was also compared line by line."
        ),
    }


def _environment_path(name: str) -> Path | None:
    value = os.environ.get(name)
    return Path(value) if value else None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cnf", type=Path, default=_environment_path("R45_D12_P2Q0_CNF"))
    parser.add_argument("--lrat", type=Path, default=_environment_path("R45_D12_P2Q0_LRAT"))
    parser.add_argument(
        "--replay-lean",
        type=Path,
        default=_environment_path("R45_D12_P2Q0_REPLAY_LEAN"),
    )
    parser.add_argument(
        "--replay-log",
        type=Path,
        default=_environment_path("R45_D12_P2Q0_REPLAY_LOG"),
    )
    parser.add_argument(
        "--replay-json",
        type=Path,
        default=_environment_path("R45_D12_P2Q0_REPLAY_JSON"),
    )
    args = parser.parse_args()
    report = run_audit(
        cnf=args.cnf,
        lrat=args.lrat,
        replay_lean=args.replay_lean,
        replay_log=args.replay_log,
        replay_json=args.replay_json,
        progress=lambda message: print(f"[p2q0-audit] {message}", file=sys.stderr, flush=True),
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
