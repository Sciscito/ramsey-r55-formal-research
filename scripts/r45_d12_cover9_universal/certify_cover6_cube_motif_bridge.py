#!/usr/bin/env python3
"""Certify a compact semantic bridge from cover6 cubes to six motifs.

This program is a deterministic analysis layer over ``exact_replay_cover6_d8``.
It shows that a 25,200-row cube-to-motif table is unnecessary: each of the six
partial cube representatives has one and only one R(4,4)-valid completion, and
the S7 action transports these six witnesses bijectively to all labelled cubes
and all labelled cover6 motifs.

It also checks blocker polarity, the common 21-pair ordering, root-free block
conditioning, and root-containing projection/simplification.  It writes no
artifact and invokes no SAT, LRAT, or Lean process.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

from . import exact_replay_cover6_d8 as replay


REPORT_NAME = "COVER6_CUBE_MOTIF_BRIDGE_V1.json"
PAIR_ORDER = tuple(
    (left, right)
    for right in range(1, replay.LOCAL_ORDER)
    for left in range(right)
)
CUBE_COMPLEMENT_PAIRS = ((0, 1), (2, 3), (4, 5))
Cube = replay.Cube
Clause = replay.Clause


class BridgeError(ValueError):
    """Raised when one of the compact bridge obligations changes."""


def digest_text(lines: Iterable[str]) -> str:
    return hashlib.sha256("".join(lines).encode("ascii")).hexdigest().upper()


def pair_order_sha256() -> str:
    return digest_text(f"{left},{right}\n" for left, right in PAIR_ORDER)


def permutations_and_maps() -> tuple[
    tuple[tuple[int, ...], tuple[int, ...]], ...
]:
    permutations = tuple(itertools.permutations(range(replay.LOCAL_ORDER)))
    maps = replay.permutation_maps()
    if len(permutations) != len(maps):
        raise BridgeError("S7 permutation/map enumeration length mismatch")
    return tuple(zip(permutations, maps))


def motif_data() -> tuple[
    tuple[int, ...], tuple[frozenset[int], ...], dict[int, int]
]:
    raw = tuple(replay.decode_graph6(record) for record in replay.read_cover_records())
    orbits = tuple(replay.graph_orbit(mask) for mask in raw)
    owner: dict[int, int] = {}
    for index, orbit in enumerate(orbits):
        for mask in orbit:
            if mask in owner:
                raise BridgeError("motif orbits overlap")
            owner[mask] = index
    if set(owner) != set(replay.forbidden_masks()):
        raise BridgeError("motif owner map differs from frozen forbidden masks")
    return raw, orbits, owner


def cube_data() -> tuple[tuple[frozenset[Cube], ...], dict[Cube, int]]:
    orbits = tuple(replay.cube_orbit(cube) for cube in replay.CUBE_REPRESENTATIVES)
    owner: dict[Cube, int] = {}
    for index, orbit in enumerate(orbits):
        for cube in orbit:
            if cube in owner:
                raise BridgeError("cube representative orbits overlap")
            owner[cube] = index
    if set(owner) != set(replay.reduced_cubes()):
        raise BridgeError("cube owner map differs from frozen reduced cubes")
    return orbits, owner


def first_isomorphism(source_mask: int, target_mask: int) -> tuple[int, ...]:
    for permutation, mapping in permutations_and_maps():
        if replay.transform(source_mask, mapping) == target_mask:
            return permutation
    raise BridgeError("no S7 isomorphism found between motif and forced completion")


def representative_certificate() -> tuple[
    list[dict[str, object]], dict[Cube, tuple[int, int]], str
]:
    valid = replay.r44_flags()
    raw_motifs, motif_orbits, motif_owner = motif_data()
    cube_orbits, _cube_owner = cube_data()
    rows = []
    implied: dict[Cube, tuple[int, int]] = {}
    forced_masks: list[int] = []
    for index, cube in enumerate(replay.CUBE_REPRESENTATIVES):
        completions = tuple(mask for mask in replay.completions(cube) if valid[mask])
        if len(completions) != 1:
            raise BridgeError(
                f"representative {index} has {len(completions)} R44 completions, expected one"
            )
        forced = completions[0]
        motif_index = motif_owner.get(forced)
        if motif_index is None:
            raise BridgeError(f"representative {index} forces a non-cover6 graph")
        permutation = first_isomorphism(raw_motifs[motif_index], forced)
        forced_masks.append(forced)
        rows.append({
            "representative_index": index,
            "ones_hex": f"{cube[0]:06X}",
            "fixed_hex": f"{cube[1]:06X}",
            "width": cube[1].bit_count(),
            "all_completions": 1 << (replay.LOCAL_EDGES - cube[1].bit_count()),
            "r44_completions": 1,
            "forced_mask_hex": f"{forced:06X}",
            "motif_index": motif_index,
            "motif_graph6": replay.COVER_RECORDS[motif_index],
            "motif_to_forced_target_to_source_permutation": list(permutation),
            "cube_orbit_size": len(cube_orbits[index]),
            "motif_orbit_size": len(motif_orbits[motif_index]),
        })

    for index, (cube, forced) in enumerate(zip(replay.CUBE_REPRESENTATIVES, forced_masks)):
        for _permutation, mapping in permutations_and_maps():
            transformed_cube = (
                replay.transform(cube[0], mapping),
                replay.transform(cube[1], mapping),
            )
            transformed_mask = replay.transform(forced, mapping)
            if transformed_mask & transformed_cube[1] != transformed_cube[0]:
                raise BridgeError("S7 transport broke cube matching")
            if not valid[transformed_mask]:
                raise BridgeError("S7 transport broke R44 validity")
            if motif_owner.get(transformed_mask) != rows[index]["motif_index"]:
                raise BridgeError("S7 transport changed motif isomorphism class")
            previous = implied.get(transformed_cube)
            value = transformed_mask, index
            if previous is not None and previous != value:
                raise BridgeError("one labelled cube implies two different R44 completions")
            implied[transformed_cube] = value

    if len(implied) != replay.CUBE_COUNT:
        raise BridgeError(f"implied labelled map has {len(implied)} rows")
    if {mask for mask, _index in implied.values()} != set(replay.forbidden_masks()):
        raise BridgeError("implied cube-to-mask map is not exactly the cover6 closure")
    if len({mask for mask, _index in implied.values()}) != len(implied):
        raise BridgeError("implied cube-to-mask map is not bijective")
    digest = digest_text(
        f"{ones:06X}\t{fixed:06X}\t{mask:06X}\t{index}\n"
        for (ones, fixed), (mask, index) in sorted(
            implied.items(), key=lambda item: (item[0][1], item[0][0])
        )
    )
    return rows, implied, digest


def complement_witnesses(
    representative_rows: Sequence[dict[str, object]],
) -> list[dict[str, object]]:
    valid = replay.r44_flags()
    if any(
        bool(valid[mask]) != bool(valid[replay.LOCAL_FULL ^ mask])
        for mask in range(1 << replay.LOCAL_EDGES)
    ):
        raise BridgeError("R44 validity is not complement-invariant")
    if {
        replay.LOCAL_FULL ^ mask for mask in replay.forbidden_masks()
    } != set(replay.forbidden_masks()):
        raise BridgeError("cover6 motif closure is not complement-invariant")
    rows = []
    forced = tuple(int(str(row["forced_mask_hex"]), 16) for row in representative_rows)
    for source, target in CUBE_COMPLEMENT_PAIRS:
        ones, fixed = replay.CUBE_REPRESENTATIVES[source]
        complemented = fixed ^ ones, fixed
        witnesses = []
        for permutation, mapping in permutations_and_maps():
            transformed = (
                replay.transform(complemented[0], mapping),
                replay.transform(complemented[1], mapping),
            )
            if transformed == replay.CUBE_REPRESENTATIVES[target]:
                witnesses.append((permutation, mapping))
        if not witnesses:
            raise BridgeError(f"no complement witness for representatives {source}/{target}")
        permutation, mapping = witnesses[0]
        transformed_completion = replay.transform(replay.LOCAL_FULL ^ forced[source], mapping)
        if transformed_completion != forced[target]:
            raise BridgeError("cube complement witness does not transport its forced completion")
        rows.append({
            "source_representative": source,
            "target_representative": target,
            "target_to_source_permutation": list(permutation),
            "witness_count": len(witnesses),
            "forced_completion_transport": "PASS",
        })
    return rows


def cube_matches(mask: int, cube: Cube) -> bool:
    ones, fixed = cube
    return mask & fixed == ones


def edge_index(order: int, left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < order:
        raise BridgeError(f"not an edge of K{order}")
    return right * (right - 1) // 2 + left


def transform_order(mask: int, permutation: Sequence[int], order: int) -> int:
    result = 0
    target = 0
    for right in range(1, order):
        for left in range(right):
            source = edge_index(order, permutation[left], permutation[right])
            result |= ((mask >> source) & 1) << target
            target += 1
    return result


def transform_cube_order(cube: Cube, permutation: Sequence[int], order: int) -> Cube:
    return (
        transform_order(cube[0], permutation, order),
        transform_order(cube[1], permutation, order),
    )


def block_stabilizer(order: int, prefix_size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        left + right
        for left in itertools.permutations(range(prefix_size))
        for right in itertools.permutations(range(prefix_size, order))
    )


def stabilizer_orbit_profile(
    cubes: Sequence[Cube], order: int, prefix_size: int
) -> tuple[dict[str, object], tuple[Cube, ...]]:
    selected = set(cubes)
    remaining = set(selected)
    permutations = block_stabilizer(order, prefix_size)
    representatives = []
    orbit_sizes = Counter()
    while remaining:
        representative = min(remaining, key=lambda cube: (cube[1], cube[0]))
        orbit = {
            transform_cube_order(representative, permutation, order)
            for permutation in permutations
        }
        if not orbit <= selected:
            raise BridgeError(
                f"conditioned cubes are not closed under the block stabilizer a={prefix_size}"
            )
        representatives.append(representative)
        orbit_sizes[len(orbit)] += 1
        remaining -= orbit
    ordered = tuple(representatives)
    return {
        "stabilizer_size": len(permutations),
        "stabilizer_orbit_representatives": len(ordered),
        "orbit_size_counts": {
            str(size): count for size, count in sorted(orbit_sizes.items())
        },
        "representative_sha256": replay.cubes_digest(ordered),
    }, ordered


def clause_eval(mask: int, clause: Clause) -> bool:
    return any(
        bool((mask >> (abs(literal) - 1)) & 1) == (literal > 0)
        for literal in clause
    )


def polarity_report() -> dict[str, object]:
    blockers = []
    for index, cube in enumerate(replay.CUBE_REPRESENTATIVES):
        clause = replay.instantiate(cube, tuple(range(1, replay.LOCAL_EDGES + 1)))
        expected = tuple(
            -(position + 1) if (cube[0] >> position) & 1 else position + 1
            for position in range(replay.LOCAL_EDGES)
            if (cube[1] >> position) & 1
        )
        if clause != expected:
            raise BridgeError(f"representative {index} blocker polarity changed")
        matching = tuple(replay.completions(cube))
        if any(clause_eval(mask, clause) or not cube_matches(mask, cube) for mask in matching):
            raise BridgeError("a matching assignment does not falsify its blocker")
        forced = next(mask for mask in matching if replay.r44_flags()[mask])
        for position in range(replay.LOCAL_EDGES):
            if (cube[1] >> position) & 1:
                mutated = forced ^ (1 << position)
                if not clause_eval(mutated, clause) or cube_matches(mutated, cube):
                    raise BridgeError("a fixed-bit mutation is not detected by its blocker")
        blockers.append(clause)
    return {
        "meaning_of_one_bit": "edge present",
        "cube_match": "assignment & fixed == ones",
        "blocker_literal": "fixed one -> negative DIMACS; fixed zero -> positive DIMACS",
        "blocker_false_iff_cube_matches": True,
        "representative_blocker_sha256": digest_text(
            " ".join(map(str, clause)) + " 0\n" for clause in blockers
        ),
    }


def block_compatible(mask: int, neighbour_count: int) -> bool:
    positive = replay.triangle_masks(range(neighbour_count))
    negative = replay.triangle_masks(range(neighbour_count, replay.LOCAL_ORDER))
    return (
        all((mask & triangle) != triangle for triangle in positive)
        and all((mask & triangle) != 0 for triangle in negative)
    )


def root_free_report(cube_owner: dict[Cube, int]) -> tuple[list[dict[str, object]], int]:
    valid = replay.r44_flags()
    motifs = replay.forbidden_masks()
    rows = []
    for neighbour_count, selected in enumerate(replay.block_conditioned_cubes()):
        if any(cube not in cube_owner for cube in selected):
            raise BridgeError("root-free conditioning introduced a non-orbit cube")
        target = {mask for mask in motifs if block_compatible(mask, neighbour_count)}
        covered = set()
        for cube in selected:
            for mask in replay.completions(cube):
                if valid[mask] and block_compatible(mask, neighbour_count):
                    covered.add(mask)
        if covered != target:
            raise BridgeError(f"root-free conditioned semantics failed at a={neighbour_count}")
        provenance = Counter(cube_owner[cube] for cube in selected)
        stabilizer, _representatives = stabilizer_orbit_profile(
            selected, replay.LOCAL_ORDER, neighbour_count
        )
        rows.append({
            "root_neighbours_in_seven_set": neighbour_count,
            "selected_cubes": len(selected),
            "target_motif_masks": len(target),
            "covered_r44_compatible_masks": len(covered),
            "exact_under_r44_and_root_constraints": True,
            "all_selected_cubes_have_six_orbit_provenance": True,
            "representative_provenance_counts": {
                str(index): provenance.get(index, 0) for index in range(6)
            },
            "selected_cube_sha256": replay.cubes_digest(selected),
            **stabilizer,
        })
    clauses = sum(
        math.comb(replay.DEGREE, count)
        * math.comb(11 - replay.DEGREE, 7 - count)
        * len(replay.block_conditioned_cubes()[count])
        for count in range(8)
        if count <= replay.DEGREE and 7 - count <= 11 - replay.DEGREE
    )
    return rows, clauses


def full_mask_from_projected(projected: int, neighbour_count: int) -> int:
    mask = 0
    for vertex in range(1, 7):
        if vertex <= neighbour_count:
            mask |= 1 << replay.local_edge(0, vertex)
    for right in range(2, 7):
        for left in range(1, right):
            if (projected >> replay.local_edge(left - 1, right - 1)) & 1:
                mask |= 1 << replay.local_edge(left, right)
    return mask


def projected_completions(cube: Cube) -> Iterable[int]:
    ones, fixed = cube
    full = (1 << 15) - 1
    remaining = full ^ fixed
    while True:
        yield ones | remaining
        if remaining == 0:
            break
        remaining = (remaining - 1) & (full ^ fixed)


def compatible_with_root(cube: Cube, neighbour_count: int) -> bool:
    ones, fixed = cube
    return all(
        not ((fixed >> replay.local_edge(0, vertex)) & 1)
        or bool((ones >> replay.local_edge(0, vertex)) & 1)
        == (vertex <= neighbour_count)
        for vertex in range(1, 7)
    )


def root_containing_lifts(
    cube_owner: dict[Cube, int], neighbour_count: int
) -> dict[Cube, tuple[Cube, ...]]:
    lifts: dict[Cube, list[Cube]] = defaultdict(list)
    for cube in replay.reduced_cubes():
        if compatible_with_root(cube, neighbour_count):
            projected = replay.project_nonroot(cube[0]), replay.project_nonroot(cube[1])
            lifts[projected].append(cube)
    result = {
        projected: tuple(sorted(items, key=lambda cube: (cube[1], cube[0])))
        for projected, items in lifts.items()
    }
    selected = replay.local_conditioned_cubes()[neighbour_count]
    if any(cube not in result for cube in selected):
        raise BridgeError("root-containing projected cube lacks a compatible full lift")
    if any(len({cube_owner[lift] for lift in result[cube]}) != 1 for cube in selected):
        raise BridgeError("root-containing projected cube has ambiguous representative provenance")
    return result


def verify_global_pair_maps() -> None:
    if PAIR_ORDER != tuple(
        (left, right) for right in range(1, 7) for left in range(right)
    ):
        raise BridgeError("local 21-pair order changed")
    for vertices in itertools.combinations(range(1, 12), 7):
        observed = replay.subset_variables(vertices)
        expected = tuple(
            replay.global_edge(vertices[left], vertices[right])
            for left, right in PAIR_ORDER
        )
        if observed != expected:
            raise BridgeError("root-free local/global pair map changed")
    pairs6 = tuple((left, right) for right in range(1, 6) for left in range(right))
    for vertices in itertools.combinations(range(1, 12), 6):
        observed = replay.subset_variables(vertices)
        expected = tuple(
            replay.global_edge(vertices[left], vertices[right])
            for left, right in pairs6
        )
        if observed != expected:
            raise BridgeError("root-containing projected pair map changed")


def root_containing_report(
    cube_owner: dict[Cube, int]
) -> tuple[list[dict[str, object]], int, int]:
    valid = replay.r44_flags()
    motifs = replay.forbidden_masks()
    selected_by_count = replay.local_conditioned_cubes()
    rows = []
    canonical_lifts: list[dict[Cube, Cube]] = []
    for neighbour_count, selected in enumerate(selected_by_count):
        lifts = root_containing_lifts(cube_owner, neighbour_count)
        canonical_lifts.append({cube: lifts[cube][0] for cube in selected})
        covered = set().union(*(set(projected_completions(cube)) for cube in selected)) if selected else set()
        r44_slice = 0
        motif_slice = set()
        for projected in range(1 << 15):
            full = full_mask_from_projected(projected, neighbour_count)
            if not valid[full]:
                continue
            r44_slice += 1
            is_motif = full in motifs
            if is_motif:
                motif_slice.add(projected)
            if (projected in covered) != is_motif:
                raise BridgeError(
                    f"root-containing projected semantics failed at a={neighbour_count}"
                )
        provenance = Counter(
            cube_owner[canonical_lifts[-1][cube]] for cube in selected
        )
        lift_multiplicities = Counter(len(lifts[cube]) for cube in selected)
        stabilizer, orbit_representatives = stabilizer_orbit_profile(
            selected, 6, neighbour_count
        )
        full_stabilizer = tuple(
            (0, *(vertex + 1 for vertex in permutation))
            for permutation in block_stabilizer(6, neighbour_count)
        )
        for projected_representative in orbit_representatives:
            full_representative = canonical_lifts[-1][projected_representative]
            for projected_permutation, full_permutation in zip(
                block_stabilizer(6, neighbour_count), full_stabilizer
            ):
                projected_image = transform_cube_order(
                    projected_representative, projected_permutation, 6
                )
                full_image = transform_cube_order(
                    full_representative, full_permutation, 7
                )
                if projected_image not in canonical_lifts[-1]:
                    raise BridgeError("projected stabilizer orbit left the selected set")
                if canonical_lifts[-1][projected_image] != full_image:
                    raise BridgeError("canonical full lift is not stabilizer-equivariant")
        lift_witness_sha256 = digest_text(
            f"{neighbour_count}\t{cube[0]:06X}\t{cube[1]:06X}\t"
            f"{canonical_lifts[-1][cube][0]:06X}\t"
            f"{canonical_lifts[-1][cube][1]:06X}\t"
            f"{cube_owner[canonical_lifts[-1][cube]]}\n"
            for cube in orbit_representatives
        )
        rows.append({
            "root_neighbours_among_six_vertices": neighbour_count,
            "selected_projected_cubes": len(selected),
            "r44_assignments_in_root_slice": r44_slice,
            "target_projected_motif_masks": len(motif_slice),
            "all_projected_cubes_have_compatible_full_lifts": True,
            "unique_representative_provenance": True,
            "full_lift_multiplicity_counts": {
                str(count): amount for count, amount in sorted(lift_multiplicities.items())
            },
            "representative_provenance_counts": {
                str(index): provenance.get(index, 0) for index in range(6)
            },
            "exact_under_r44_and_fixed_root_edges": True,
            "selected_cube_sha256": replay.cubes_digest(selected),
            "orbit_representative_lift_sha256": lift_witness_sha256,
            **stabilizer,
        })

    root_assignment = {
        replay.global_edge(0, vertex): vertex <= replay.DEGREE
        for vertex in range(1, 12)
    }
    checked_clauses = 0
    for vertices in itertools.combinations(range(1, 12), 6):
        neighbour_count = sum(vertex <= replay.DEGREE for vertex in vertices)
        full_variables = replay.subset_variables((0, *vertices))
        projected_variables = replay.subset_variables(vertices)
        for projected_cube in selected_by_count[neighbour_count]:
            full_cube = canonical_lifts[neighbour_count][projected_cube]
            full_clause = replay.instantiate(full_cube, full_variables)
            simplified = replay.simplify_clause(full_clause, root_assignment)
            projected_clause = replay.instantiate(projected_cube, projected_variables)
            if simplified != projected_clause:
                raise BridgeError("root-containing projection does not equal root simplification")
            checked_clauses += 1
    expected_clauses = sum(
        math.comb(replay.DEGREE, count)
        * math.comb(11 - replay.DEGREE, 6 - count)
        * len(selected_by_count[count])
        for count in range(7)
        if count <= replay.DEGREE and 6 - count <= 11 - replay.DEGREE
    )
    if checked_clauses != expected_clauses:
        raise BridgeError("root-containing global clause count changed")
    return rows, expected_clauses, checked_clauses


def build_report() -> dict[str, object]:
    if len(PAIR_ORDER) != replay.LOCAL_EDGES:
        raise BridgeError("pair order does not contain 21 edges")
    verify_global_pair_maps()
    representative_rows, implied, implied_sha256 = representative_certificate()
    _cube_orbits, cube_owner = cube_data()
    complement = complement_witnesses(representative_rows)
    root_free, root_free_clauses = root_free_report(cube_owner)
    root_containing, root_containing_clauses, checked_simplifications = (
        root_containing_report(cube_owner)
    )
    if root_free_clauses != 3_210_480 or root_containing_clauses != 156_240:
        raise BridgeError("conditioned global clause totals changed")
    compact_representatives = []
    for row in representative_rows:
        if row["cube_orbit_size"] != row["motif_orbit_size"]:
            raise BridgeError("representative cube and motif orbit sizes differ")
        compact_representatives.append({
            "index": row["representative_index"],
            "ones_hex": row["ones_hex"],
            "fixed_hex": row["fixed_hex"],
            "width": row["width"],
            "all_completions": row["all_completions"],
            "r44_completions": row["r44_completions"],
            "forced_mask_hex": row["forced_mask_hex"],
            "motif_index": row["motif_index"],
            "motif_graph6": row["motif_graph6"],
            "target_to_source_permutation": row[
                "motif_to_forced_target_to_source_permutation"
            ],
            "cube_and_motif_orbit_size": row["cube_orbit_size"],
        })
    compact_complement = [
        {
            "source": row["source_representative"],
            "target": row["target_representative"],
            "permutation": row["target_to_source_permutation"],
        }
        for row in complement
    ]
    return {
        "schema_version": 1,
        "status": "PASS_COMPACT_CUBE_MOTIF_BRIDGE",
        "scope": (
            "Finite cube/motif and conditioning semantics only; no SAT, LRAT, "
            "parsed-DIMACS equality, Lean replay, or cover6-d8 theorem."
        ),
        "implementation": {
            "name": Path(__file__).name,
            "relation_to_exact_replay": (
                "Deterministic analysis layer importing exact_replay_cover6_d8; "
                "not a low-common-mode independent implementation."
            ),
        },
        "pair_order": {
            "convention": "column-wise upper triangle: right outer, left inner",
            "count": len(PAIR_ORDER),
            "sha256": pair_order_sha256(),
            "graph6_mask_order": "PASS",
            "cube_mask_order": "PASS",
            "root_free_global_variable_map": "PASS",
            "root_containing_projected_variable_map": "PASS",
        },
        "polarity": polarity_report(),
        "representatives": compact_representatives,
        "s7_transport": {
            "action_convention": (
                "target edge (u,v) receives the source bit at (perm[u],perm[v])"
            ),
            "permutations": math.factorial(replay.LOCAL_ORDER),
            "implied_cube_to_motif_rows": len(implied),
            "implied_distinct_motif_masks": len({value[0] for value in implied.values()}),
            "bijection": True,
            "implied_mapping_sha256": implied_sha256,
        },
        "complement_reduction": {
            "three_representatives_are_logically_sufficient": True,
            "witnesses": compact_complement,
            "recommendation": (
                "Keep six rows in Lean: three saved finite checks do not justify adding "
                "complement-invariance dependencies to the semantic core."
            ),
        },
        "root_free_conditioning": {
            "neighbour_counts": [
                row["root_neighbours_in_seven_set"] for row in root_free
            ],
            "selected_cubes": [row["selected_cubes"] for row in root_free],
            "target_motif_masks": [row["target_motif_masks"] for row in root_free],
            "selected_cube_sha256": [
                row["selected_cube_sha256"] for row in root_free
            ],
            "all_selected_cubes_have_six_orbit_provenance": all(
                row["all_selected_cubes_have_six_orbit_provenance"]
                for row in root_free
            ),
            "exact_under_r44_and_root_constraints": all(
                row["exact_under_r44_and_root_constraints"] for row in root_free
            ),
            "stabilizer_sizes": [row["stabilizer_size"] for row in root_free],
            "stabilizer_orbit_representatives": [
                row["stabilizer_orbit_representatives"] for row in root_free
            ],
            "stabilizer_representative_sha256": [
                row["representative_sha256"] for row in root_free
            ],
            "global_clauses": root_free_clauses,
            "total_stabilizer_orbit_representatives": sum(
                row["stabilizer_orbit_representatives"] for row in root_free
            ),
            "certificate_need": (
                "No extra cube-to-motif table; every selected cube is already in one "
                "of the six S7 orbits."
            ),
        },
        "root_containing_conditioning": {
            "root_neighbours_among_six_vertices": [
                row["root_neighbours_among_six_vertices"]
                for row in root_containing
            ],
            "selected_projected_cubes": [
                row["selected_projected_cubes"] for row in root_containing
            ],
            "r44_assignments_in_root_slice": [
                row["r44_assignments_in_root_slice"] for row in root_containing
            ],
            "target_projected_motif_masks": [
                row["target_projected_motif_masks"] for row in root_containing
            ],
            "selected_cube_sha256": [
                row["selected_cube_sha256"] for row in root_containing
            ],
            "all_1860_projected_cubes_have_unique_full_lifts": all(
                row["all_projected_cubes_have_compatible_full_lifts"]
                for row in root_containing
            ),
            "unique_representative_provenance": all(
                row["unique_representative_provenance"]
                for row in root_containing
            ),
            "exact_under_r44_and_fixed_root_edges": all(
                row["exact_under_r44_and_fixed_root_edges"]
                for row in root_containing
            ),
            "stabilizer_sizes": [
                row["stabilizer_size"] for row in root_containing
            ],
            "stabilizer_orbit_representatives": [
                row["stabilizer_orbit_representatives"]
                for row in root_containing
            ],
            "stabilizer_representative_sha256": [
                row["representative_sha256"] for row in root_containing
            ],
            "orbit_representative_lift_sha256": [
                row["orbit_representative_lift_sha256"]
                for row in root_containing
            ],
            "global_clauses": root_containing_clauses,
            "global_projection_simplifications_checked": checked_simplifications,
            "total_stabilizer_orbit_representatives": sum(
                row["stabilizer_orbit_representatives"] for row in root_containing
            ),
            "certificate_need": (
                "Derive projected cubes as projections of compatible orbit cubes, or "
                "materialize 38 stabilizer-orbit representatives with equivariant full "
                "lifts; neither 1,860 lift rows nor a 25,200-row cube-to-motif table is needed."
            ),
        },
        "minimal_lean_certificate": {
            "recommended_data_rows": 6,
            "row_fields": [
                "ones", "fixed", "forcedMask", "motifIndex", "motifIsomorphismPermutation"
            ],
            "generic_lemmas": [
                "partial blocker eval_false iff cubeMatches",
                "R44 and representative cubeMatches imply equality to forcedMask",
                "R44, cubeMatches, and motif membership are invariant under S7 relabelling",
                "six representative S7 orbits give a bijection between 25,200 cubes and motifs",
                "compatible full-cube blocker simplifies to its projected root-containing blocker",
            ],
            "suggested_terminal_local_theorem": (
                "isR44Mask mask -> ((exists cube in reducedCubeOrbits, cubeMatches mask cube) "
                "<-> (exists motif in cover6Motifs, IsomorphicMask mask motif))"
            ),
            "table_of_25200_cube_to_motif_rows_required": False,
            "optional_conditioning_rows_if_python_selection_is_not_reimplemented": {
                "root_free_stabilizer_orbit_representatives": 334,
                "root_containing_projected_orbit_representatives_with_lifts": 38,
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", default="check", choices=("check",))
    parser.parse_args()
    print(json.dumps(build_report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
