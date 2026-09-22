#!/usr/bin/env python3
"""Generate canonical degree branches for the complement-closed cover5 family.

The local target is the eight-isomorphism-class complement closure audited by
``generate_complement_closed_cover5``.  Because the target is invariant under
color complementation, a future universal proof only needs root degrees 6, 7,
and 8; degrees 5, 4, and 3 are their complements.

Generation is deterministic and large outputs are restricted to ``S:``.  This
module invokes no SAT solver and claims no UNSAT result.
"""

from __future__ import annotations

import argparse
import functools
import itertools
import json
import math
import os
from collections import Counter
from pathlib import Path

from . import generate_complement_closed_cover5 as local
from . import generate_degree_branch as degree_branch
from . import generate_universal as universal


DEGREES = (6, 7, 8)
BLOCK_CONDITIONED_COUNTS = (2_520, 4_320, 9_240, 13_104, 13_104, 9_240, 4_320, 2_520)
LOCAL_CONDITIONED_COUNTS = (0, 180, 384, 468, 384, 180, 0)
EXPECTED_CLAUSE_COUNTS = {
    6: 4_177_770,
    7: 3_750_963,
    8: 2_990_445,
}

Cube = tuple[int, int]
Clause = tuple[int, ...]


@functools.cache
def forbidden_masks() -> frozenset[int]:
    closure = local.complement_closure()["closed"]
    if not isinstance(closure, frozenset) or len(closure) != local.EXPECTED_COMPLEMENT_CLOSURE:
        raise RuntimeError("complement-closed target changed")
    return closure


@functools.cache
def reduced_cubes() -> tuple[Cube, ...]:
    cubes = frozenset().union(
        *(local.cube_orbit(cube) for cube in local.CUBE_REPRESENTATIVES)
    )
    if len(cubes) != local.EXPECTED_CUBES:
        raise RuntimeError("complement-closed cube family changed")
    if {(fixed ^ ones, fixed) for ones, fixed in cubes} != cubes:
        raise RuntimeError("cube family is not closed under complementation")
    return tuple(sorted(cubes, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))


def triangle_masks(vertices: range) -> tuple[int, ...]:
    return tuple(
        sum(
            1 << universal.edge_position(left, right)
            for left, right in itertools.combinations(triple, 2)
        )
        for triple in itertools.combinations(vertices, 3)
    )


def block_forbidden_masks(neighbour_count: int) -> tuple[int, ...]:
    if not 0 <= neighbour_count <= 7:
        raise ValueError("local block size must lie in 0..7")
    positive_triangles = triangle_masks(range(neighbour_count))
    negative_triangles = triangle_masks(range(neighbour_count, 7))
    return tuple(
        sorted(
            mask
            for mask in forbidden_masks()
            if all((mask & triangle) != triangle for triangle in positive_triangles)
            and all((mask & triangle) != 0 for triangle in negative_triangles)
        )
    )


@functools.cache
def block_conditioned_cubes() -> tuple[tuple[Cube, ...], ...]:
    """Keep one safe cube for each distinct useful local coverage set."""
    full = (1 << universal.LOCAL_VARIABLE_COUNT) - 1
    result: list[tuple[Cube, ...]] = []
    for neighbour_count in range(8):
        target = block_forbidden_masks(neighbour_count)
        index = {mask: item for item, mask in enumerate(target)}
        by_coverage: dict[tuple[int, ...], Cube] = {}
        for ones, fixed in reduced_cubes():
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
            if not covered:
                continue
            coverage = tuple(covered)
            previous = by_coverage.get(coverage)
            if previous is None or (fixed.bit_count(), fixed, ones) < (
                previous[1].bit_count(),
                previous[1],
                previous[0],
            ):
                by_coverage[coverage] = (ones, fixed)
        selected = tuple(
            sorted(
                by_coverage.values(),
                key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]),
            )
        )
        if len(selected) != BLOCK_CONDITIONED_COUNTS[neighbour_count]:
            raise RuntimeError(
                f"block-conditioned count a={neighbour_count} changed: {len(selected)}"
            )
        rejected = {
            mask
            for mask in target
            if any((mask & fixed) == ones for ones, fixed in selected)
        }
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


def restricted_local_cubes(neighbour_count: int) -> tuple[Cube, ...]:
    if not 0 <= neighbour_count <= 6:
        raise ValueError("root-neighbour count must lie in 0..6")
    restricted: set[Cube] = set()
    for ones, fixed in reduced_cubes():
        survives = True
        for vertex in range(1, 7):
            position = universal.edge_position(0, vertex)
            if (fixed >> position) & 1:
                actual = vertex <= neighbour_count
                if bool((ones >> position) & 1) != actual:
                    survives = False
                    break
        if survives:
            restricted.add((project_nonroot(ones), project_nonroot(fixed)))
    return tuple(
        sorted(restricted, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
    )


@functools.cache
def conditioned_local_cubes() -> tuple[tuple[Cube, ...], ...]:
    """Greedily retain an exact cover after fixing the local root pattern."""
    result: list[tuple[Cube, ...]] = []
    root_positions = tuple(
        universal.edge_position(0, vertex) for vertex in range(1, 7)
    )
    for neighbour_count in range(7):
        projected = tuple(
            sorted(
                {
                    project_nonroot(mask)
                    for mask in forbidden_masks()
                    if all(
                        bool((mask >> position) & 1) == (vertex <= neighbour_count)
                        for vertex, position in enumerate(root_positions, 1)
                    )
                }
            )
        )
        index = {mask: item for item, mask in enumerate(projected)}
        candidates: list[tuple[frozenset[int], int, int]] = []
        for ones, fixed in restricted_local_cubes(neighbour_count):
            coverage = frozenset(
                index[mask] for mask in projected if (mask & fixed) == ones
            )
            if coverage:
                candidates.append((coverage, ones, fixed))
        active = set(range(len(projected)))
        selected: list[Cube] = []
        while active:
            coverage, ones, fixed = max(
                candidates,
                key=lambda item: (
                    len(active & item[0]),
                    -item[2].bit_count(),
                    -item[2],
                    -item[1],
                ),
            )
            newly_covered = active & coverage
            if not newly_covered:
                raise RuntimeError(
                    f"conditioned local cover stuck at a={neighbour_count}"
                )
            selected.append((ones, fixed))
            active -= newly_covered
        ordered = tuple(
            sorted(
                set(selected),
                key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]),
            )
        )
        if len(ordered) != LOCAL_CONDITIONED_COUNTS[neighbour_count]:
            raise RuntimeError(
                f"conditioned local count a={neighbour_count} changed: {len(ordered)}"
            )
        rejected = {
            mask
            for mask in projected
            if any((mask & fixed) == ones for ones, fixed in ordered)
        }
        if rejected != set(projected):
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
        raise RuntimeError(f"degree-{degree} clause count changed: {total}")
    return total


def generate(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    total = clause_count(degree)
    name = f"cover5_closed_block_degree_d{degree}.cnf"
    manifest_name = f"cover5_closed_block_degree_d{degree}_manifest.json"
    target = output / name
    manifest_path = output / manifest_name
    output.mkdir(parents=True, exist_ok=True)
    for path in (target, manifest_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace complement-closed artifact: {path}")
    partial = output / f"{name}.{os.getpid()}.partial"
    root_free_cubes = block_conditioned_cubes()
    root_containing_cubes = conditioned_local_cubes()
    root_free_count = 0
    root_containing_count = 0
    widths: Counter[int] = Counter()
    try:
        with partial.open("xb", buffering=8 * 1024 * 1024) as stream:
            writer = degree_branch.HashedWriter(stream)
            writer.block(f"p cnf 66 {total}\n".encode("ascii"))
            base = degree_branch.simplified_base_clauses(degree)
            writer.clause_block(base)
            widths.update(map(len, base))
            for vertices in itertools.combinations(range(1, 12), 7):
                neighbours = sum(vertex <= degree for vertex in vertices)
                variables = universal.subset_variables(vertices)
                clauses = tuple(
                    universal.instantiate_cube_blocker(cube, variables)
                    for cube in root_free_cubes[neighbours]
                )
                writer.clause_block(clauses)
                root_free_count += len(clauses)
                widths.update(map(len, clauses))
            for vertices in itertools.combinations(range(1, 12), 6):
                neighbours = sum(vertex <= degree for vertex in vertices)
                variables = degree_branch.six_subset_variables(vertices)
                clauses = tuple(
                    degree_branch.instantiate(cube, variables)
                    for cube in root_containing_cubes[neighbours]
                )
                writer.clause_block(clauses)
                root_containing_count += len(clauses)
                widths.update(map(len, clauses))
            if writer.clauses != total:
                raise RuntimeError(
                    f"written clause mismatch: {writer.clauses} != {total}"
                )
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
        "status": "UNCERTIFIED_COMPLEMENT_CLOSED_DEGREE_TARGET",
        "scope": (
            "Catalogue-independent residual CNF for the complement-closed "
            "eight-class order-seven target; generation alone proves no UNSAT."
        ),
        "degree": degree,
        "complementary_degree": 11 - degree,
        "local_target": {
            "isomorphism_classes": local.EXPECTED_ISOMORPHISM_CLASSES,
            "labelled_masks": local.EXPECTED_COMPLEMENT_CLOSURE,
            "cubes": local.EXPECTED_CUBES,
            "cube_sha256": local.EXPECTED_CUBE_CLOSURE_SHA256,
            "closed_under_complement": True,
        },
        "files": {"formula": formula},
        "counts": {
            "base": len(degree_branch.simplified_base_clauses(degree)),
            "root_free": root_free_count,
            "root_containing": root_containing_count,
            "total": total,
            "widths": dict(sorted(widths.items())),
        },
        "formal_bridge_status": "not yet formalized in Lean",
        "proof_status": "no solver proof",
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return manifest


def verify(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    manifest_path = output / f"cover5_closed_block_degree_d{degree}_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    metadata = manifest["files"]["formula"]
    path = output / metadata["name"]
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    if digest != metadata["sha256"] or size != metadata["bytes"]:
        raise ValueError("complement-closed formula hash or size mismatch")
    if lines != clause_count(degree) + 1:
        raise ValueError("complement-closed formula line count mismatch")
    return {
        "status": "PASS",
        "degree": degree,
        "sha256": digest,
        "bytes": size,
        "lines": lines,
    }


def preflight() -> dict[str, object]:
    blocks = block_conditioned_cubes()
    locals_ = conditioned_local_cubes()
    return {
        "status": "PASS",
        "scope": "counts and exact local reductions only; no K12 CNF written",
        "complement_closed_classes": local.EXPECTED_ISOMORPHISM_CLASSES,
        "labelled_masks": len(forbidden_masks()),
        "cubes": len(reduced_cubes()),
        "block_conditioned_counts": [len(items) for items in blocks],
        "local_conditioned_counts": [len(items) for items in locals_],
        "degree_clause_counts": {str(degree): clause_count(degree) for degree in DEGREES},
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("preflight", "generate", "verify"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--degree", type=int, choices=DEGREES)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    else:
        if args.output is None or args.degree is None:
            parser.error("generate/verify require --output and --degree")
        result = (
            generate(args.output, args.degree)
            if args.command == "generate"
            else verify(args.output, args.degree)
        )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
