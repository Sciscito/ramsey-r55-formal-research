#!/usr/bin/env python3
"""Generate a degree branch also conditioned by its two root blocks."""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
from collections import Counter
from pathlib import Path

from . import generate_degree_branch as degree_branch
from . import generate_universal as universal


BLOCK_CONDITIONED_COUNTS = (2_520, 5_760, 9_960, 11_448, 9_396, 5_040, 1_260, 0)
EXPECTED_CLAUSE_COUNTS = {
    3: 3_052_941,
    4: 3_465_951,
    5: 3_508_890,
    6: 3_181_470,
    7: 2_552_955,
    8: 1_750_101,
}

Cube = tuple[int, int]


def triangle_masks(vertices) -> tuple[int, ...]:
    return tuple(
        sum(
            1 << universal.edge_position(left, right)
            for left, right in itertools.combinations(triple, 2)
        )
        for triple in itertools.combinations(vertices, 3)
    )


def block_forbidden_masks(neighbour_count: int) -> tuple[int, ...]:
    positive_triangles = triangle_masks(range(neighbour_count))
    negative_triangles = triangle_masks(range(neighbour_count, 7))
    return tuple(
        sorted(
            mask
            for mask in universal.raw_forbidden_masks()
            if all((mask & triangle) != triangle for triangle in positive_triangles)
            and all((mask & triangle) != 0 for triangle in negative_triangles)
        )
    )


def block_conditioned_cubes() -> tuple[tuple[Cube, ...], ...]:
    """Keep one audited universal cube for each distinct useful coverage set."""
    full = (1 << universal.LOCAL_VARIABLE_COUNT) - 1
    result = []
    for neighbour_count in range(8):
        target = block_forbidden_masks(neighbour_count)
        index = {mask: item for item, mask in enumerate(target)}
        by_coverage: dict[tuple[int, ...], Cube] = {}
        for ones, fixed in universal.reduced_cubes():
            free = full ^ fixed
            completion = free
            covered = []
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
            old = by_coverage.get(coverage)
            if old is None or (fixed.bit_count(), fixed, ones) < (
                old[1].bit_count(),
                old[1],
                old[0],
            ):
                by_coverage[coverage] = (ones, fixed)
        selected = tuple(
            sorted(by_coverage.values(), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
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


def clause_count(degree: int) -> int:
    if degree not in degree_branch.DEGREES:
        raise ValueError("unsupported degree")
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
        * degree_branch.LOCAL_CONDITIONED_COUNTS[neighbours]
        for neighbours in range(7)
        if neighbours <= degree and 6 - neighbours <= 11 - degree
    )
    result = len(degree_branch.simplified_base_clauses(degree)) + root_free + root_containing
    if result != EXPECTED_CLAUSE_COUNTS[degree]:
        raise RuntimeError(f"block degree-{degree} count changed: {result}")
    return result


def generate(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    universal.verify(output)
    total = clause_count(degree)
    name = f"cover9_universal_block_degree_d{degree}.cnf"
    manifest_name = f"block_degree_d{degree}_manifest.json"
    target = output / name
    manifest_path = output / manifest_name
    for path in (target, manifest_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace block-degree artifact: {path}")
    partial = output / f"{name}.{os.getpid()}.partial"
    root_free_cubes = block_conditioned_cubes()
    root_containing_cubes = degree_branch.conditioned_local_cubes()
    root_free_count = 0
    root_containing_count = 0
    width_counts: Counter[int] = Counter()
    try:
        with partial.open("xb", buffering=8 * 1024 * 1024) as stream:
            writer = degree_branch.HashedWriter(stream)
            writer.block(f"p cnf 66 {total}\n".encode("ascii"))
            writer.clause_block(degree_branch.simplified_base_clauses(degree))
            for subset_index, vertices in enumerate(itertools.combinations(range(1, 12), 7), 1):
                neighbours = sum(vertex <= degree for vertex in vertices)
                variables = universal.subset_variables(vertices)
                clauses = tuple(
                    universal.instantiate_cube_blocker(cube, variables)
                    for cube in root_free_cubes[neighbours]
                )
                root_free_count += len(clauses)
                width_counts.update(map(len, clauses))
                writer.clause_block(clauses)
                if subset_index % 55 == 0:
                    print(f"block degree {degree}: root-free {subset_index}/330", flush=True)
            for subset_index, vertices in enumerate(itertools.combinations(range(1, 12), 6), 1):
                neighbours = sum(vertex <= degree for vertex in vertices)
                variables = degree_branch.six_subset_variables(vertices)
                clauses = tuple(
                    degree_branch.instantiate(cube, variables)
                    for cube in root_containing_cubes[neighbours]
                )
                root_containing_count += len(clauses)
                width_counts.update(map(len, clauses))
                writer.clause_block(clauses)
                if subset_index % 77 == 0:
                    print(f"block degree {degree}: root-containing {subset_index}/462", flush=True)
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
        "status": "UNCERTIFIED_BLOCK_CONDITIONED_DEGREE_TARGET",
        "files": {"formula": formula},
        "degree": degree,
        "root_assignment": [
            variable if value else -variable
            for variable, value in degree_branch.root_assignment(degree).items()
        ],
        "counts": {
            "base": len(degree_branch.simplified_base_clauses(degree)),
            "root_free_motif": root_free_count,
            "root_containing_motif": root_containing_count,
            "total": total,
            "widths": dict(sorted(width_counts.items())),
        },
        "local_certificates": {
            "root_free_counts_by_neighbour_block_size": list(BLOCK_CONDITIONED_COUNTS),
            "root_containing_counts_by_neighbour_block_size": list(
                degree_branch.LOCAL_CONDITIONED_COUNTS
            ),
            "scope": (
                "Exact under R(4,4), no positive triangle inside the root-neighbour "
                "block, and no negative triangle inside the root-nonneighbour block."
            ),
        },
        "formal_bridge_status": "not yet formalized in Lean",
        "proof_status": "no solver proof",
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
    )
    return manifest


def verify(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    manifest = json.loads(
        (output / f"block_degree_d{degree}_manifest.json").read_text(encoding="utf-8")
    )
    metadata = manifest["files"]["formula"]
    path = output / metadata["name"]
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    if digest != metadata["sha256"] or size != metadata["bytes"]:
        raise ValueError("block-degree formula hash or size mismatch")
    if lines != clause_count(degree) + 1:
        raise ValueError("block-degree formula line count mismatch")
    return {"status": "PASS", "degree": degree, "sha256": digest, "bytes": size, "lines": lines}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("counts", "generate", "verify"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--degree", type=int)
    args = parser.parse_args()
    if args.command == "counts":
        result = {str(degree): clause_count(degree) for degree in degree_branch.DEGREES}
    else:
        if args.output is None or args.degree is None:
            parser.error("generate/verify require --output and --degree")
        result = generate(args.output, args.degree) if args.command == "generate" else verify(args.output, args.degree)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
