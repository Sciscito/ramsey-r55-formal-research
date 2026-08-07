#!/usr/bin/env python3
"""Generate one offline-simplified canonical root-degree branch."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
from collections import Counter
from pathlib import Path
from typing import BinaryIO, Sequence

from . import generate_universal as universal


DEGREES = tuple(range(3, 9))
UNCHANGED_SEVEN_SUBSETS = math.comb(11, 7)
LOCAL_RESTRICTED_COUNTS = (0, 210, 384, 666, 1_080, 1_530, 2_160)
LOCAL_CONDITIONED_COUNTS = (0, 30, 216, 414, 432, 150, 0)
EXPECTED_CLAUSE_COUNTS = {
    3: 5_063_901,
    4: 5_105_211,
    5: 5_139_690,
    6: 5_158_770,
    7: 5_156_115,
    8: 5_129_421,
}

Cube = tuple[int, int]
Clause = tuple[int, ...]


def root_assignment(degree: int) -> dict[int, bool]:
    if degree not in DEGREES:
        raise ValueError(f"canonical degree must be one of {DEGREES}")
    return {universal.edge_var(12, 0, vertex): vertex <= degree for vertex in range(1, 12)}


def simplify_clause(clause: Sequence[int], assignment: dict[int, bool]) -> Clause | None:
    result = []
    for literal in clause:
        value = assignment.get(abs(literal))
        if value is None:
            result.append(literal)
        elif value == (literal > 0):
            return None
    return tuple(result)


def restricted_local_cubes(cubes: Sequence[Cube] | None = None) -> tuple[tuple[Cube, ...], ...]:
    """Restrict local vertex 0 to a prefix of a neighbours, for a=0..6."""
    selected = universal.reduced_cubes() if cubes is None else tuple(cubes)
    results = []
    for neighbour_count in range(7):
        restricted: set[Cube] = set()
        for ones, fixed in selected:
            survives = True
            for vertex in range(1, 7):
                position = universal.edge_position(0, vertex)
                if (fixed >> position) & 1:
                    actual = vertex <= neighbour_count
                    if bool((ones >> position) & 1) != actual:
                        survives = False
                        break
            if not survives:
                continue
            ones6 = 0
            fixed6 = 0
            for right in range(2, 7):
                for left in range(1, right):
                    source = universal.edge_position(left, right)
                    target = universal.edge_position(left - 1, right - 1)
                    if (fixed >> source) & 1:
                        fixed6 |= 1 << target
                        if (ones >> source) & 1:
                            ones6 |= 1 << target
            restricted.add((ones6, fixed6))
        ordered = tuple(sorted(restricted, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))
        if len(ordered) != LOCAL_RESTRICTED_COUNTS[neighbour_count]:
            raise RuntimeError(
                f"restricted local count a={neighbour_count} changed: {len(ordered)}"
            )
        results.append(ordered)
    return tuple(results)


def project_nonroot(mask: int) -> int:
    result = 0
    for right in range(2, 7):
        for left in range(1, right):
            if (mask >> universal.edge_position(left, right)) & 1:
                result |= 1 << universal.edge_position(left - 1, right - 1)
    return result


def conditioned_local_cubes() -> tuple[tuple[Cube, ...], ...]:
    """Remove restricted cubes useless/redundant under local R(4,4)."""
    raw = restricted_local_cubes()
    forbidden = universal.raw_forbidden_masks()
    root_positions = tuple(universal.edge_position(0, vertex) for vertex in range(1, 7))
    result = []
    for neighbour_count, candidates in enumerate(raw):
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
        index = {mask: item for item, mask in enumerate(projected)}
        covered_candidates = []
        for ones, fixed in candidates:
            coverage = frozenset(
                index[mask] for mask in projected if (mask & fixed) == ones
            )
            if coverage:
                covered_candidates.append((coverage, ones, fixed))
        active = set(range(len(projected)))
        selected: list[Cube] = []
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
                raise RuntimeError(f"conditioned cover stuck at a={neighbour_count}")
            selected.append((ones, fixed))
            active -= newly_covered
        ordered = tuple(
            sorted(set(selected), key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
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
            raise RuntimeError("conditioned local coverage mismatch")
        result.append(ordered)
    return tuple(result)

def simplified_base_clauses(degree: int) -> tuple[Clause, ...]:
    clauses: list[Clause] = []
    nonroot = range(1, 12)
    for vertices in itertools.combinations(nonroot, 4):
        edges = tuple(
            universal.edge_var(12, left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        clauses.append(tuple(-edge for edge in edges))
        clauses.append(edges)
    for vertices in itertools.combinations(range(1, degree + 1), 3):
        clauses.append(
            tuple(
                -universal.edge_var(12, left, right)
                for left, right in itertools.combinations(vertices, 2)
            )
        )
    for vertices in itertools.combinations(range(degree + 1, 12), 3):
        clauses.append(
            tuple(
                universal.edge_var(12, left, right)
                for left, right in itertools.combinations(vertices, 2)
            )
        )
    if any(simplify_clause(clause, root_assignment(degree)) != clause for clause in clauses):
        raise RuntimeError("simplified base unexpectedly mentions a root edge")
    return tuple(clauses)


def branch_clause_count(degree: int) -> int:
    if degree not in DEGREES:
        raise ValueError("unsupported degree")
    with_root = sum(
        math.comb(degree, neighbours)
        * math.comb(11 - degree, 6 - neighbours)
        * LOCAL_CONDITIONED_COUNTS[neighbours]
        for neighbours in range(7)
        if neighbours <= degree and 6 - neighbours <= 11 - degree
    )
    result = (
        len(simplified_base_clauses(degree))
        + UNCHANGED_SEVEN_SUBSETS * universal.REDUCED_LOCAL_CLAUSE_COUNT
        + with_root
    )
    if result != EXPECTED_CLAUSE_COUNTS[degree]:
        raise RuntimeError(f"degree-{degree} clause count changed: {result}")
    return result


def six_subset_variables(vertices: Sequence[int]) -> tuple[int, ...]:
    if len(vertices) != 6 or tuple(sorted(vertices)) != tuple(vertices):
        raise ValueError("expected six increasing vertices")
    return tuple(
        universal.edge_var(12, vertices[left], vertices[right])
        for right in range(1, 6)
        for left in range(right)
    )


def instantiate(cube: Cube, variables: Sequence[int]) -> Clause:
    ones, fixed = cube
    return tuple(
        -variables[position] if (ones >> position) & 1 else variables[position]
        for position in range(len(variables))
        if (fixed >> position) & 1
    )


class HashedWriter:
    def __init__(self, stream: BinaryIO):
        self.stream = stream
        self.digest = hashlib.sha256()
        self.bytes = 0
        self.clauses = 0

    def block(self, data: bytes, clauses: int = 0) -> None:
        self.stream.write(data)
        self.digest.update(data)
        self.bytes += len(data)
        self.clauses += clauses

    def clause_block(self, clauses: Sequence[Clause]) -> None:
        data = "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses).encode("ascii")
        self.block(data, len(clauses))


def generate(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    universal.verify(output)
    clause_count = branch_clause_count(degree)
    name = f"cover9_universal_degree_d{degree}.cnf"
    manifest_name = f"degree_d{degree}_manifest.json"
    target = output / name
    manifest_path = output / manifest_name
    for path in (target, manifest_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace degree artifact: {path}")
    partial = output / f"{name}.{os.getpid()}.partial"
    full_cubes = universal.reduced_cubes()
    by_neighbour_count = conditioned_local_cubes()
    try:
        with partial.open("xb", buffering=8 * 1024 * 1024) as stream:
            writer = HashedWriter(stream)
            writer.block(f"p cnf 66 {clause_count}\n".encode("ascii"))
            writer.clause_block(simplified_base_clauses(degree))

            for subset_index, vertices in enumerate(itertools.combinations(range(1, 12), 7), 1):
                variables = universal.subset_variables(vertices)
                clauses = tuple(universal.instantiate_cube_blocker(cube, variables) for cube in full_cubes)
                writer.clause_block(clauses)
                if subset_index % 55 == 0:
                    print(f"degree {degree}: root-free subsets {subset_index}/{UNCHANGED_SEVEN_SUBSETS}", flush=True)

            containing_count = 0
            duplicate_count = 0
            width_counts: Counter[int] = Counter()
            for subset_index, vertices in enumerate(itertools.combinations(range(1, 12), 6), 1):
                neighbour_count = sum(vertex <= degree for vertex in vertices)
                variables = six_subset_variables(vertices)
                local = by_neighbour_count[neighbour_count]
                clauses = tuple(instantiate(cube, variables) for cube in local)
                if len(set(clauses)) != len(clauses):
                    raise RuntimeError("post-instantiation duplicate survived local deduplication")
                containing_count += len(clauses)
                duplicate_count += 0
                width_counts.update(map(len, clauses))
                writer.clause_block(clauses)
                if subset_index % 77 == 0:
                    print(f"degree {degree}: root-containing subsets {subset_index}/462", flush=True)
            if writer.clauses != clause_count:
                raise RuntimeError(f"written clause count mismatch: {writer.clauses} != {clause_count}")
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

    assignment = root_assignment(degree)
    manifest = {
        "schema_version": 1,
        "status": "UNCERTIFIED_CANONICAL_DEGREE_TARGET",
        "files": {"formula": formula},
        "degree": degree,
        "root_assignment": [variable if value else -variable for variable, value in assignment.items()],
        "restriction": {
            "source_formula_sha256": universal.EXPECTED_FORMULA_SHA256,
            "satisfied_clauses_removed": True,
            "false_root_literals_removed": True,
            "root_variables_retained_but_unused": list(range(1, 12)),
            "exact_duplicate_clauses_removed_within_each_restricted_subset": True,
            "restricted_local_counts_before_conditioned_pruning": list(LOCAL_RESTRICTED_COUNTS),
            "conditioned_local_counts_by_number_of_neighbours": list(LOCAL_CONDITIONED_COUNTS),
            "conditioned_pruning_scope": (
                "exact relative to local R(4,4): zero-coverage cubes are removed "
                "and a deterministic set cover still rejects every forbidden "
                "completion in the fixed root-neighbour slice"
            ),
            "root_free_motif_clauses": UNCHANGED_SEVEN_SUBSETS * universal.REDUCED_LOCAL_CLAUSE_COUNT,
            "root_containing_motif_clauses": containing_count,
            "root_containing_widths": dict(sorted(width_counts.items())),
        },
        "global_cover_obligation": (
            "To infer UNSAT of the universal source, prove degrees lie in 3..8, "
            "transport every root neighbourhood by a vertex permutation to its "
            "prefix representative, and replay all six restricted UNSAT proofs."
        ),
        "formal_bridge_status": "not yet formalized in Lean",
        "proof_status": "no solver proof",
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
    )
    return manifest


def verify(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    manifest_path = output / f"degree_d{degree}_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    metadata = manifest["files"]["formula"]
    path = output / metadata["name"]
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    if digest != metadata["sha256"] or size != metadata["bytes"]:
        raise ValueError("degree formula hash or size mismatch")
    if lines != branch_clause_count(degree) + 1:
        raise ValueError("degree formula line count mismatch")
    return {"status": "PASS", "degree": degree, "sha256": digest, "bytes": size, "lines": lines}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("counts", "generate", "verify"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--degree", type=int)
    args = parser.parse_args()
    if args.command == "counts":
        result = {str(degree): branch_clause_count(degree) for degree in DEGREES}
    else:
        if args.output is None or args.degree is None:
            parser.error("generate/verify require --output and --degree")
        result = generate(args.output, args.degree) if args.command == "generate" else verify(args.output, args.degree)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
