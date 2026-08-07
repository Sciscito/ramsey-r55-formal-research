#!/usr/bin/env python3
"""Count admissible A-to-B row patterns modulo automorphisms of each A type."""

from __future__ import annotations

import importlib.util
import itertools
import json
from pathlib import Path
from typing import Sequence


REPOSITORY = Path(__file__).resolve().parents[2]
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"
CATALOGUE_PATH = REPOSITORY / "r55" / "r35_12.g6"
Graph = tuple[int, ...]


def load_ramsey():
    spec = importlib.util.spec_from_file_location("d12_orbit_ramsey", RAMSEY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {RAMSEY_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ramsey = load_ramsey()


def edge(graph: Graph, left: int, right: int) -> bool:
    return ramsey.has_edge(graph, left, right)


def is_isomorphism(source: Graph, target: Graph, permutation: Sequence[int]) -> bool:
    return all(
        edge(source, left, right) == edge(target, permutation[left], permutation[right])
        for left, right in itertools.combinations(range(len(source)), 2)
    )


def all_automorphisms(graph: Graph) -> tuple[tuple[int, ...], ...]:
    order = len(graph)
    degrees = tuple(row.bit_count() for row in graph)

    def signature(vertex: int):
        return (
            degrees[vertex],
            tuple(sorted(
                degrees[neighbor]
                for neighbor in range(order)
                if edge(graph, vertex, neighbor)
            )),
        )

    signatures = tuple(signature(vertex) for vertex in range(order))
    candidates = tuple(
        tuple(target for target in range(order) if signatures[target] == signatures[source])
        for source in range(order)
    )
    mapping = [-1] * order
    results: list[tuple[int, ...]] = []

    def visit(mapped: int, used: int) -> None:
        if mapped == order:
            permutation = tuple(mapping)
            if not is_isomorphism(graph, graph, permutation):
                raise AssertionError("invalid automorphism")
            results.append(permutation)
            return
        best_source = -1
        best_targets: tuple[int, ...] | None = None
        for source in range(order):
            if mapping[source] >= 0:
                continue
            compatible = tuple(
                target
                for target in candidates[source]
                if not (used >> target) & 1
                and all(
                    edge(graph, source, other)
                    == edge(graph, target, mapping[other])
                    for other in range(order)
                    if mapping[other] >= 0
                )
            )
            if not compatible:
                return
            if best_targets is None or len(compatible) < len(best_targets):
                best_source, best_targets = source, compatible
        assert best_source >= 0 and best_targets is not None
        for target in best_targets:
            mapping[best_source] = target
            visit(mapped + 1, used | 1 << target)
            mapping[best_source] = -1

    visit(0, 0)
    return tuple(sorted(results))


def permute_mask(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    for source, target in enumerate(permutation):
        if (mask >> source) & 1:
            result |= 1 << target
    return result


def main() -> None:
    records = tuple(
        line.strip()
        for line in CATALOGUE_PATH.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    rows: list[dict[str, object]] = []
    for index, record in enumerate(records):
        graph = ramsey.decode_graph6(record)
        automorphisms = all_automorphisms(graph)
        blue_k4s = tuple(
            vertices
            for vertices in itertools.combinations(range(12), 4)
            if all(not edge(graph, left, right) for left, right in itertools.combinations(vertices, 2))
        )
        admissible = {
            mask
            for mask in range(1 << 12)
            if all(any((mask >> vertex) & 1 for vertex in block) for block in blue_k4s)
        }
        representatives: set[int] = set()
        orbit_sizes: list[int] = []
        unseen = set(admissible)
        while unseen:
            seed = min(unseen)
            orbit = {permute_mask(seed, permutation) for permutation in automorphisms}
            if not orbit <= admissible:
                raise AssertionError("automorphism did not preserve admissibility")
            representatives.add(min(orbit))
            orbit_sizes.append(len(orbit))
            unseen -= orbit
        rows.append({
            "catalogue_index": index,
            "record": record,
            "automorphism_group_order": len(automorphisms),
            "admissible_patterns": len(admissible),
            "pattern_orbits": len(representatives),
            "minimum_orbit_size": min(orbit_sizes),
            "maximum_orbit_size": max(orbit_sizes),
        })
    print(json.dumps({
        "rows": rows,
        "total_admissible_patterns": sum(int(row["admissible_patterns"]) for row in rows),
        "total_pattern_orbits": sum(int(row["pattern_orbits"]) for row in rows),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
