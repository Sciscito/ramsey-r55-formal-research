#!/usr/bin/env python3
"""Build an exact disjoint cube cover of each admissible d12 cross row.

For a fixed R(3,5,12) graph A, a B vertex may be blue to the deleted
root.  Its red-neighbour mask in A must hit every independent 4-set of A.
This monotone Boolean function has only 12 variables.  A memoized exact
decision-tree recurrence chooses, at every partial assignment, the next bit
which minimizes the number of accepted terminal cubes.

The emitted counts describe a disjoint interval/cube cover.  They do not by
themselves prove the full d12 branch UNSAT.
"""

from __future__ import annotations

import functools
import importlib.util
import itertools
import json
from collections import Counter
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[2]
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"
CATALOGUE_PATH = REPOSITORY / "r55" / "r35_12.g6"
ORDER = 12
FULL = (1 << ORDER) - 1


def load_ramsey():
    spec = importlib.util.spec_from_file_location("d12_interval_ramsey", RAMSEY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {RAMSEY_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ramsey = load_ramsey()


def independent_four_masks(graph: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        sum(1 << vertex for vertex in vertices)
        for vertices in itertools.combinations(range(ORDER), 4)
        if all(
            not ramsey.has_edge(graph, left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
    )


def optimal_disjoint_cover(blocks: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    """Return disjoint accepted cubes as ``(red_bits, blue_bits)`` pairs."""

    choice: dict[tuple[int, int], int] = {}

    @functools.lru_cache(maxsize=None)
    def minimum(red: int, blue: int) -> int:
        if all(red & block for block in blocks):
            return 1
        if any(block & ~blue == 0 for block in blocks):
            return 0
        unassigned = FULL & ~(red | blue)
        if not unassigned:
            raise AssertionError("total assignment was neither accepted nor rejected")
        best_count: int | None = None
        best_vertex = -1
        remaining = unassigned
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            count = minimum(red | bit, blue) + minimum(red, blue | bit)
            if best_count is None or count < best_count:
                best_count, best_vertex = count, bit.bit_length() - 1
        assert best_count is not None and best_vertex >= 0
        choice[red, blue] = best_vertex
        return best_count

    expected = minimum(0, 0)
    cubes: list[tuple[int, int]] = []

    def visit(red: int, blue: int) -> None:
        if all(red & block for block in blocks):
            cubes.append((red, blue))
            return
        if any(block & ~blue == 0 for block in blocks):
            return
        vertex = choice[red, blue]
        bit = 1 << vertex
        visit(red | bit, blue)
        visit(red, blue | bit)

    visit(0, 0)
    if len(cubes) != expected:
        raise AssertionError("cover reconstruction disagrees with optimum")

    matching = [0] * (1 << ORDER)
    for red, blue in cubes:
        if red & blue:
            raise AssertionError("cube assigns one bit both ways")
        for assignment in range(1 << ORDER):
            if assignment & red == red and (~assignment & FULL) & blue == blue:
                matching[assignment] += 1
    for assignment, count in enumerate(matching):
        accepted = all(assignment & block for block in blocks)
        if count != int(accepted):
            raise AssertionError(
                f"assignment {assignment} has multiplicity {count}, accepted={accepted}"
            )
    return tuple(cubes)


def report() -> dict[str, object]:
    records = tuple(
        line.strip()
        for line in CATALOGUE_PATH.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    rows: list[dict[str, object]] = []
    for index, record in enumerate(records):
        graph = ramsey.decode_graph6(record)
        blocks = independent_four_masks(graph)
        cubes = optimal_disjoint_cover(blocks)
        admissible = sum(
            all(assignment & block for block in blocks)
            for assignment in range(1 << ORDER)
        )
        rows.append({
            "catalogue_index": index,
            "record": record,
            "blue_K4s": len(blocks),
            "admissible_patterns": admissible,
            "optimal_adaptive_disjoint_cubes": len(cubes),
            "assigned_literal_distribution": dict(sorted(Counter(
                (red | blue).bit_count() for red, blue in cubes
            ).items())),
        })
    return {
        "algorithm": "exact dynamic programming over 3^12 partial assignments",
        "rows": rows,
        "total_admissible_patterns": sum(int(row["admissible_patterns"]) for row in rows),
        "total_disjoint_cubes": sum(int(row["optimal_adaptive_disjoint_cubes"]) for row in rows),
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
