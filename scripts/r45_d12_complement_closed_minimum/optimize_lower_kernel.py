#!/usr/bin/env python3
"""Greedily compress the exact two-pair lower-bound proof kernel."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

from scripts.r45_d12_complement_closed_minimum import derive_lower_kernel as derive
from scripts.r45_d12_complement_closed_minimum import search_complement_closed_minimum as search


def selection_hit_mask(clause: int, candidate_count: int) -> int:
    result = 0
    position = 0
    for left in range(candidate_count):
        left_hits = clause >> left & 1
        for right in range(left, candidate_count):
            if left_hits or clause >> right & 1:
                result |= 1 << position
            position += 1
    return result


def greedy_kernel(
    rows: Sequence[int], clauses_by_row: dict[int, int], candidate_count: int
) -> tuple[int, ...]:
    selection_count = candidate_count * (candidate_count + 1) // 2
    survivors = (1 << selection_count) - 1
    hit_masks = {
        row: selection_hit_mask(clauses_by_row[row], candidate_count) for row in rows
    }
    chosen: list[int] = []
    remaining = set(rows)
    while survivors:
        row = min(
            remaining,
            key=lambda candidate: (
                (survivors & hit_masks[candidate]).bit_count(),
                candidate,
            ),
        )
        new_survivors = survivors & hit_masks[row]
        if new_survivors == survivors:
            raise AssertionError("witness pool cannot eliminate surviving selections")
        chosen.append(row)
        remaining.remove(row)
        survivors = new_survivors
    return derive.deletion_minimize(chosen, clauses_by_row, candidate_count)


def optimize(incidence_path: Path, source12_path: Path) -> dict[str, object]:
    records, covers, graph_count = search.read_incidence(incidence_path)
    involution = search.complement_involution(records)
    pairs, pair_covers = search.paired_candidates(covers, involution)
    lower_search = search.exact_cover_search(pair_covers, graph_count, 2)
    if lower_search["cover"] is not None:
        raise ValueError("full incidence unexpectedly has a two-pair cover")
    pool = lower_search["state_witness_rows"]
    clauses_by_row = {row: derive.row_clause(pair_covers, row) for row in pool}
    reduced = greedy_kernel(pool, clauses_by_row, len(pairs))
    if derive.hitting_set_at_most_two(
        [clauses_by_row[row] for row in reduced], len(pairs)
    ) is not None:
        raise AssertionError("optimized kernel admits a two-pair cover")
    source_records = derive.records_at(source12_path, reduced)
    return {
        "schema_version": 1,
        "status": "PASS",
        "initial_state_witnesses": len(pool),
        "kernel_graphs": len(reduced),
        "kernel": [
            {
                "catalogue_index_zero_based": row,
                "graph6": source_records[row],
                "covering_pair_count": clauses_by_row[row].bit_count(),
                "covering_pair_mask_hex": f"{clauses_by_row[row]:046X}",
            }
            for row in reduced
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--incidence", type=Path, required=True)
    parser.add_argument("--source12", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(optimize(args.incidence, args.source12), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
