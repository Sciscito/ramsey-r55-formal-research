#!/usr/bin/env python3
"""Derive a small explicit kernel excluding two complement-pair covers."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
from typing import Sequence

from scripts.r45_d12_complement_closed_minimum import search_complement_closed_minimum as search


EXPECTED_SOURCE12_SHA256 = (
    "C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def row_clause(covers: Sequence[int], graph_index: int) -> int:
    graph_bit = 1 << graph_index
    return sum(1 << candidate for candidate, cover in enumerate(covers) if cover & graph_bit)


def hitting_set_at_most_two(
    clauses: Sequence[int], candidate_count: int
) -> tuple[int, ...] | None:
    if any(clause == 0 for clause in clauses):
        return None
    if not clauses:
        return ()
    all_candidates = (1 << candidate_count) - 1
    for first in range(candidate_count):
        unhit = tuple(clause for clause in clauses if not (clause >> first & 1))
        if not unhit:
            return (first,)
        common = all_candidates
        for clause in unhit:
            common &= clause
        if common:
            second_bit = common & -common
            return first, second_bit.bit_length() - 1
    return None


def deletion_minimize(
    rows: Sequence[int], clauses_by_row: dict[int, int], candidate_count: int
) -> tuple[int, ...]:
    current = list(rows)
    changed = True
    while changed:
        changed = False
        for row in tuple(reversed(current)):
            trial = [candidate for candidate in current if candidate != row]
            if hitting_set_at_most_two(
                [clauses_by_row[candidate] for candidate in trial], candidate_count
            ) is None:
                current = trial
                changed = True
    return tuple(current)


def find_smaller_kernel(
    pool: Sequence[int], clauses_by_row: dict[int, int], candidate_count: int, upper: int
) -> tuple[int, ...] | None:
    for size in range(1, upper):
        for rows in itertools.combinations(pool, size):
            if hitting_set_at_most_two(
                [clauses_by_row[row] for row in rows], candidate_count
            ) is None:
                return rows
    return None


def records_at(path: Path, indices: Sequence[int]) -> dict[int, str]:
    wanted = set(indices)
    result: dict[int, str] = {}
    with path.open("rt", encoding="ascii") as stream:
        for index, line in enumerate(stream):
            if index in wanted:
                result[index] = line.strip()
    if result.keys() != wanted:
        raise ValueError("kernel record missing from source")
    return result


def derive(incidence_path: Path, source12_path: Path) -> dict[str, object]:
    if sha256(source12_path) != EXPECTED_SOURCE12_SHA256:
        raise ValueError("order-twelve source SHA-256 mismatch")
    records, covers, graph_count = search.read_incidence(incidence_path)
    involution = search.complement_involution(records)
    pairs, pair_covers = search.paired_candidates(covers, involution)
    lower_search = search.exact_cover_search(pair_covers, graph_count, 2)
    if lower_search["cover"] is not None:
        raise ValueError("full incidence unexpectedly has a two-pair cover")
    pool = lower_search["state_witness_rows"]
    clauses_by_row = {row: row_clause(pair_covers, row) for row in pool}
    if hitting_set_at_most_two(tuple(clauses_by_row.values()), len(pairs)) is not None:
        raise AssertionError("state witness rows do not replay the lower bound")
    reduced = deletion_minimize(pool, clauses_by_row, len(pairs))
    smaller = (
        find_smaller_kernel(pool, clauses_by_row, len(pairs), len(reduced))
        if len(reduced) <= 5
        else None
    )
    if smaller is not None:
        reduced = smaller
    if hitting_set_at_most_two(
        [clauses_by_row[row] for row in reduced], len(pairs)
    ) is not None:
        raise AssertionError("reduced kernel admits a two-pair cover")
    source_records = records_at(source12_path, reduced)
    return {
        "schema_version": 1,
        "status": "PASS",
        "claim": "The explicit kernel has no cover by at most two complement pairs.",
        "incidence_sha256": search.sha256(incidence_path),
        "source12_sha256": sha256(source12_path),
        "candidate_classes": len(records),
        "complement_pairs": len(pairs),
        "full_search_states": lower_search["explored_states"],
        "initial_state_witnesses": len(pool),
        "kernel_graphs": len(reduced),
        "kernel": [
            {
                "catalogue_index_zero_based": row,
                "graph6": source_records[row],
                "covering_pair_ids_zero_based": [
                    candidate
                    for candidate in range(len(pairs))
                    if clauses_by_row[row] >> candidate & 1
                ],
            }
            for row in reduced
        ],
        "scope": (
            "Catalogue-relative lower bound for complement-closed order-seven "
            "motif covers; the independent verifier must reconstruct signatures."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--incidence", type=Path, required=True)
    parser.add_argument("--source12", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(derive(args.incidence, args.source12), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
