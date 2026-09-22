#!/usr/bin/env python3
"""Greedily augment the tracked motif covers on R(4,4;10/11) holes.

This second-stage pilot uses the frozen official R(4,4;7) catalogue to name
every induced seven-vertex class in each hole left by cover5 or cover6.  It
reports deterministic greedy additions, both by individual motif and by exact
complement pair.  The computation is catalogue-relative and proof-free.
"""

from __future__ import annotations

import argparse
import gzip
import json
import time
from pathlib import Path
from typing import Iterable, Sequence

from scripts.r45_d12_complement_closed_minimum import verify_cover6 as cover6
from scripts.r45_d12_cover9_universal import generate_complement_closed_cover5 as cover5
from scripts.r45_d12_cover9_universal import scan_small_r44_covers as scan


EXPECTED_SOURCE7_BYTES = 2_172
EXPECTED_SOURCE7_SHA256 = "6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010"
EXPECTED_CLASSES7 = 362
EXPECTED_LABELLED_R44_7 = 923_012


def read_source7(path: Path) -> tuple[str, ...]:
    identity = (path.stat().st_size, scan.sha256(path))
    expected = (EXPECTED_SOURCE7_BYTES, EXPECTED_SOURCE7_SHA256)
    if identity != expected:
        raise ValueError(f"R(4,4;7) identity mismatch: {identity} != {expected}")
    records = tuple(
        line.strip() for line in path.read_text(encoding="ascii").splitlines()
    )
    if len(records) != EXPECTED_CLASSES7 or len(set(records)) != len(records):
        raise ValueError("R(4,4;7) record count or uniqueness changed")
    return records


def build_all_owner(records: Sequence[str]) -> dict[int, int]:
    owner: dict[int, int] = {}
    for class_id, record in enumerate(records):
        for mask in cover6.orbit(record):
            previous = owner.setdefault(mask, class_id)
            if previous != class_id:
                raise ValueError("R(4,4;7) labelled class overlap")
    if len(owner) != EXPECTED_LABELLED_R44_7:
        raise ValueError(
            f"labelled R(4,4;7) count changed: {len(owner)}"
        )
    return owner


def class_ids_for_records(
    records: Iterable[str], owner: dict[int, int]
) -> tuple[int, ...]:
    result = tuple(owner[cover6.decode_graph6(record, 7)] for record in records)
    if len(set(result)) != len(result):
        raise ValueError("base cover repeats an isomorphism class")
    return result


def complement_pairs(
    records: Sequence[str], owner: dict[int, int]
) -> tuple[tuple[int, int], ...]:
    full = (1 << 21) - 1
    pairs = set()
    for class_id, record in enumerate(records):
        mask = cover6.decode_graph6(record, 7)
        complement_id = owner[full ^ mask]
        if complement_id == class_id:
            raise ValueError("unexpected self-complementary order-seven class")
        pairs.add(tuple(sorted((class_id, complement_id))))
    result = tuple(sorted(pairs))
    if len(result) != 181:
        raise ValueError(f"complement-pair count changed: {len(result)}")
    return result


def greedy_individual(
    holes: Sequence[frozenset[int]], candidates: Iterable[int]
) -> dict[str, object]:
    remaining = set(range(len(holes)))
    selected: list[int] = []
    gains: list[int] = []
    candidate_list = tuple(sorted(candidates))
    while remaining:
        best = max(
            candidate_list,
            key=lambda candidate: (
                sum(candidate in holes[index] for index in remaining),
                -candidate,
            ),
        )
        newly_covered = {
            index for index in remaining if best in holes[index]
        }
        if not newly_covered:
            raise ValueError("individual greedy cover is stuck")
        selected.append(best)
        gains.append(len(newly_covered))
        remaining.difference_update(newly_covered)
    return {"selected_class_ids": selected, "new_holes_covered": gains}


def greedy_pairs(
    holes: Sequence[frozenset[int]], pairs: Sequence[tuple[int, int]]
) -> dict[str, object]:
    hole_pairs = tuple(
        frozenset(
            pair_id
            for pair_id, pair in enumerate(pairs)
            if pair[0] in classes or pair[1] in classes
        )
        for classes in holes
    )
    result = greedy_individual(hole_pairs, range(len(pairs)))
    selected_pair_ids = result.pop("selected_class_ids")
    return {
        "selected_pair_ids": selected_pair_ids,
        "selected_class_pairs": [list(pairs[index]) for index in selected_pair_ids],
        **result,
    }


def scan_holes(
    source: Path,
    order: int,
    owner_all: dict[int, int],
    owner5: dict[int, int],
    owner6: dict[int, int],
) -> tuple[list[frozenset[int]], list[frozenset[int]], int]:
    expected = scan.CATALOGUES[order]
    identity = (source.stat().st_size, scan.sha256(source))
    expected_identity = (
        expected["compressed_bytes"],
        expected["compressed_sha256"],
    )
    if identity != expected_identity:
        raise ValueError(f"R(4,4;{order}) compressed identity mismatch")
    positions = scan.subset_positions(order)
    holes5: list[frozenset[int]] = []
    holes6: list[frozenset[int]] = []
    graph_count = 0
    with gzip.open(source, "rt", encoding="ascii", newline="") as stream:
        for raw_line in stream:
            graph = cover6.decode_graph6(raw_line.strip(), order)
            hit5 = False
            hit6 = False
            classes: set[int] = set()
            for edge_positions in positions:
                induced = cover6.induced_mask(graph, edge_positions)
                class_id = owner_all.get(induced)
                if class_id is None:
                    raise ValueError(
                        f"catalogue R(4,4;{order}) contains a non-R44 induced seven-set"
                    )
                classes.add(class_id)
                hit5 = hit5 or induced in owner5
                hit6 = hit6 or induced in owner6
                if hit5 and hit6:
                    break
            if not hit5 or not hit6:
                # If either family is absent, the loop necessarily exhausted all
                # subsets, so ``classes`` is the full induced-class signature.
                frozen = frozenset(classes)
                if not hit5:
                    holes5.append(frozen)
                if not hit6:
                    holes6.append(frozen)
            graph_count += 1
    if graph_count != expected["graphs"]:
        raise ValueError(f"R(4,4;{order}) record count changed")
    return holes5, holes6, graph_count


def describe_classes(class_ids: Sequence[int], records: Sequence[str]) -> list[dict[str, object]]:
    return [
        {"class_id_zero_based": class_id, "graph6": records[class_id]}
        for class_id in class_ids
    ]


def run(
    source7: Path,
    sources: Iterable[tuple[int, Path]],
) -> dict[str, object]:
    started = time.perf_counter()
    records = read_source7(source7)
    owner_all = build_all_owner(records)
    owner5 = scan.build_cover5_owner()
    _orbits6, owner6 = cover6.build_closure()
    base5 = class_ids_for_records(cover5.EXPECTED_RECORDS, owner_all)
    base6 = class_ids_for_records(cover6.EXPECTED_RECORDS, owner_all)
    pairs = complement_pairs(records, owner_all)
    base6_pairs = {
        pair_id
        for pair_id, pair in enumerate(pairs)
        if pair[0] in base6 or pair[1] in base6
    }
    if len(base6_pairs) != 3:
        raise ValueError("cover6 no longer consists of three complement pairs")

    results = []
    for order, source in sources:
        scan_started = time.perf_counter()
        holes5, holes6, graph_count = scan_holes(
            source, order, owner_all, owner5, owner6
        )
        addition5 = greedy_individual(
            holes5, set(range(len(records))) - set(base5)
        )
        addition6 = greedy_individual(
            holes6, set(range(len(records))) - set(base6)
        )
        addition6_pairs = greedy_pairs(
            holes6,
            tuple(pair for index, pair in enumerate(pairs) if index not in base6_pairs),
        )
        selected5 = addition5["selected_class_ids"]
        selected6 = addition6["selected_class_ids"]
        results.append(
            {
                "order": order,
                "graphs": graph_count,
                "cover5_holes": len(holes5),
                "cover6_holes": len(holes6),
                "cover5_plus_individual_greedy": {
                    "base_size": len(base5),
                    "added_size": len(selected5),
                    "total_size": len(base5) + len(selected5),
                    "added": describe_classes(selected5, records),
                    "gains": addition5["new_holes_covered"],
                },
                "cover6_plus_individual_greedy": {
                    "base_size": len(base6),
                    "added_size": len(selected6),
                    "total_size": len(base6) + len(selected6),
                    "added": describe_classes(selected6, records),
                    "gains": addition6["new_holes_covered"],
                },
                "cover6_plus_complement_pairs_greedy": {
                    "base_pairs": 3,
                    "added_pairs": len(addition6_pairs["selected_pair_ids"]),
                    "total_pairs": 3 + len(addition6_pairs["selected_pair_ids"]),
                    "total_motifs": 2 * (
                        3 + len(addition6_pairs["selected_pair_ids"])
                    ),
                    "added": [
                        [
                            {"class_id_zero_based": class_id, "graph6": records[class_id]}
                            for class_id in pair
                        ]
                        for pair in addition6_pairs["selected_class_pairs"]
                    ],
                    "gains": addition6_pairs["new_holes_covered"],
                },
                "elapsed_seconds": time.perf_counter() - scan_started,
            }
        )

    return {
        "schema_version": 1,
        "status": "CATALOGUE_RELATIVE_GREEDY_PILOT",
        "proof_level": 1,
        "scope_warning": (
            "Greedy upper covers of two frozen official catalogues. Minimality, "
            "universal completeness, independent replay, and formalization are not claimed."
        ),
        "source7": {
            "path": str(source7),
            "bytes": source7.stat().st_size,
            "sha256": scan.sha256(source7),
            "classes": len(records),
            "labelled_graphs": len(owner_all),
            "complement_pairs": len(pairs),
        },
        "catalogues": results,
        "elapsed_seconds": time.perf_counter() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source7", type=Path, required=True)
    parser.add_argument("--source10", type=Path, required=True)
    parser.add_argument("--source11", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run(
        args.source7,
        ((10, args.source10), (11, args.source11)),
    )
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        if args.output.exists():
            raise FileExistsError(f"refusing to replace pilot report: {args.output}")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
