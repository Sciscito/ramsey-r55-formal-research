#!/usr/bin/env python3
"""Audit frozen mixed-order covers against native full-catalogue incidence.

The incidence products are deliberately external to the repository.  This
module checks their hashes, maps every frozen graph6 record back to the
official catalogues, proves zero uncovered bits, and reports irredundancy.
It makes no minimum-cardinality or R(4,5,25) claim.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

from scripts.r45_d12_structural_cover import structural_cover


HERE = Path(__file__).resolve().parent
EXPECTED_INCIDENCE = {
    "expanded": "C8161ED13F099103EA830CD79394E62E8EC6A5E4197E5B22E232C6B36C7304DB",
    "all_order7": "B14A1693C28CFED8965149ADB8C4410B993F86688466BC18736089E7D6735523",
}


def cover_records(path: Path) -> tuple[tuple[int, str], ...]:
    result: list[tuple[int, str]] = []
    phase8 = False
    for line_number, line in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"{path}:{line_number}: expected order and graph6")
        order, record = int(fields[0]), fields[1]
        if order not in (7, 8):
            raise ValueError(f"{path}:{line_number}: unsupported order {order}")
        if order == 7 and phase8:
            raise ValueError("order-7 records must precede order-8 records")
        phase8 |= order == 8
        graph = structural_cover.ramsey.decode_graph6(record)
        if len(graph) != order:
            raise ValueError(f"{path}:{line_number}: graph6 order mismatch")
        result.append((order, record))
    if not result or len(result) > 255 or len(set(result)) != len(result):
        raise ValueError("cover must contain 1..255 distinct records")
    return tuple(result)


def official_membership(source: Path, records: Iterable[tuple[int, str]]) -> None:
    catalogues = {
        order: structural_cover.records(source / f"r44_{order}.g6")
        for order in (7, 8)
    }
    for order, record in records:
        if catalogues[order].count(record) != 1:
            raise ValueError(f"record is not unique in official order-{order} catalogue: {record}")
        graph = structural_cover.ramsey.decode_graph6(record)
        if structural_cover.ramsey.count_cliques(graph, 4):
            raise ValueError(f"motif contains K4: {record}")
        complement = structural_cover.ramsey.complement_graph(graph)
        if structural_cover.ramsey.count_cliques(complement, 4):
            raise ValueError(f"motif contains an independent K4: {record}")


def verify(source: Path, incidence_path: Path, cover_path: Path) -> dict[str, object]:
    sources = structural_cover.validate_source(source, (7, 8, 12))
    digest = structural_cover.sha256(incidence_path)
    if digest not in EXPECTED_INCIDENCE.values():
        raise ValueError(f"unrecognized full-incidence SHA-256: {digest}")
    incidence = structural_cover.read_incidence(incidence_path)
    if incidence.graph_count != structural_cover.EXPECTED_COUNTS[12]:
        raise ValueError("incidence is not for the complete order-12 catalogue")
    records = cover_records(cover_path)
    official_membership(source, records)
    lookup = {
        (7 if index < incidence.count7 else 8, record): index
        for index, record in enumerate(incidence.graph6)
    }
    try:
        selected = tuple(lookup[item] for item in records)
    except KeyError as error:
        raise ValueError(f"cover record absent from incidence: {error.args[0]}") from error
    missing = structural_cover.uncovered_bits(incidence, selected)
    if missing:
        raise ValueError(f"cover leaves {missing.bit_count()} catalogue records uncovered")
    removal_holes = tuple(
        structural_cover.uncovered_bits(
            incidence, (candidate for candidate in selected if candidate != removed)
        ).bit_count()
        for removed in selected
    )
    if any(count == 0 for count in removal_holes):
        raise ValueError("cover is not irredundant")
    rows = []
    for (order, record), index, holes in zip(records, selected, removal_holes, strict=True):
        rows.append(
            {
                "order": order,
                "graph6": record,
                "edges": structural_cover.edge_count(record),
                "incidence_candidate_index_zero_based": index,
                "individual_coverage": incidence.covers[index].bit_count(),
                "holes_if_removed": holes,
            }
        )
    return {
        "schema_version": 1,
        "status": "PASS",
        "claim": (
            "Every frozen official R(4,4,12) catalogue record contains an "
            "induced raw-graph6 copy of at least one listed motif."
        ),
        "scope_warning": (
            "Catalogue-relative structural certificate only; no minimum-cover, "
            "catalogue-completeness, SAT-unsatisfiability, or R(4,5,25) claim."
        ),
        "sources": sources,
        "incidence": {
            "path": str(incidence_path),
            "sha256": digest,
            "catalogue_records": incidence.graph_count,
            "candidate_pool": len(incidence.covers),
            "candidate_order7": incidence.count7,
            "candidate_order8": incidence.count8,
            "uncovered": 0,
        },
        "cover": {
            "path": str(cover_path),
            "sha256": structural_cover.sha256(cover_path),
            "size": len(records),
            "order7": sum(order == 7 for order, _ in records),
            "order8": sum(order == 8 for order, _ in records),
            "irredundant": True,
            "records": rows,
        },
        "color_convention": "raw graph6 edge = positive DIMACS/red when benchmarked",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--incidence", type=Path, required=True)
    parser.add_argument("--cover", type=Path, default=HERE / "cover7_mixed.tsv")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = verify(args.source, args.incidence, args.cover)
    if args.report:
        structural_cover.ensure_ssd(args.report)
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
