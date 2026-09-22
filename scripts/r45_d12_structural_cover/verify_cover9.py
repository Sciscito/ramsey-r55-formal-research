#!/usr/bin/env python3
"""Verify the compact nine-pattern induced cover and its native incidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from . import structural_cover


EXPECTED_COVER_SHA256 = "5A2B4F3824FFFEF9BC6048C0B881F5BC7E2C90D85024485422C7A9B096EF5B12"
EXPECTED_INCIDENCE_SHA256 = "D5E50DFF135023BF934D75078DDA74173C182EDB49B7048B207A6A1046EB83BC"
EXPECTED_RECORDS = (
    "FiIXw",
    "FANbw",
    "F@Y]w",
    "FqhXw",
    "FFhmw",
    "FqHXw",
    "FQl~_",
    "FIiZw",
    "Fqoxw",
)
EXPECTED_EDGES = (11, 11, 11, 12, 13, 11, 13, 12, 12)
EXPECTED_REMOVAL_HOLES = (6, 50, 12, 9, 1, 5, 1, 1, 1)


def cover_records(path: Path) -> tuple[str, ...]:
    result = []
    for line in path.read_text(encoding="ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        order, record = line.split()
        if order != "7":
            raise ValueError("cover9 must contain order-7 records only")
        result.append(record)
    return tuple(result)


def verify(source_directory: Path, incidence_path: Path) -> dict[str, object]:
    cover_path = Path(__file__).with_name("cover9.tsv")
    if structural_cover.sha256(cover_path) != EXPECTED_COVER_SHA256:
        raise ValueError("cover9.tsv SHA-256 mismatch")
    if structural_cover.sha256(incidence_path) != EXPECTED_INCIDENCE_SHA256:
        raise ValueError("incidence SHA-256 mismatch")
    sources = structural_cover.validate_source(source_directory, (7, 8, 12))
    selected = cover_records(cover_path)
    if selected != EXPECTED_RECORDS:
        raise ValueError("cover record mismatch")
    source7 = structural_cover.records(source_directory / "r44_7.g6")
    for record, expected_edges in zip(selected, EXPECTED_EDGES, strict=True):
        if source7.count(record) != 1:
            raise ValueError(f"cover record does not occur exactly once: {record}")
        graph = structural_cover.ramsey.decode_graph6(record)
        if structural_cover.ramsey.graph_edge_count(graph) != expected_edges:
            raise ValueError(f"edge count mismatch: {record}")
        if structural_cover.ramsey.count_cliques(graph, 4):
            raise ValueError(f"cover record contains K4: {record}")
        complement = structural_cover.ramsey.complement_graph(graph)
        if structural_cover.ramsey.count_cliques(complement, 4):
            raise ValueError(f"cover record contains independent K4: {record}")
    incidence = structural_cover.read_incidence(incidence_path)
    if incidence.graph_count != structural_cover.EXPECTED_COUNTS[12]:
        raise ValueError("incidence does not cover the complete source catalogue")
    if (incidence.count7, incidence.count8, incidence.graph6) != (9, 0, selected):
        raise ValueError("incidence candidate header mismatch")
    uncovered = structural_cover.uncovered_bits(incidence, range(9))
    if uncovered:
        raise ValueError(f"cover has {uncovered.bit_count()} uncovered records")
    removal_holes = tuple(
        structural_cover.uncovered_bits(
            incidence, (candidate for candidate in range(9) if candidate != removed)
        ).bit_count()
        for removed in range(9)
    )
    if removal_holes != EXPECTED_REMOVAL_HOLES:
        raise ValueError(f"irredundancy counts changed: {removal_holes}")
    return {
        "schema_version": 1,
        "status": "PASS",
        "theorem_checked": (
            "Every one of the 1,449,166 catalogue representatives in "
            "R(4,4,12) contains, as a raw-graph6 induced subgraph, at least "
            "one of the nine listed R(4,4,7) representatives."
        ),
        "sources": sources,
        "cover": {
            "path": str(cover_path),
            "sha256": EXPECTED_COVER_SHA256,
            "records": list(selected),
            "edge_counts": list(EXPECTED_EDGES),
            "size": 9,
        },
        "incidence": {
            "path": str(incidence_path),
            "sha256": EXPECTED_INCIDENCE_SHA256,
            "catalogue_records": incidence.graph_count,
            "covered_records": incidence.graph_count,
            "uncovered_records": 0,
            "individual_coverage": [cover.bit_count() for cover in incidence.covers],
            "removal_holes": list(removal_holes),
            "padding_bits_zero": True,
        },
        "minimality": (
            "The displayed cover is irredundant. No claim that nine is the "
            "minimum possible cover size is made."
        ),
        "historical_comparison": (
            "McKay--Radziszowski (1995) report 23 order-7 plus 51 order-8 "
            "patterns optimized for their gluing computation; their exact "
            "list was not published. This nine-pattern list was found "
            "independently as a cardinality-oriented reconstruction. No "
            "indexed prior match was found in the limited audit, but that "
            "audit is incomplete; this is not claimed to be the historical list."
        ),
        "computational_scope": (
            "This certifies only the structural R(4,4,12) cover. It does not "
            "certify that the resulting R(4,5,25) gluing/SAT leaves are easy "
            "or unsatisfiable."
        ),
        "color_convention": {
            "checked_relation": "raw graph6 adjacency",
            "current_dimacs_if_imported": "edge = positive literal = red",
            "hol4_numeric": "1 = blue, 2 = red",
            "complement_required_between_opposite_edge-color_conventions": True,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--incidence", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = verify(args.source, args.incidence)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
