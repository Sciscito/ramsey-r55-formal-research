#!/usr/bin/env python3
"""Prepare a thresholded R(4,4,7/8) candidate pool on the external SSD."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from . import structural_cover


def prepare(
    source: Path,
    output: Path,
    *,
    minimum_edges7: int,
    minimum_edges8: int,
) -> dict[str, object]:
    output = structural_cover.ensure_ssd(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    sources = structural_cover.validate_source(source, (7, 8, 12))
    selected: list[structural_cover.PoolRecord] = []
    for order, threshold in ((7, minimum_edges7), (8, minimum_edges8)):
        selected.extend(
            structural_cover.PoolRecord(order, record, structural_cover.edge_count(record))
            for record in structural_cover.records(source / f"r44_{order}.g6")
            if structural_cover.edge_count(record) >= threshold
        )
    count7 = sum(item.order == 7 for item in selected)
    count8 = len(selected) - count7
    if not count7 or not count8 or len(selected) > 1024:
        raise ValueError(f"unsupported pool dimensions: {count7}+{count8}")
    output.write_text(
        "# raw graph6 adjacency; order-7 candidates precede order-8 candidates\n"
        + "".join(f"{item.order}\t{item.graph6}\n" for item in selected),
        encoding="ascii",
        newline="\n",
    )
    report = {
        "schema_version": 1,
        "sources": sources,
        "output": str(output),
        "sha256": structural_cover.sha256(output),
        "minimum_edges7": minimum_edges7,
        "minimum_edges8": minimum_edges8,
        "order7": count7,
        "order8": count8,
        "total": len(selected),
        "relation": "raw graph6 adjacency",
        "historical_status": "new threshold reconstruction, not the unpublished list",
    }
    output.with_suffix(".json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--minimum-edges7", type=int, required=True)
    parser.add_argument("--minimum-edges8", type=int, required=True)
    args = parser.parse_args()
    print(
        json.dumps(
            prepare(
                args.source,
                args.output,
                minimum_edges7=args.minimum_edges7,
                minimum_edges8=args.minimum_edges8,
            ),
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
