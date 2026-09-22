#!/usr/bin/env python3
"""Audit McKay's public R(4,4,7/8) catalogues by density."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from collections import Counter
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[2]
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"


def load_ramsey():
    spec = importlib.util.spec_from_file_location("d12_external_ramsey", RAMSEY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {RAMSEY_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ramsey = load_ramsey()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def report(directory: Path) -> dict[str, object]:
    result: dict[str, object] = {}
    for order, requested in ((7, 23), (8, 51)):
        path = directory / f"r44_{order}.g6"
        records = tuple(
            line.strip()
            for line in path.read_text(encoding="ascii").splitlines()
            if line.strip()
        )
        graphs = tuple(ramsey.decode_graph6(record) for record in records)
        if any(len(graph) != order for graph in graphs):
            raise ValueError(f"wrong order in {path}")
        if any(
            ramsey.count_cliques(graph, 4)
            or ramsey.count_cliques(ramsey.complement_graph(graph), 4)
            for graph in graphs
        ):
            raise ValueError(f"non-R(4,4) graph in {path}")
        ranked = sorted(
            zip(records, graphs, strict=True),
            key=lambda item: (-ramsey.graph_edge_count(item[1]), item[0]),
        )
        threshold = ramsey.graph_edge_count(ranked[requested - 1][1])
        result[str(order)] = {
            "path": str(path),
            "sha256": sha256(path),
            "records": len(records),
            "edge_count_distribution": dict(sorted(Counter(
                ramsey.graph_edge_count(graph) for graph in graphs
            ).items())),
            "paper_cover_count": requested,
            "top_count_edge_threshold": threshold,
            "strictly_denser_than_threshold": sum(
                ramsey.graph_edge_count(graph) > threshold
                for _record, graph in ranked
            ),
            "all_at_threshold": sum(
                ramsey.graph_edge_count(graph) == threshold
                for _record, graph in ranked
            ),
            "top_records": [record for record, _graph in ranked[:requested]],
        }
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(report(args.directory), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
