#!/usr/bin/env python3
"""Pilot the existing order-seven motif covers on R(4,4;10/11).

This is deliberately a catalogue-relative, proof-free screen.  It reads the
official compressed graph6 catalogues, rebuilds the labelled closures of the
tracked cover5 and complement-closed cover6, and checks every order-seven
induced subgraph until both families have been found or the graph is exhausted.

The result is evidence for choosing a K45 branch representation.  It is not a
universal graph theorem and it proves no Ramsey-number bound.
"""

from __future__ import annotations

import argparse
import functools
import gzip
import hashlib
import itertools
import json
import time
from pathlib import Path
from typing import Iterable, Sequence

from scripts.r45_d12_complement_closed_minimum import verify_cover6 as cover6
from scripts.r45_d12_cover9_universal import generate_complement_closed_cover5 as cover5


CATALOGUES = {
    10: {
        "graphs": 103_706,
        "compressed_bytes": 443_274,
        "compressed_sha256": "C34980E1CE734573D3A92486C6071144E154EE53E049B0E050CB1F8FFE0F6691",
    },
    11: {
        "graphs": 546_356,
        "compressed_bytes": 2_605_345,
        "compressed_sha256": "05EEC90C5C14659E31F5E2C31A810B75649BA7D670D01A079ED9AABF17A3BBBC",
    },
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def build_cover5_owner() -> dict[int, int]:
    records = cover5.read_records()
    orbits = tuple(
        cover5.labelled_orbit(cover5.decode_graph6(record)) for record in records
    )
    if tuple(map(len, orbits)) != cover5.EXPECTED_RAW_ORBIT_SIZES:
        raise ValueError("cover5 labelled orbit sizes changed")
    owner: dict[int, int] = {}
    for motif, orbit in enumerate(orbits):
        for mask in orbit:
            previous = owner.setdefault(mask, motif)
            if previous != motif:
                raise ValueError("cover5 motif classes overlap")
    if len(owner) != cover5.EXPECTED_RAW_CLOSURE:
        raise ValueError("cover5 labelled closure size changed")
    return owner


@functools.cache
def subset_positions(order: int) -> tuple[tuple[int, ...], ...]:
    if order < 7:
        raise ValueError("the host order must be at least seven")
    return tuple(
        tuple(
            cover6.edge_position(vertices[left], vertices[right])
            for right in range(1, 7)
            for left in range(right)
        )
        for vertices in itertools.combinations(range(order), 7)
    )


def scan_catalogue(
    source: Path,
    order: int,
    owner5: dict[int, int],
    owner6: dict[int, int],
    *,
    witness_limit: int = 20,
) -> dict[str, object]:
    if order not in CATALOGUES:
        raise ValueError(f"unsupported catalogue order: {order}")
    expected = CATALOGUES[order]
    observed_identity = (source.stat().st_size, sha256(source))
    expected_identity = (expected["compressed_bytes"], expected["compressed_sha256"])
    if observed_identity != expected_identity:
        raise ValueError(
            f"R(4,4;{order}) compressed identity mismatch: "
            f"{observed_identity} != {expected_identity}"
        )

    positions = subset_positions(order)
    started = time.perf_counter()
    graph_count = 0
    subsets_examined = 0
    covered5 = 0
    covered6 = 0
    first5 = [0] * len(cover5.EXPECTED_RECORDS)
    first6 = [0] * len(cover6.EXPECTED_RECORDS)
    holes5: list[dict[str, object]] = []
    holes6: list[dict[str, object]] = []

    with gzip.open(source, "rt", encoding="ascii", newline="") as stream:
        for graph_index, raw_line in enumerate(stream):
            record = raw_line.strip()
            graph = cover6.decode_graph6(record, order)
            hit5: int | None = None
            hit6: int | None = None
            for edge_positions in positions:
                induced = cover6.induced_mask(graph, edge_positions)
                subsets_examined += 1
                if hit5 is None:
                    hit5 = owner5.get(induced)
                if hit6 is None:
                    hit6 = owner6.get(induced)
                if hit5 is not None and hit6 is not None:
                    break
            if hit5 is None:
                if len(holes5) < witness_limit:
                    holes5.append({"index_zero_based": graph_index, "graph6": record})
            else:
                covered5 += 1
                first5[hit5] += 1
            if hit6 is None:
                if len(holes6) < witness_limit:
                    holes6.append({"index_zero_based": graph_index, "graph6": record})
            else:
                covered6 += 1
                first6[hit6] += 1
            graph_count += 1

    if graph_count != expected["graphs"]:
        raise ValueError(
            f"R(4,4;{order}) record count mismatch: {graph_count} != {expected['graphs']}"
        )
    elapsed = time.perf_counter() - started
    return {
        "order": order,
        "source": {
            "path": str(source),
            "compressed_bytes": observed_identity[0],
            "compressed_sha256": observed_identity[1],
            "graphs": graph_count,
        },
        "subsets_per_graph": len(positions),
        "subsets_examined_until_both_hit_or_exhausted": subsets_examined,
        "cover5": {
            "records": list(cover5.EXPECTED_RECORDS),
            "covered": covered5,
            "uncovered": graph_count - covered5,
            "first_hit_distribution": first5,
            "first_uncovered_witnesses": holes5,
        },
        "cover6": {
            "records": list(cover6.EXPECTED_RECORDS),
            "covered": covered6,
            "uncovered": graph_count - covered6,
            "first_hit_distribution": first6,
            "first_uncovered_witnesses": holes6,
        },
        "elapsed_seconds": elapsed,
    }


def run(sources: Iterable[tuple[int, Path]]) -> dict[str, object]:
    started = time.perf_counter()
    owner5 = build_cover5_owner()
    orbits6, owner6 = cover6.build_closure()
    results = [
        scan_catalogue(path, order, owner5, owner6) for order, path in sources
    ]
    return {
        "schema_version": 1,
        "status": "CATALOGUE_RELATIVE_PILOT",
        "proof_level": 1,
        "scope_warning": (
            "The scan is relative to two frozen official catalogues and uses no "
            "certificate or formal semantic bridge. It proves no new Ramsey bound."
        ),
        "cover5": {
            "source_sha256": cover5.EXPECTED_COVER_SHA256,
            "labelled_closure": len(owner5),
            "complement_closed": False,
        },
        "cover6": {
            "source_sha256": cover6.EXPECTED_COVER_SHA256,
            "labelled_closure": len(owner6),
            "orbit_sizes": list(map(len, orbits6)),
            "complement_closed": True,
        },
        "catalogues": results,
        "elapsed_seconds": time.perf_counter() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source10", type=Path, required=True)
    parser.add_argument("--source11", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run(((10, args.source10), (11, args.source11)))
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        if args.output.exists():
            raise FileExistsError(f"refusing to replace pilot report: {args.output}")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
