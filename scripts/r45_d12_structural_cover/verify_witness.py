#!/usr/bin/env python3
"""Independent verifier for the compact cover9 witness certificate."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import shutil
import struct
from pathlib import Path
from typing import Sequence

from . import structural_cover
from . import verify_cover9


HEADER = struct.Struct("<8sQII")
MAGIC = b"R44WIT1\0"
EXPECTED_WITNESS_SHA256: str | None = "A5C8BFC67618FB5345AD072E07237271390068B0883C12B04D4B0BEE4E379B96"


def decode_short_graph6_mask(record: str, order: int) -> int:
    """Decode graph6 independently of the native scanner and ramsey.py."""
    record = record.strip()
    if not record or ord(record[0]) - 63 != order:
        raise ValueError(f"wrong graph6 order: {record!r}")
    edge_count = order * (order - 1) // 2
    payload_count = (edge_count + 5) // 6
    if len(record) != 1 + payload_count:
        raise ValueError(f"wrong graph6 length: {record!r}")
    result = 0
    position = 0
    for char in record[1:]:
        value = ord(char) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 payload: {record!r}")
        for payload_bit in range(5, -1, -1):
            if position < edge_count and (value >> payload_bit) & 1:
                result |= 1 << position
            position += 1
    if position < edge_count:
        raise ValueError("truncated graph6 record")
    return result


def edge_position(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


def relabelled_mask(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    local_position = 0
    for right in range(1, len(permutation)):
        for left in range(right):
            source_position = edge_position(permutation[left], permutation[right])
            if (mask >> source_position) & 1:
                result |= 1 << local_position
            local_position += 1
    return result


def subset_positions() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(vertices[left], vertices[right])
            for right in range(1, 7)
            for left in range(right)
        )
        for vertices in itertools.combinations(range(12), 7)
    )


def induced_mask(graph_mask: int, positions: Sequence[int]) -> int:
    result = 0
    for local_position, source_position in enumerate(positions):
        if (graph_mask >> source_position) & 1:
            result |= 1 << local_position
    return result


def read_header(stream) -> tuple[int, tuple[str, ...], int]:
    raw = stream.read(HEADER.size)
    if len(raw) != HEADER.size:
        raise ValueError("truncated witness header")
    magic, graph_count, candidate_count, subset_count = HEADER.unpack(raw)
    if magic != MAGIC or subset_count != 792:
        raise ValueError("invalid witness header")
    records = []
    for _ in range(candidate_count):
        raw_record = stream.read(24)
        if len(raw_record) != 24:
            raise ValueError("truncated witness candidate table")
        records.append(raw_record.split(b"\0", 1)[0].decode("ascii"))
    return graph_count, tuple(records), subset_count


def verify(source_directory: Path, witness_path: Path) -> dict[str, object]:
    sources = structural_cover.validate_source(source_directory, (7, 8, 12))
    witness_hash = structural_cover.sha256(witness_path)
    if EXPECTED_WITNESS_SHA256 is not None and witness_hash != EXPECTED_WITNESS_SHA256:
        raise ValueError("witness SHA-256 mismatch")
    candidates = verify_cover9.cover_records(Path(__file__).with_name("cover9.tsv"))
    candidate_masks = tuple(decode_short_graph6_mask(record, 7) for record in candidates)
    closures = tuple(
        {
            relabelled_mask(mask, permutation)
            for permutation in itertools.permutations(range(7))
        }
        for mask in candidate_masks
    )
    positions = subset_positions()
    distribution = [0] * len(candidates)
    source12 = source_directory / "r44_12.g6"
    with witness_path.open("rb") as witness, source12.open("rt", encoding="ascii") as graphs:
        graph_count, embedded_candidates, subset_count = read_header(witness)
        if graph_count != structural_cover.EXPECTED_COUNTS[12]:
            raise ValueError("witness graph count mismatch")
        if embedded_candidates != candidates:
            raise ValueError("witness candidate table mismatch")
        for graph_index, record in enumerate(graphs):
            entry = witness.read(3)
            if len(entry) != 3:
                raise ValueError(f"truncated witness at graph {graph_index}")
            candidate_id = entry[0]
            subset_index = entry[1] | (entry[2] << 8)
            if candidate_id >= len(candidates):
                raise ValueError(f"invalid candidate id at graph {graph_index}")
            if subset_index >= subset_count:
                raise ValueError(f"invalid subset index at graph {graph_index}")
            graph_mask = decode_short_graph6_mask(record, 12)
            subgraph = induced_mask(graph_mask, positions[subset_index])
            if subgraph not in closures[candidate_id]:
                raise ValueError(
                    f"false induced-isomorphism witness at graph {graph_index}"
                )
            distribution[candidate_id] += 1
        if sum(distribution) != graph_count:
            raise ValueError("source graph count mismatch")
        if witness.read(1):
            raise ValueError("trailing bytes in witness certificate")
    return {
        "schema_version": 1,
        "status": "PASS",
        "format": {
            "magic": "R44WIT1\\0",
            "header": "little-endian <8sQII>, then 24 bytes per graph6 candidate",
            "entry": "3 bytes: uint8 candidate_id, uint16 little-endian subset7_index",
            "subset_order": "lexicographic itertools.combinations(range(12), 7)",
        },
        "source": sources["r44_12.g6"],
        "cover_sha256": verify_cover9.EXPECTED_COVER_SHA256,
        "witness": {
            "path": str(witness_path),
            "sha256": witness_hash,
            "bytes": witness_path.stat().st_size,
            "entries": graph_count,
            "candidate_distribution": distribution,
        },
        "verification": {
            "algorithm": (
                "independent Python graph6 decoder; exact 7! labelled closure "
                "for each motif; direct 21-edge check for every recorded subset"
            ),
            "valid_entries": graph_count,
            "invalid_entries": 0,
        },
        "scope": "catalogue-relative structural cover only; no SAT/gluing claim",
    }


def corruption_test(
    source_directory: Path,
    witness_path: Path,
    temporary_path: Path,
) -> dict[str, object]:
    shutil.copyfile(witness_path, temporary_path)
    try:
        with temporary_path.open("r+b") as stream:
            graph_count, candidates, _subset_count = read_header(stream)
            if not graph_count or not candidates:
                raise ValueError("cannot corrupt empty certificate")
            first_entry = HEADER.size + 24 * len(candidates)
            stream.seek(first_entry)
            stream.write(b"\xff")
        rejected = False
        message = ""
        try:
            verify(source_directory, temporary_path)
        except ValueError as error:
            rejected = True
            message = str(error)
        if not rejected:
            raise AssertionError("corrupted witness was accepted")
        return {"status": "PASS", "corruption_rejected": True, "error": message}
    finally:
        temporary_path.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--witness", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--corruption-test", type=Path)
    args = parser.parse_args()
    report = verify(args.source, args.witness)
    if args.corruption_test:
        report["corruption_test"] = corruption_test(
            args.source, args.witness, args.corruption_test
        )
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
