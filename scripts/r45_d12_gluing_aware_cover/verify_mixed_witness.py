#!/usr/bin/env python3
"""Independent replay of the R44MWI1 mixed-order cover witness."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import shutil
import struct
from pathlib import Path
from typing import Sequence

from scripts.r45_d12_gluing_aware_cover import cover_audit
from scripts.r45_d12_structural_cover import structural_cover


HEADER = struct.Struct("<8sQIIII")
MAGIC = b"R44MWI1\0"
EXPECTED_WITNESS_BY_COVER = {
    "C896124FF97206B5CB43E89916243B9A2378A6A65614EB03429E6E5686C9580E":
        "0F0E551A8D8357E9CE3B132F5989CD0610A2D9A876BF453531144CD330FE0C3F",
    "CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288":
        "36EC5E95D8599F6AE8099A6D3376D0E3F43269059FC644A1A3F96C52846414CB",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def decode_graph6_mask(record: str, order: int) -> int:
    record = record.strip()
    edge_count = order * (order - 1) // 2
    if not record or ord(record[0]) - 63 != order or len(record) != 1 + (edge_count + 5) // 6:
        raise ValueError(f"wrong graph6 order or length: {record!r}")
    result = 0
    position = 0
    for char in record[1:]:
        value = ord(char) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 payload: {record!r}")
        for bit in range(5, -1, -1):
            if position < edge_count and (value >> bit) & 1:
                result |= 1 << position
            position += 1
    return result


def edge_position(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


def relabelled_mask(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    local = 0
    for right in range(1, len(permutation)):
        for left in range(right):
            if (mask >> edge_position(permutation[left], permutation[right])) & 1:
                result |= 1 << local
            local += 1
    return result


def subset_positions(order: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(vertices[left], vertices[right])
            for right in range(1, order)
            for left in range(right)
        )
        for vertices in itertools.combinations(range(12), order)
    )


def induced_mask(graph_mask: int, positions: Sequence[int]) -> int:
    result = 0
    for local, source in enumerate(positions):
        if (graph_mask >> source) & 1:
            result |= 1 << local
    return result


def read_header(stream) -> tuple[int, tuple[tuple[int, str], ...]]:
    raw = stream.read(HEADER.size)
    if len(raw) != HEADER.size:
        raise ValueError("truncated mixed witness header")
    magic, graph_count, candidate_count, subsets7, subsets8, entry_size = HEADER.unpack(raw)
    if magic != MAGIC or (subsets7, subsets8, entry_size) != (792, 495, 24):
        raise ValueError("invalid mixed witness header")
    candidates: list[tuple[int, str]] = []
    for _ in range(candidate_count):
        raw_entry = stream.read(entry_size)
        if len(raw_entry) != entry_size:
            raise ValueError("truncated candidate table")
        order = raw_entry[0]
        record = raw_entry[1:].split(b"\0", 1)[0].decode("ascii")
        if order not in (7, 8):
            raise ValueError("invalid candidate order")
        candidates.append((order, record))
    return graph_count, tuple(candidates)


def verify(
    source_directory: Path,
    witness_path: Path,
    cover_path: Path,
    *,
    check_frozen_hash: bool = True,
) -> dict[str, object]:
    sources = structural_cover.validate_source(source_directory, (7, 8, 12))
    cover_hash = sha256(cover_path)
    witness_hash = sha256(witness_path)
    if check_frozen_hash:
        expected_hash = EXPECTED_WITNESS_BY_COVER.get(cover_hash)
        if expected_hash is None or witness_hash != expected_hash:
            raise ValueError(f"witness SHA-256 mismatch: {witness_hash}")
    candidates = cover_audit.cover_records(cover_path)
    closures = tuple(
        {
            relabelled_mask(decode_graph6_mask(record, order), permutation)
            for permutation in itertools.permutations(range(order))
        }
        for order, record in candidates
    )
    positions = {7: subset_positions(7), 8: subset_positions(8)}
    distribution = [0] * len(candidates)
    source12 = source_directory / "r44_12.g6"
    with witness_path.open("rb") as witness, source12.open("rt", encoding="ascii") as graphs:
        graph_count, embedded = read_header(witness)
        if graph_count != structural_cover.EXPECTED_COUNTS[12] or embedded != candidates:
            raise ValueError("witness source count or candidate table mismatch")
        for graph_index, record in enumerate(graphs):
            entry = witness.read(3)
            if len(entry) != 3:
                raise ValueError(f"truncated witness at graph {graph_index}")
            candidate_id = entry[0]
            subset_index = entry[1] | entry[2] << 8
            if candidate_id >= len(candidates):
                raise ValueError(f"invalid candidate id at graph {graph_index}")
            order = candidates[candidate_id][0]
            if subset_index >= len(positions[order]):
                raise ValueError(f"invalid order-{order} subset index at graph {graph_index}")
            graph_mask = decode_graph6_mask(record, 12)
            induced = induced_mask(graph_mask, positions[order][subset_index])
            if induced not in closures[candidate_id]:
                raise ValueError(f"false mixed induced witness at graph {graph_index}")
            distribution[candidate_id] += 1
        if sum(distribution) != graph_count:
            raise ValueError("source graph count mismatch")
        if witness.read(1):
            raise ValueError("trailing witness bytes")
    return {
        "schema_version": 1,
        "status": "PASS",
        "sources": sources,
        "cover": {"path": str(cover_path), "sha256": cover_hash, "records": candidates},
        "witness": {
            "path": str(witness_path),
            "sha256": witness_hash,
            "bytes": witness_path.stat().st_size,
            "entries": graph_count,
            "candidate_distribution": distribution,
        },
        "verification": (
            "independent graph6 decoder; explicit 7!/8! labelled closures; "
            "direct replay of every order-aware subset witness"
        ),
        "scope": "catalogue-relative structural cover only",
    }


def corruption_test(source: Path, witness: Path, cover: Path, temporary: Path) -> dict[str, object]:
    shutil.copyfile(witness, temporary)
    try:
        with temporary.open("r+b") as stream:
            _count, candidates = read_header(stream)
            stream.seek(HEADER.size + 24 * len(candidates))
            stream.write(b"\xff")
        try:
            verify(source, temporary, cover, check_frozen_hash=False)
        except ValueError as error:
            return {"status": "PASS", "corruption_rejected": True, "error": str(error)}
        raise AssertionError("corrupted mixed witness was accepted")
    finally:
        temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--witness", type=Path, required=True)
    parser.add_argument("--cover", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--corruption-test", type=Path)
    args = parser.parse_args()
    report = verify(args.source, args.witness, args.cover)
    if args.corruption_test:
        report["corruption_test"] = corruption_test(args.source, args.witness, args.cover, args.corruption_test)
    if args.report:
        structural_cover.ensure_ssd(args.report)
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
