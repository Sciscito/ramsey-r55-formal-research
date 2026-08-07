#!/usr/bin/env python3
"""Prepare and audit induced-subgraph covers of the R(4,4,12) catalogue.

The native scanner writes candidate incidence bitsets.  This module keeps
source hashing, candidate policy, set-cover heuristics, and JSON reporting in
small readable Python.  Heavy outputs are restricted to an absolute S: path.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import struct
import sys
from dataclasses import dataclass
from pathlib import Path, PureWindowsPath
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"

EXPECTED_HASHES = {
    "r44_7.g6": "6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010",
    "r44_8.g6": "B27389F7B1C70F823161A2CCA629BED3F4FBF058A43907637C0F9CE2E0CC4AB3",
    "r44_12.g6": "C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A",
}
EXPECTED_COUNTS = {7: 362, 8: 2079, 12: 1_449_166}
HEADER = struct.Struct("<8sQQQQIIII")
MAGIC = b"R44COV1\0"


def load_ramsey_module():
    spec = importlib.util.spec_from_file_location("r44_cover_ramsey", RAMSEY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {RAMSEY_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ramsey = load_ramsey_module()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def ensure_ssd(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise ValueError(f"heavy artifact path must be absolute on S:, got {path}")
    return path


def records(path: Path) -> tuple[str, ...]:
    return tuple(
        line.strip()
        for line in path.read_text(encoding="ascii").splitlines()
        if line.strip()
    )


def edge_count(record: str) -> int:
    return ramsey.graph_edge_count(ramsey.decode_graph6(record))


def validate_source(directory: Path, orders: Iterable[int]) -> dict[str, object]:
    result: dict[str, object] = {}
    for order in orders:
        name = f"r44_{order}.g6"
        path = directory / name
        digest = sha256(path)
        with path.open("rb") as stream:
            count = sum(1 for line in stream if line.strip())
        if digest != EXPECTED_HASHES[name]:
            raise ValueError(f"unexpected SHA-256 for {name}: {digest}")
        if count != EXPECTED_COUNTS[order]:
            raise ValueError(f"unexpected record count for {name}: {count}")
        result[name] = {"sha256": digest, "records": count}
    return result


@dataclass(frozen=True)
class PoolRecord:
    order: int
    graph6: str
    edges: int


def dense_pool(directory: Path) -> tuple[PoolRecord, ...]:
    pool: list[PoolRecord] = []
    for order, threshold, expected in ((7, 13, 46), (8, 18, 53)):
        source_records = records(directory / f"r44_{order}.g6")
        if len(source_records) != EXPECTED_COUNTS[order]:
            raise ValueError(f"unexpected order-{order} catalogue size")
        selected = tuple(
            PoolRecord(order, record, edge_count(record))
            for record in source_records
            if edge_count(record) >= threshold
        )
        if len(selected) != expected:
            raise ValueError(f"unexpected dense order-{order} pool size")
        pool.extend(selected)
    return tuple(pool)


def prepare(directory: Path, output_directory: Path) -> dict[str, object]:
    output_directory = ensure_ssd(output_directory)
    output_directory.mkdir(parents=True, exist_ok=True)
    sources = validate_source(directory, (7, 8, 12))
    pool = dense_pool(directory)
    candidate_path = output_directory / "dense_candidates.tsv"
    candidate_path.write_text(
        "# order<TAB>graph6; raw graph6 adjacency, no color reinterpretation\n"
        + "".join(f"{item.order}\t{item.graph6}\n" for item in pool),
        encoding="ascii",
        newline="\n",
    )
    metadata = {
        "schema_version": 1,
        "sources": sources,
        "candidate_file": {
            "path": str(candidate_path),
            "sha256": sha256(candidate_path),
            "records": len(pool),
            "order7": sum(item.order == 7 for item in pool),
            "order8": sum(item.order == 8 for item in pool),
        },
        "candidate_policy": {
            "order7": "all R(4,4,7) records with at least 13 raw graph6 edges",
            "order8": "all R(4,4,8) records with at least 18 raw graph6 edges",
        },
        "color_convention": {
            "scanner": "raw graph6 adjacency only",
            "current_dimacs_if_imported": "graph6 edge -> positive literal -> red",
            "hol4_numeric": "1 = blue, 2 = red",
            "warning": "A HOL4 color-1/blue representation must be complemented before comparison with the current DIMACS-positive/red convention.",
        },
        "historical_status": "candidate reconstruction; not the unpublished 1995 list",
    }
    metadata_path = output_directory / "prepare.json"
    metadata_path.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return metadata


@dataclass(frozen=True)
class Incidence:
    graph_count: int
    words: int
    map8_unique: int
    map8_duplicates: int
    count7: int
    count8: int
    graph6: tuple[str, ...]
    covers: tuple[int, ...]


def read_incidence(path: Path) -> Incidence:
    data = path.read_bytes()
    if len(data) < HEADER.size:
        raise ValueError("truncated incidence header")
    (
        magic,
        graph_count,
        words,
        map8_unique,
        map8_duplicates,
        candidate_count,
        count7,
        count8,
        reserved,
    ) = HEADER.unpack_from(data)
    if magic != MAGIC or reserved != 0:
        raise ValueError("invalid incidence header")
    if candidate_count != count7 + count8:
        raise ValueError("candidate count mismatch")
    records_offset = HEADER.size
    bits_offset = records_offset + 24 * candidate_count
    expected_size = bits_offset + 8 * words * candidate_count
    if len(data) != expected_size:
        raise ValueError(f"incidence size mismatch: {len(data)} != {expected_size}")
    graph6 = tuple(
        data[records_offset + 24 * index : records_offset + 24 * (index + 1)]
        .split(b"\0", 1)[0]
        .decode("ascii")
        for index in range(candidate_count)
    )
    block_size = 8 * words
    covers = tuple(
        int.from_bytes(
            data[bits_offset + index * block_size : bits_offset + (index + 1) * block_size],
            "little",
        )
        for index in range(candidate_count)
    )
    if graph_count % 64:
        padding = ~((1 << graph_count) - 1)
        if any(cover & padding for cover in covers):
            raise ValueError("non-zero padding bits in final incidence word")
    return Incidence(
        graph_count,
        words,
        map8_unique,
        map8_duplicates,
        count7,
        count8,
        graph6,
        covers,
    )


def union(covers: Sequence[int], selected: Iterable[int]) -> int:
    result = 0
    for index in selected:
        result |= covers[index]
    return result


def uncovered_bits(incidence: Incidence, selected: Iterable[int]) -> int:
    universe = (1 << incidence.graph_count) - 1
    return universe & ~union(incidence.covers, selected)


def density_selection(incidence: Incidence) -> tuple[int, ...]:
    counts = tuple(edge_count(record) for record in incidence.graph6)
    order7 = sorted(range(incidence.count7), key=lambda index: (-counts[index], incidence.graph6[index]))[:23]
    order8 = sorted(
        range(incidence.count7, incidence.count7 + incidence.count8),
        key=lambda index: (-counts[index], incidence.graph6[index]),
    )[:51]
    return tuple(order7 + order8)


def greedy_selection(
    incidence: Incidence,
    *,
    cap7: int = 23,
    cap8: int = 51,
    initial: Iterable[int] = (),
) -> tuple[int, ...]:
    selected = list(dict.fromkeys(initial))
    chosen = set(selected)
    used7 = sum(index < incidence.count7 for index in selected)
    used8 = len(selected) - used7
    uncovered = uncovered_bits(incidence, selected)
    counts = tuple(edge_count(record) for record in incidence.graph6)
    while uncovered and used7 + used8 < cap7 + cap8:
        eligible = (
            index
            for index in range(len(incidence.covers))
            if index not in chosen
            and ((index < incidence.count7 and used7 < cap7) or (index >= incidence.count7 and used8 < cap8))
        )
        best = max(
            eligible,
            key=lambda index: (
                (incidence.covers[index] & uncovered).bit_count(),
                counts[index],
                tuple(-ord(char) for char in incidence.graph6[index]),
            ),
            default=None,
        )
        if best is None or not (incidence.covers[best] & uncovered):
            break
        selected.append(best)
        chosen.add(best)
        if best < incidence.count7:
            used7 += 1
        else:
            used8 += 1
        uncovered &= ~incidence.covers[best]
    return tuple(selected)


def prune_selection(incidence: Incidence, selected: Iterable[int]) -> tuple[int, ...]:
    current = list(dict.fromkeys(selected))
    changed = True
    while changed:
        changed = False
        for candidate in tuple(reversed(current)):
            trial = [index for index in current if index != candidate]
            if not uncovered_bits(incidence, trial):
                current = trial
                changed = True
    return tuple(current)


def first_set_bits(value: int, limit: int = 20) -> tuple[int, ...]:
    result: list[int] = []
    while value and len(result) < limit:
        low = value & -value
        result.append(low.bit_length() - 1)
        value ^= low
    return tuple(result)


def graph_records_at(path: Path, indices: Iterable[int]) -> dict[int, str]:
    wanted = set(indices)
    found: dict[int, str] = {}
    if not wanted:
        return found
    with path.open("rt", encoding="ascii") as stream:
        for index, line in enumerate(stream):
            if index in wanted:
                found[index] = line.strip()
                if len(found) == len(wanted):
                    break
    return found


def selection_report(incidence: Incidence, selected: Sequence[int], source12: Path) -> dict[str, object]:
    missing = uncovered_bits(incidence, selected)
    sample_indices = first_set_bits(missing)
    samples = graph_records_at(source12, sample_indices)
    return {
        "selected": len(selected),
        "selected_order7": sum(index < incidence.count7 for index in selected),
        "selected_order8": sum(index >= incidence.count7 for index in selected),
        "covered": incidence.graph_count - missing.bit_count(),
        "uncovered": missing.bit_count(),
        "first_uncovered": [
            {"catalogue_index_zero_based": index, "graph6": samples[index]}
            for index in sample_indices
        ],
        "records": [
            {
                "candidate_index_zero_based": index,
                "order": 7 if index < incidence.count7 else 8,
                "edges": edge_count(incidence.graph6[index]),
                "graph6": incidence.graph6[index],
            }
            for index in selected
        ],
    }


def analyze(incidence_path: Path, source_directory: Path, output_path: Path) -> dict[str, object]:
    output_path = ensure_ssd(output_path)
    sources = validate_source(source_directory, (7, 8, 12))
    incidence = read_incidence(incidence_path)
    if incidence.graph_count > EXPECTED_COUNTS[12]:
        raise ValueError("incidence graph count exceeds source catalogue")
    source12 = source_directory / "r44_12.g6"
    density = density_selection(incidence)
    greedy = greedy_selection(incidence)
    all_pruned = prune_selection(incidence, range(len(incidence.covers)))
    candidates = {
        "density_lexicographic_23_plus_51": density,
        "greedy_caps_23_plus_51": greedy,
        "all_pool_redundancy_pruned": all_pruned,
    }
    report = {
        "schema_version": 1,
        "sources": sources,
        "incidence": {
            "path": str(incidence_path),
            "sha256": sha256(incidence_path),
            "graph_count": incidence.graph_count,
            "complete_catalogue": incidence.graph_count == EXPECTED_COUNTS[12],
            "candidate_count": len(incidence.covers),
            "order7": incidence.count7,
            "order8": incidence.count8,
            "order8_labeled_closure_unique": incidence.map8_unique,
            "order8_duplicate_permutations": incidence.map8_duplicates,
        },
        "relation": "raw graph6 induced-subgraph isomorphism",
        "color_convention": {
            "scanner": "raw graph6 adjacency",
            "current_dimacs_if_imported": "edge = positive = red",
            "hol4_numeric": "1 = blue, 2 = red",
            "not_interchangeable_without_complement": True,
        },
        "historical_status": (
            "independent reconstruction; the exact 1995 list remains unpublished, "
            "and the limited indexed-source audit is incomplete"
        ),
        "selections": {
            name: selection_report(incidence, selection, source12)
            for name, selection in candidates.items()
        },
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    prepare_parser = commands.add_parser("prepare")
    prepare_parser.add_argument("--source", type=Path, required=True)
    prepare_parser.add_argument("--output", type=Path, required=True)
    analyze_parser = commands.add_parser("analyze")
    analyze_parser.add_argument("--incidence", type=Path, required=True)
    analyze_parser.add_argument("--source", type=Path, required=True)
    analyze_parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "prepare":
        result = prepare(args.source, args.output)
    else:
        result = analyze(args.incidence, args.source, args.output)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
