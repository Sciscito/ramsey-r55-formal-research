#!/usr/bin/env python3
"""Exact search for complement-closed order-seven covers of R(4,4,12).

This research driver reads the full column incidence matrix, reconstructs the
complement involution on the 362 official R(4,4,7) isomorphism classes, and
searches the resulting 181 paired candidates.  Heavy inputs and optional
reports must live on the external S: drive.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import struct
import time
from pathlib import Path, PureWindowsPath
from typing import Iterable, Sequence


HEADER = struct.Struct("<8sQQQQIIII")
MAGIC = b"R44COV1\0"
EXPECTED_INCIDENCE_SHA256 = (
    "B14A1693C28CFED8965149ADB8C4410B993F86688466BC18736089E7D6735523"
)
EXPECTED_GRAPH_COUNT = 1_449_166
EXPECTED_CANDIDATES = 362
N = 7
EDGE_COUNT = N * (N - 1) // 2
FULL7 = (1 << EDGE_COUNT) - 1


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def require_ssd(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise ValueError(f"heavy path must be absolute on S:, got {path}")
    return path


def decode_graph6(record: str) -> int:
    if len(record) != 5 or ord(record[0]) - 63 != N:
        raise ValueError(f"not an order-seven graph6 record: {record!r}")
    result = 0
    position = 0
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 payload: {record!r}")
        for shift in range(5, -1, -1):
            bit = value >> shift & 1
            if position < EDGE_COUNT:
                result |= bit << position
            elif bit:
                raise ValueError(f"nonzero graph6 padding: {record!r}")
            position += 1
    return result


def edge_position(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


@functools.cache
def permutation_edge_maps() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(permutation[left], permutation[right])
            for right in range(1, N)
            for left in range(right)
        )
        for permutation in itertools.permutations(range(N))
    )


def relabel(mask: int, edge_map: Sequence[int]) -> int:
    result = 0
    for target, source in enumerate(edge_map):
        result |= ((mask >> source) & 1) << target
    return result


def orbit_extrema(mask: int) -> tuple[int, int]:
    minimum = FULL7
    maximum = 0
    for edge_map in permutation_edge_maps():
        labelled = relabel(mask, edge_map)
        minimum = min(minimum, labelled)
        maximum = max(maximum, labelled)
    return minimum, maximum


def complement_involution(records: Sequence[str]) -> tuple[int, ...]:
    extrema = tuple(orbit_extrema(decode_graph6(record)) for record in records)
    canonical_to_id: dict[int, int] = {}
    for candidate, (minimum, _maximum) in enumerate(extrema):
        previous = canonical_to_id.setdefault(minimum, candidate)
        if previous != candidate:
            raise ValueError(f"duplicate isomorphism classes {previous} and {candidate}")
    result = tuple(canonical_to_id[FULL7 ^ maximum] for _minimum, maximum in extrema)
    if any(result[result[index]] != index for index in range(len(result))):
        raise ValueError("complement map is not an involution")
    if any(result[index] == index for index in range(len(result))):
        raise ValueError("unexpected self-complementary odd-edge class")
    if any(
        decode_graph6(records[index]).bit_count()
        + decode_graph6(records[result[index]]).bit_count()
        != EDGE_COUNT
        for index in range(len(result))
    ):
        raise ValueError("complement partners have inconsistent edge counts")
    return result


def read_incidence(path: Path) -> tuple[tuple[str, ...], tuple[int, ...], int]:
    require_ssd(path)
    digest = sha256(path)
    if digest != EXPECTED_INCIDENCE_SHA256:
        raise ValueError(f"incidence SHA-256 mismatch: {digest}")
    with path.open("rb") as stream:
        raw_header = stream.read(HEADER.size)
        if len(raw_header) != HEADER.size:
            raise ValueError("truncated incidence header")
        (
            magic,
            graph_count,
            words,
            _map8_unique,
            _map8_duplicates,
            candidate_count,
            count7,
            count8,
            reserved,
        ) = HEADER.unpack(raw_header)
        if magic != MAGIC or reserved != 0:
            raise ValueError("invalid incidence header")
        if (graph_count, candidate_count, count7, count8) != (
            EXPECTED_GRAPH_COUNT,
            EXPECTED_CANDIDATES,
            EXPECTED_CANDIDATES,
            0,
        ):
            raise ValueError("incidence dimensions are not the frozen full order-seven matrix")
        if words != (graph_count + 63) // 64:
            raise ValueError("incidence word count mismatch")
        records = []
        for _ in range(candidate_count):
            raw = stream.read(24)
            if len(raw) != 24:
                raise ValueError("truncated candidate table")
            records.append(raw.split(b"\0", 1)[0].decode("ascii"))
        block_bytes = 8 * words
        covers = []
        universe = (1 << graph_count) - 1
        for _ in range(candidate_count):
            raw = stream.read(block_bytes)
            if len(raw) != block_bytes:
                raise ValueError("truncated incidence columns")
            cover = int.from_bytes(raw, "little")
            if cover & ~universe:
                raise ValueError("nonzero padding bits")
            covers.append(cover)
        if stream.read(1):
            raise ValueError("trailing incidence bytes")
    return tuple(records), tuple(covers), graph_count


def paired_candidates(
    covers: Sequence[int], involution: Sequence[int]
) -> tuple[tuple[tuple[int, int], ...], tuple[int, ...]]:
    pairs = tuple(
        (candidate, involution[candidate])
        for candidate in range(len(involution))
        if candidate < involution[candidate]
    )
    if len(pairs) * 2 != len(involution):
        raise ValueError("complement pairs do not partition the candidates")
    return pairs, tuple(covers[left] | covers[right] for left, right in pairs)


def first_bits(value: int, limit: int) -> tuple[int, ...]:
    result = []
    while value and len(result) < limit:
        bit = value & -value
        result.append(bit)
        value ^= bit
    return tuple(result)


def exact_cover_search(
    covers: Sequence[int], graph_count: int, limit: int
) -> dict[str, object]:
    """Complete branch-and-bound search for a cover using at most ``limit`` sets."""
    universe = (1 << graph_count) - 1
    explored = 0
    witness_rows: set[int] = set()

    @functools.cache
    def selected_union(selected: int) -> int:
        result = 0
        remaining = selected
        while remaining:
            bit = remaining & -remaining
            result |= covers[bit.bit_length() - 1]
            remaining ^= bit
        return result

    @functools.cache
    def search(selected: int) -> int | None:
        nonlocal explored
        explored += 1
        uncovered = universe & ~selected_union(selected)
        if not uncovered:
            return selected
        used = selected.bit_count()
        if used >= limit:
            witness_rows.add((uncovered & -uncovered).bit_length() - 1)
            return None

        # Among a small deterministic prefix, branch on the most constrained row.
        best_bit = 0
        best_candidates: tuple[int, ...] | None = None
        for graph_bit in first_bits(uncovered, 24):
            candidates = tuple(
                index
                for index, cover in enumerate(covers)
                if not (selected >> index & 1) and cover & graph_bit
            )
            if best_candidates is None or len(candidates) < len(best_candidates):
                best_bit = graph_bit
                best_candidates = candidates
        if best_candidates is None:
            raise AssertionError("nonempty uncovered set has no first bit")
        graph_index = best_bit.bit_length() - 1
        witness_rows.add(graph_index)
        if not best_candidates:
            return None

        ordered = sorted(
            best_candidates,
            key=lambda candidate: (covers[candidate] & uncovered).bit_count(),
            reverse=True,
        )
        for candidate in ordered:
            result = search(selected | 1 << candidate)
            if result is not None:
                return result
        return None

    started = time.perf_counter()
    selected = search(0)
    elapsed = time.perf_counter() - started
    result = None
    if selected is not None:
        result = tuple(
            index for index in range(len(covers)) if selected >> index & 1
        )
    return {
        "cover": result,
        "explored_states": explored,
        "elapsed_seconds": elapsed,
        "state_witness_rows": tuple(sorted(witness_rows)),
        "state_witness_count": len(witness_rows),
    }


def pair_ids_for_records(
    records: Sequence[str], pairs: Sequence[tuple[int, int]], wanted: Iterable[str]
) -> tuple[int, ...]:
    record_to_id = {record: index for index, record in enumerate(records)}
    candidate_to_pair = {
        candidate: pair_id
        for pair_id, pair in enumerate(pairs)
        for candidate in pair
    }
    return tuple(sorted({candidate_to_pair[record_to_id[record]] for record in wanted}))


def analyze(incidence_path: Path) -> dict[str, object]:
    started = time.perf_counter()
    records, covers, graph_count = read_incidence(incidence_path)
    loaded = time.perf_counter()
    involution = complement_involution(records)
    paired = time.perf_counter()
    pairs, pair_covers = paired_candidates(covers, involution)
    search2 = exact_cover_search(pair_covers, graph_count, 2)
    search3 = exact_cover_search(pair_covers, graph_count, 3)
    frozen_cover5 = ("F@h^g", "FCUrO", "FDLmW", "FG`Xo", "FdW}w")
    upper_pair_ids = pair_ids_for_records(records, pairs, frozen_cover5)
    universe = (1 << graph_count) - 1
    upper_missing = universe
    for pair_id in upper_pair_ids:
        upper_missing &= ~pair_covers[pair_id]
    if upper_missing:
        raise ValueError("complement closure of frozen cover5 is not a cover")
    if len(upper_pair_ids) != 4:
        raise ValueError(f"expected four complement pairs, got {upper_pair_ids}")
    found_pair_ids = search3["cover"]
    if found_pair_ids is None:
        raise ValueError("expected the discovered three-pair cover")
    found_missing = universe
    for pair_id in found_pair_ids:
        found_missing &= ~pair_covers[pair_id]
    if found_missing:
        raise AssertionError("reported three-pair solution does not cover")
    removal_holes = []
    for removed in found_pair_ids:
        missing = universe
        for pair_id in found_pair_ids:
            if pair_id != removed:
                missing &= ~pair_covers[pair_id]
        removal_holes.append(missing.bit_count())
    return {
        "schema_version": 1,
        "status": "PASS",
        "claim": {
            "cover_by_three_complement_pairs_found": search3["cover"] is not None,
            "cover_by_at_most_two_complement_pairs_found": search2["cover"] is not None,
            "minimum_complement_pairs": 3 if search2["cover"] is None else None,
            "minimum_motif_classes": 6 if search2["cover"] is None else None,
            "upper_bound_pairs": len(upper_pair_ids),
        },
        "incidence": {
            "path": str(incidence_path),
            "sha256": sha256(incidence_path),
            "graph_count": graph_count,
            "candidate_classes": len(records),
        },
        "complement_involution": {
            "pairs": len(pairs),
            "fixed_points": sum(involution[index] == index for index in range(len(involution))),
            "map_zero_based": list(involution),
        },
        "search_at_most_two_pairs": search2,
        "search_at_most_three_pairs": search3,
        "minimum_cover": {
            "pair_ids_zero_based": list(found_pair_ids),
            "candidate_ids_zero_based": [list(pairs[pair_id]) for pair_id in found_pair_ids],
            "records": [
                [records[left], records[right]]
                for left, right in (pairs[pair_id] for pair_id in found_pair_ids)
            ],
            "individual_pair_coverage": [
                pair_covers[pair_id].bit_count() for pair_id in found_pair_ids
            ],
            "pair_removal_holes": removal_holes,
            "missing_graphs": found_missing.bit_count(),
        },
        "known_upper_bound": {
            "pair_ids_zero_based": list(upper_pair_ids),
            "candidate_ids_zero_based": [list(pairs[pair_id]) for pair_id in upper_pair_ids],
            "records": [
                [records[left], records[right]]
                for left, right in (pairs[pair_id] for pair_id in upper_pair_ids)
            ],
            "missing_graphs": upper_missing.bit_count(),
        },
        "timing_seconds": {
            "read_and_hash": loaded - started,
            "complement_involution": paired - loaded,
            "total": time.perf_counter() - started,
        },
        "scope": (
            "Exact only for complement-closed covers made from order-seven classes "
            "against the frozen exhaustive R(4,4,12) catalogue."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--incidence", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = analyze(args.incidence)
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.report:
        require_ssd(args.report)
        args.report.parent.mkdir(parents=True, exist_ok=True)
        if args.report.exists():
            raise FileExistsError(f"refusing to overwrite {args.report}")
        args.report.write_text(payload, encoding="utf-8", newline="\n")
    print(payload, end="")


if __name__ == "__main__":
    main()
