#!/usr/bin/env python3
"""Independently replay the 25-graph lower-bound kernel for order-7 covers.

This verifier deliberately imports only the Python standard library.  It does
not use the McKay R(4,4) catalogues, the large incidence files, or
``minimum_order7_cover``.  The only mathematical inputs are 25 explicit
order-12 graph6 records and the five frozen order-7 motifs.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
KERNEL_PATH = HERE / "kernel25_r44_12.g6"
COVER_PATH = HERE / "cover5_order7.tsv"

EXPECTED_KERNEL_SHA256 = (
    "442C5DAA776DCD0FC0D22A698BB15BBB797F3760CCDCC5902BAE7B0B185DBBBF"
)
EXPECTED_COVER_SHA256 = (
    "CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288"
)
EXPECTED_SIGNATURE_SIZES = (
    12,
    12,
    28,
    48,
    48,
    48,
    52,
    52,
    55,
    55,
    56,
    58,
    60,
    63,
    35,
    56,
    55,
    73,
    73,
    81,
    58,
    81,
    35,
    48,
    63,
)
EXPECTED_CANONICAL_MOTIFS = 323
EXPECTED_SIGNATURE_SHA256 = (
    "FD43077A19F14BC10248D68415C95C8B03093AC535F524D9E501B6DFBA6FCA9D"
)
EXPECTED_LABELLED_MASKS_CACHED = 829_562
EXPECTED_DFS_STATES = 147_127
EXPECTED_COVER_ROW_COUNTS = (7, 7, 8, 9, 9)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def edge_position(left: int, right: int) -> int:
    if left == right:
        raise ValueError("loops have no graph6 edge position")
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


def decode_graph6_mask(record: str, expected_order: int) -> int:
    """Decode a strict short-form graph6 record into triangular edge bits."""
    if not record or record != record.strip():
        raise ValueError(f"invalid graph6 whitespace: {record!r}")
    edge_count = expected_order * (expected_order - 1) // 2
    payload_length = (edge_count + 5) // 6
    if len(record) != payload_length + 1 or ord(record[0]) - 63 != expected_order:
        raise ValueError(f"wrong graph6 order or length: {record!r}")
    mask = 0
    position = 0
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 payload: {record!r}")
        for shift in range(5, -1, -1):
            bit = value >> shift & 1
            if position < edge_count:
                mask |= bit << position
            elif bit:
                raise ValueError(f"nonzero graph6 padding: {record!r}")
            position += 1
    return mask


def encode_graph6_mask(mask: int, order: int) -> str:
    edge_count = order * (order - 1) // 2
    if not 0 <= mask < 1 << edge_count:
        raise ValueError("graph mask does not fit its order")
    characters = [chr(order + 63)]
    for start in range(0, edge_count, 6):
        value = 0
        for offset in range(6):
            value <<= 1
            position = start + offset
            if position < edge_count:
                value |= mask >> position & 1
        characters.append(chr(value + 63))
    return "".join(characters)


@functools.cache
def clique_masks(order: int, size: int) -> tuple[int, ...]:
    masks: list[int] = []
    for vertices in itertools.combinations(range(order), size):
        mask = 0
        for right in range(1, size):
            for left in range(right):
                mask |= 1 << edge_position(vertices[left], vertices[right])
        masks.append(mask)
    return tuple(masks)


def is_r44(mask: int, order: int) -> bool:
    edge_count = order * (order - 1) // 2
    if not 0 <= mask < 1 << edge_count:
        return False
    return all(mask & clique not in (0, clique) for clique in clique_masks(order, 4))


@functools.cache
def permutation_edge_maps(order: int) -> tuple[tuple[int, ...], ...]:
    """Return every S_order action as output-edge -> input-edge positions."""
    return tuple(
        tuple(
            edge_position(permutation[left], permutation[right])
            for right in range(1, order)
            for left in range(right)
        )
        for permutation in itertools.permutations(range(order))
    )


def relabel_mask(mask: int, edge_map: Sequence[int]) -> int:
    result = 0
    output_bit = 1
    for source in edge_map:
        if mask >> source & 1:
            result |= output_bit
        output_bit <<= 1
    return result


class OrderSevenCanonicalizer:
    """Exact S7 orbit canonicalizer with a complete orbit cache."""

    def __init__(self) -> None:
        self.edge_maps = permutation_edge_maps(7)
        if len(self.edge_maps) != 5_040:
            raise AssertionError("S7 enumeration is incomplete")
        self.cache: dict[int, int] = {}
        self.orbits_expanded = 0

    def canonical(self, mask: int) -> int:
        if not 0 <= mask < 1 << 21:
            raise ValueError("order-seven mask is out of range")
        known = self.cache.get(mask)
        if known is not None:
            return known
        orbit = {relabel_mask(mask, edge_map) for edge_map in self.edge_maps}
        canonical = min(orbit)
        for labelled in orbit:
            self.cache[labelled] = canonical
        self.orbits_expanded += 1
        return canonical


@functools.cache
def subset_edge_positions(parent_order: int, subset_order: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(vertices[left], vertices[right])
            for right in range(1, subset_order)
            for left in range(right)
        )
        for vertices in itertools.combinations(range(parent_order), subset_order)
    )


def induced_mask(parent_mask: int, positions: Sequence[int]) -> int:
    result = 0
    for local, source in enumerate(positions):
        result |= (parent_mask >> source & 1) << local
    return result


def read_kernel(path: Path) -> tuple[str, ...]:
    try:
        text = path.read_text(encoding="ascii")
    except UnicodeDecodeError as error:
        raise ValueError("kernel graph6 file is not ASCII") from error
    records = tuple(text.splitlines())
    if len(records) != 25 or any(not record for record in records):
        raise ValueError("kernel must contain exactly 25 nonempty graph6 records")
    if len(set(records)) != len(records):
        raise ValueError("kernel contains duplicate graph6 records")
    return records


def read_cover(path: Path) -> tuple[str, ...]:
    records: list[str] = []
    for line_number, raw_line in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7" or not fields[1]:
            raise ValueError(f"invalid cover row {line_number}: {raw_line!r}")
        records.append(fields[1])
    if len(records) != 5 or len(set(records)) != 5:
        raise ValueError("cover must contain five distinct order-seven records")
    return tuple(records)


def recompute_signatures(
    records: Sequence[str], canonicalizer: OrderSevenCanonicalizer
) -> tuple[tuple[int, ...], ...]:
    positions = subset_edge_positions(12, 7)
    if len(positions) != 792 or any(len(row) != 21 for row in positions):
        raise AssertionError("the K12 choose 7 incidence table is malformed")
    signatures: list[tuple[int, ...]] = []
    for index, record in enumerate(records):
        graph = decode_graph6_mask(record, 12)
        if not is_r44(graph, 12):
            raise ValueError(f"kernel graph {index} is not R(4,4,12)")
        signature: set[int] = set()
        for subset_index, edge_positions in enumerate(positions):
            induced = induced_mask(graph, edge_positions)
            if not is_r44(induced, 7):
                raise AssertionError(
                    f"induced graph {index}/{subset_index} unexpectedly violates R(4,4)"
                )
            signature.add(canonicalizer.canonical(induced))
        signatures.append(tuple(sorted(signature)))
    return tuple(signatures)


def disjoint_row_lower_bound(unhit: Sequence[int], stop_after: int) -> int:
    used_candidates = 0
    count = 0
    for row in sorted(unhit, key=int.bit_count):
        if not row & used_candidates:
            used_candidates |= row
            count += 1
            if count > stop_after:
                break
    return count


def find_hitting_set(
    signatures: Sequence[Sequence[int]], limit: int
) -> tuple[tuple[int, ...] | None, int]:
    """Exhaustively find a hitting set of size at most ``limit``, if one exists."""
    if limit < 0 or any(not signature for signature in signatures):
        raise ValueError("invalid hitting-set instance")
    candidates = tuple(sorted({candidate for row in signatures for candidate in row}))
    candidate_index = {candidate: index for index, candidate in enumerate(candidates)}
    row_masks = tuple(
        sum(1 << candidate_index[candidate] for candidate in row)
        for row in signatures
    )
    explored = 0

    @functools.cache
    def search(selected: int) -> int | None:
        nonlocal explored
        explored += 1
        unhit = tuple(row for row in row_masks if not row & selected)
        if not unhit:
            return selected
        remaining = limit - selected.bit_count()
        if remaining <= 0:
            return None
        if disjoint_row_lower_bound(unhit, remaining) > remaining:
            return None
        branch = min(unhit, key=int.bit_count)
        branch_candidates = [
            index for index in range(len(candidates)) if branch >> index & 1
        ]
        branch_candidates.sort(
            key=lambda index: sum(row >> index & 1 for row in unhit),
            reverse=True,
        )
        for index in branch_candidates:
            result = search(selected | 1 << index)
            if result is not None:
                return result
        return None

    selected_mask = search(0)
    if selected_mask is None:
        return None, explored
    return (
        tuple(
            candidates[index]
            for index in range(len(candidates))
            if selected_mask >> index & 1
        ),
        explored,
    )


def signature_bytes(signatures: Iterable[Sequence[int]]) -> bytes:
    return "".join(
        ",".join(f"{candidate:06X}" for candidate in signature) + "\n"
        for signature in signatures
    ).encode("ascii")


def verify(
    kernel_path: Path = KERNEL_PATH,
    cover_path: Path = COVER_PATH,
    *,
    check_frozen: bool = True,
) -> dict[str, object]:
    kernel_hash = sha256(kernel_path)
    cover_hash = sha256(cover_path)
    if check_frozen and kernel_hash != EXPECTED_KERNEL_SHA256:
        raise ValueError(f"kernel SHA-256 mismatch: {kernel_hash}")
    if check_frozen and cover_hash != EXPECTED_COVER_SHA256:
        raise ValueError(f"cover SHA-256 mismatch: {cover_hash}")

    kernel = read_kernel(kernel_path)
    cover = read_cover(cover_path)
    canonicalizer = OrderSevenCanonicalizer()
    signatures = recompute_signatures(kernel, canonicalizer)
    signature_sizes = tuple(map(len, signatures))
    candidate_union = {candidate for signature in signatures for candidate in signature}
    signature_hash = sha256_bytes(signature_bytes(signatures))
    if check_frozen and signature_sizes != EXPECTED_SIGNATURE_SIZES:
        raise ValueError(f"signature sizes changed: {signature_sizes}")
    if check_frozen and len(candidate_union) != EXPECTED_CANONICAL_MOTIFS:
        raise ValueError(f"canonical motif count changed: {len(candidate_union)}")
    if check_frozen and signature_hash != EXPECTED_SIGNATURE_SHA256:
        raise ValueError(f"signature SHA-256 mismatch: {signature_hash}")
    if check_frozen and len(canonicalizer.cache) != EXPECTED_LABELLED_MASKS_CACHED:
        raise ValueError(
            f"labelled orbit closure changed: {len(canonicalizer.cache)}"
        )

    hitting_four, explored = find_hitting_set(signatures, 4)
    if hitting_four is not None:
        raise ValueError(
            "kernel unexpectedly has a hitting set of size at most four: "
            f"{tuple(encode_graph6_mask(mask, 7) for mask in hitting_four)}"
        )
    if check_frozen and explored != EXPECTED_DFS_STATES:
        raise ValueError(f"hitting-set search state count changed: {explored}")

    cover_masks = tuple(
        canonicalizer.canonical(decode_graph6_mask(record, 7)) for record in cover
    )
    if len(set(cover_masks)) != 5:
        raise ValueError("two frozen cover motifs are isomorphic")
    missed = tuple(
        index
        for index, signature in enumerate(signatures)
        if not set(signature).intersection(cover_masks)
    )
    if missed:
        raise ValueError(f"frozen cover5 misses kernel rows: {missed}")
    cover_row_counts = tuple(
        sum(mask in signature for signature in signatures) for mask in cover_masks
    )
    if check_frozen and cover_row_counts != EXPECTED_COVER_ROW_COUNTS:
        raise ValueError(f"cover row counts changed: {cover_row_counts}")

    return {
        "schema_version": 1,
        "status": "PASS",
        "claim": (
            "The 25 explicit R(4,4,12) graphs have no hitting set of at most "
            "four induced order-seven isomorphism classes; the five frozen "
            "motifs hit all 25 graphs."
        ),
        "inputs": {
            "kernel_graph6": {
                "path": str(kernel_path),
                "sha256": kernel_hash,
                "records": len(kernel),
            },
            "cover5": {
                "path": str(cover_path),
                "sha256": cover_hash,
                "records": list(cover),
            },
        },
        "induced_recomputation": {
            "kernel_graphs_r44_checked": len(kernel),
            "four_vertex_subsets_per_kernel_graph": len(clique_masks(12, 4)),
            "four_vertex_subsets_checked": len(kernel) * len(clique_masks(12, 4)),
            "subsets_per_kernel_graph": len(subset_edge_positions(12, 7)),
            "induced_subgraphs_checked": len(kernel) * len(subset_edge_positions(12, 7)),
            "signature_sizes": list(signature_sizes),
            "signature_sha256": signature_hash,
            "canonical_motifs_in_kernel": len(candidate_union),
            "s7_permutations": len(canonicalizer.edge_maps),
            "s7_orbits_expanded": canonicalizer.orbits_expanded,
            "labelled_masks_cached": len(canonicalizer.cache),
        },
        "lower_bound": {
            "maximum_forbidden_size": 4,
            "hitting_set_found": False,
            "dfs_states_explored": explored,
        },
        "frozen_five_motifs": {
            "all_kernel_graphs_hit": True,
            "rows_hit_by_motif": list(cover_row_counts),
            "canonical_graph6": [
                encode_graph6_mask(mask, 7) for mask in cover_masks
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel", type=Path, default=KERNEL_PATH)
    parser.add_argument("--cover", type=Path, default=COVER_PATH)
    parser.add_argument("--allow-unfrozen-input", action="store_true")
    arguments = parser.parse_args()
    report = verify(
        arguments.kernel,
        arguments.cover,
        check_frozen=not arguments.allow_unfrozen_input,
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
