#!/usr/bin/env python3
"""Standalone verifier for the complement-closed order-seven minimum.

The lower-bound replay imports no project module and reads no incidence file.
It exhaustively reconstructs the 362 order-seven R(4,4) isomorphism classes,
their complement involution, and the induced signatures of 30 explicit
R(4,4,12) graphs.  It then excludes every choice of at most two complement
pairs.  The six-record upper bound is checked locally for exact pairing and
labelled closure; its separate witness replay covers the full K12 catalogue.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
KERNEL_PATH = HERE / "kernel30_r44_12.g6"
COVER_PATH = HERE / "cover6_complement_closed.tsv"

EXPECTED_SOURCE7_SHA256 = (
    "6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010"
)
EXPECTED_KERNEL_SHA256 = (
    "EB61306B5DA0F15DC1112D82007BB29CD2FD3AEE460FD1C0D62E24401C66C8CC"
)
EXPECTED_COVER_SHA256 = (
    "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
)
EXPECTED_ORDER7_CLASSES = 362
EXPECTED_LABELLED_R44 = 923_012
EXPECTED_COMPLEMENT_PAIRS = 181
EXPECTED_KERNEL_GRAPHS = 30
EXPECTED_COVER_RECORDS = (
    "F@h^g",
    "FKDhw",
    "FG`Xo",
    "FdW}w",
    "FHFLw",
    "FIIXw",
)
EXPECTED_COVER_CANDIDATE_IDS = (41, 220, 174, 323, 185, 194)
EXPECTED_COVER_PAIR_IDS = (40, 138, 144)
EXPECTED_SELECTED_ORBIT_SIZES = (5_040, 5_040, 2_520, 2_520, 5_040, 5_040)
EXPECTED_SELECTED_CLOSURE = 25_200
EXPECTED_SIGNATURE_SHA256 = (
    "FD92B41FAD600EEC47FA5214EA1F36D9E7B1B6D44DDBE8EADFD029F41EFD89A9"
)
EXPECTED_DELETION_WITNESS_SHA256 = (
    "0A813D1203A9A6F2E16AC0E4BA1E73C4F39928EAFF372468F2267EA40930AEDF"
)
EXPECTED_SELECTED_CLOSURE_SHA256 = (
    "04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def records(path: Path) -> tuple[str, ...]:
    return tuple(
        line.strip()
        for line in path.read_text(encoding="ascii").splitlines()
        if line.strip()
    )


def cover_records(path: Path) -> tuple[str, ...]:
    result = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="ascii").splitlines(), 1
    ):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise ValueError(f"invalid cover row {line_number}: {raw_line!r}")
        result.append(fields[1])
    return tuple(result)


def edge_position(left: int, right: int) -> int:
    if left == right:
        raise ValueError("loop is not an edge")
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


def decode_graph6(record: str, order: int) -> int:
    edge_count = order * (order - 1) // 2
    expected_length = 1 + (edge_count + 5) // 6
    if len(record) != expected_length or ord(record[0]) - 63 != order:
        raise ValueError(f"wrong graph6 order or length: {record!r}")
    result = 0
    position = 0
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 payload: {record!r}")
        for shift in range(5, -1, -1):
            bit = value >> shift & 1
            if position < edge_count:
                result |= bit << position
            elif bit:
                raise ValueError(f"nonzero graph6 padding: {record!r}")
            position += 1
    return result


@functools.cache
def permutations(order: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.permutations(range(order)))


def relabel(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    target = 0
    for right in range(1, len(permutation)):
        for left in range(right):
            source = edge_position(permutation[left], permutation[right])
            result |= ((mask >> source) & 1) << target
            target += 1
    return result


@functools.cache
def clique_masks(order: int) -> tuple[int, ...]:
    return tuple(
        sum(
            1 << edge_position(left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(order), 4)
    )


def is_r44(mask: int, order: int) -> bool:
    return all(mask & clique not in (0, clique) for clique in clique_masks(order))


def labelled_catalogue_map(source_records: Sequence[str]) -> dict[int, int]:
    mapping: dict[int, int] = {}
    for candidate_id, record in enumerate(source_records):
        mask = decode_graph6(record, 7)
        if not is_r44(mask, 7):
            raise ValueError(f"source candidate is not R(4,4,7): {record}")
        for permutation in permutations(7):
            labelled = relabel(mask, permutation)
            previous = mapping.setdefault(labelled, candidate_id)
            if previous != candidate_id:
                raise ValueError(
                    f"source candidates {previous} and {candidate_id} are isomorphic"
                )
    return mapping


def verify_catalogue_completeness(mapping: dict[int, int]) -> None:
    limit = 1 << 21
    valid = 0
    for mask in range(limit):
        expected = is_r44(mask, 7)
        valid += expected
        if expected != (mask in mapping):
            raise ValueError(f"order-seven completeness failed at mask {mask:#x}")
    if valid != EXPECTED_LABELLED_R44 or len(mapping) != EXPECTED_LABELLED_R44:
        raise ValueError("labelled R(4,4,7) count mismatch")


def complement_involution(
    source_records: Sequence[str], mapping: dict[int, int]
) -> tuple[int, ...]:
    full = (1 << 21) - 1
    result = tuple(
        mapping[full ^ decode_graph6(record, 7)] for record in source_records
    )
    if any(result[result[index]] != index for index in range(len(result))):
        raise ValueError("complement map is not involutive")
    if any(result[index] == index for index in range(len(result))):
        raise ValueError("unexpected fixed point of the complement map")
    if any(
        decode_graph6(source_records[index], 7).bit_count()
        + decode_graph6(source_records[result[index]], 7).bit_count()
        != 21
        for index in range(len(result))
    ):
        raise ValueError("complement partner edge counts do not sum to 21")
    return result


def complement_pairs(involution: Sequence[int]) -> tuple[tuple[int, int], ...]:
    result = tuple(
        (candidate, involution[candidate])
        for candidate in range(len(involution))
        if candidate < involution[candidate]
    )
    if len(result) != EXPECTED_COMPLEMENT_PAIRS:
        raise ValueError("complement pair count mismatch")
    return result


@functools.cache
def subset_positions() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(vertices[left], vertices[right])
            for right in range(1, 7)
            for left in range(right)
        )
        for vertices in itertools.combinations(range(12), 7)
    )


def induced_mask(graph: int, positions: Sequence[int]) -> int:
    return sum(((graph >> source) & 1) << target for target, source in enumerate(positions))


def kernel_signature(
    record: str, mapping: dict[int, int], candidate_to_pair: Sequence[int]
) -> int:
    graph = decode_graph6(record, 12)
    if not is_r44(graph, 12):
        raise ValueError(f"kernel graph is not R(4,4,12): {record}")
    result = 0
    for positions in subset_positions():
        candidate = mapping.get(induced_mask(graph, positions))
        if candidate is None:
            raise ValueError("induced R(4,4,7) graph absent from complete mapping")
        result |= 1 << candidate_to_pair[candidate]
    return result


def hitting_set_at_most_two(
    clauses: Sequence[int], candidate_count: int
) -> tuple[int, ...] | None:
    if not clauses:
        return ()
    if any(clause == 0 for clause in clauses):
        return None
    all_candidates = (1 << candidate_count) - 1
    for first in range(candidate_count):
        unhit = tuple(clause for clause in clauses if not (clause >> first & 1))
        if not unhit:
            return (first,)
        common = all_candidates
        for clause in unhit:
            common &= clause
        if common:
            bit = common & -common
            return first, bit.bit_length() - 1
    return None


def digest_lines(lines: Iterable[str]) -> str:
    digest = hashlib.sha256()
    for line in lines:
        digest.update(line.encode("ascii"))
    return digest.hexdigest().upper()


def verify(source7_path: Path) -> dict[str, object]:
    if sha256(source7_path) != EXPECTED_SOURCE7_SHA256:
        raise ValueError("order-seven source SHA-256 mismatch")
    if sha256(KERNEL_PATH) != EXPECTED_KERNEL_SHA256:
        raise ValueError("kernel SHA-256 mismatch")
    if sha256(COVER_PATH) != EXPECTED_COVER_SHA256:
        raise ValueError("cover SHA-256 mismatch")
    source_records = records(source7_path)
    if len(source_records) != EXPECTED_ORDER7_CLASSES:
        raise ValueError("order-seven source class count mismatch")
    mapping = labelled_catalogue_map(source_records)
    verify_catalogue_completeness(mapping)
    involution = complement_involution(source_records, mapping)
    pairs = complement_pairs(involution)
    candidate_to_pair = [0] * len(source_records)
    for pair_id, (left, right) in enumerate(pairs):
        candidate_to_pair[left] = pair_id
        candidate_to_pair[right] = pair_id

    kernel_records = records(KERNEL_PATH)
    if len(kernel_records) != EXPECTED_KERNEL_GRAPHS or len(set(kernel_records)) != len(kernel_records):
        raise ValueError("kernel count or uniqueness mismatch")
    signatures = tuple(
        kernel_signature(record, mapping, candidate_to_pair)
        for record in kernel_records
    )
    lower_solution = hitting_set_at_most_two(signatures, len(pairs))
    if lower_solution is not None:
        raise ValueError(f"kernel admits an at-most-two-pair cover: {lower_solution}")
    deletion_witnesses = []
    for removed in range(len(signatures)):
        witness = hitting_set_at_most_two(
            signatures[:removed] + signatures[removed + 1 :], len(pairs)
        )
        if witness is None:
            raise ValueError(f"kernel row {removed} is removable")
        deletion_witnesses.append(witness)

    frozen_records = cover_records(COVER_PATH)
    if frozen_records != EXPECTED_COVER_RECORDS:
        raise ValueError("frozen cover records changed")
    record_to_id = {record: candidate for candidate, record in enumerate(source_records)}
    selected_ids = tuple(record_to_id[record] for record in frozen_records)
    if selected_ids != EXPECTED_COVER_CANDIDATE_IDS:
        raise ValueError(f"frozen cover candidate IDs changed: {selected_ids}")
    selected_pair_ids = tuple(sorted({candidate_to_pair[candidate] for candidate in selected_ids}))
    if selected_pair_ids != EXPECTED_COVER_PAIR_IDS:
        raise ValueError(f"frozen cover pair IDs changed: {selected_pair_ids}")
    if any(involution[selected_ids[2 * index]] != selected_ids[2 * index + 1] for index in range(3)):
        raise ValueError("frozen cover rows are not exact consecutive complement pairs")
    if any(not signature & sum(1 << pair for pair in selected_pair_ids) for signature in signatures):
        raise ValueError("frozen cover does not cover its lower-bound kernel")

    orbit_counts = Counter(mapping.values())
    selected_orbit_sizes = tuple(orbit_counts[candidate] for candidate in selected_ids)
    if selected_orbit_sizes != EXPECTED_SELECTED_ORBIT_SIZES:
        raise ValueError(f"selected orbit sizes changed: {selected_orbit_sizes}")
    selected_set = set(selected_ids)
    selected_closure = tuple(sorted(mask for mask, candidate in mapping.items() if candidate in selected_set))
    if len(selected_closure) != EXPECTED_SELECTED_CLOSURE:
        raise ValueError("selected labelled closure size mismatch")

    signature_digest = digest_lines(
        f"{record}\t{signature:046X}\n"
        for record, signature in zip(kernel_records, signatures, strict=True)
    )
    closure_digest = digest_lines(f"{mask:06X}\n" for mask in selected_closure)
    deletion_digest = digest_lines(
        f"{index}\t{','.join(map(str, witness))}\n"
        for index, witness in enumerate(deletion_witnesses)
    )
    if signature_digest != EXPECTED_SIGNATURE_SHA256:
        raise ValueError(f"kernel signature SHA-256 changed: {signature_digest}")
    if deletion_digest != EXPECTED_DELETION_WITNESS_SHA256:
        raise ValueError(f"deletion-witness SHA-256 changed: {deletion_digest}")
    if closure_digest != EXPECTED_SELECTED_CLOSURE_SHA256:
        raise ValueError(f"selected closure SHA-256 changed: {closure_digest}")
    return {
        "schema_version": 1,
        "status": "PASS",
        "claim": {
            "minimum_complement_pairs": 3,
            "minimum_motif_classes": 6,
            "lower_bound_absolute_on_explicit_kernel": True,
            "upper_bound_full_catalogue_replay_separate": True,
        },
        "order7_catalogue": {
            "path": str(source7_path),
            "sha256": sha256(source7_path),
            "classes": len(source_records),
            "all_labelled_graphs_examined": 1 << 21,
            "labelled_r44": len(mapping),
            "complement_pairs": len(pairs),
            "fixed_points": 0,
        },
        "lower_bound": {
            "kernel_path": str(KERNEL_PATH),
            "kernel_sha256": sha256(KERNEL_PATH),
            "kernel_graphs": len(kernel_records),
            "induced_subgraphs_checked": len(kernel_records) * len(subset_positions()),
            "candidate_selections_excluded": len(pairs) * (len(pairs) + 1) // 2,
            "signature_sha256": signature_digest,
            "deletion_irredundant": True,
            "deletion_witness_sha256": deletion_digest,
        },
        "upper_bound_local": {
            "cover_path": str(COVER_PATH),
            "cover_sha256": sha256(COVER_PATH),
            "records": list(frozen_records),
            "candidate_ids_zero_based": list(selected_ids),
            "pair_ids_zero_based": list(selected_pair_ids),
            "orbit_sizes": list(selected_orbit_sizes),
            "labelled_closure": len(selected_closure),
            "labelled_closure_sha256": closure_digest,
            "exact_complement_pairs": True,
        },
        "scope": (
            "The lower bound is absolute for order-seven complement-closed motif "
            "covers because every kernel graph is checked directly.  The upper bound "
            "for all R(4,4,12) classes is established by the separate exhaustive "
            "catalogue witness replay."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source7", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.source7), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
