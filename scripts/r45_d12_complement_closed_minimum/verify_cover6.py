#!/usr/bin/env python3
"""Direct stdlib-only replay of the six-motif upper bound.

This verifier reads the frozen official R(4,4,12) graph6 catalogue directly.
It rebuilds all 25,200 labelled copies of the six motifs and checks each of the
1,449,166 order-twelve records through its 792 seven-vertex subsets.  It does
not read the native incidence matrix or the generated witness file.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import time
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
COVER_PATH = HERE / "cover6_complement_closed.tsv"

EXPECTED_COVER_SHA256 = (
    "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
)
EXPECTED_SOURCE12_SHA256 = (
    "C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A"
)
EXPECTED_RECORDS = ("F@h^g", "FKDhw", "FG`Xo", "FdW}w", "FHFLw", "FIIXw")
EXPECTED_ORBIT_SIZES = (5_040, 5_040, 2_520, 2_520, 5_040, 5_040)
EXPECTED_CLOSURE_SIZE = 25_200
EXPECTED_CLOSURE_SHA256 = (
    "04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7"
)
EXPECTED_GRAPHS = 1_449_166
EXPECTED_FIRST_HIT_DISTRIBUTION = (46_679, 347_807, 698_002, 36_774, 108_486, 211_418)
REMOVAL_WITNESSES = (
    (40, 277_215, "KCdPQGbl]VNo", 22),
    (138, 3_927, "K@LS{TfyAysn", 446),
    (144, 121_102, "K@h\\Qmr[uw|c", 40),
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def edge_position(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


def decode_graph6(record: str, order: int) -> int:
    edge_count = order * (order - 1) // 2
    if len(record) != 1 + (edge_count + 5) // 6 or ord(record[0]) - 63 != order:
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
def edge_maps() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(permutation[left], permutation[right])
            for right in range(1, 7)
            for left in range(right)
        )
        for permutation in itertools.permutations(range(7))
    )


def relabel(mask: int, edge_map: Sequence[int]) -> int:
    result = 0
    for target, source in enumerate(edge_map):
        result |= ((mask >> source) & 1) << target
    return result


def orbit(record: str) -> frozenset[int]:
    mask = decode_graph6(record, 7)
    return frozenset(relabel(mask, edge_map) for edge_map in edge_maps())


def cover_records() -> tuple[str, ...]:
    result = []
    for line_number, raw_line in enumerate(
        COVER_PATH.read_text(encoding="ascii").splitlines(), 1
    ):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise ValueError(f"invalid cover row {line_number}: {raw_line!r}")
        result.append(fields[1])
    return tuple(result)


def digest_masks(masks: Iterable[int]) -> str:
    digest = hashlib.sha256()
    for mask in sorted(masks):
        digest.update(f"{mask:06X}\n".encode("ascii"))
    return digest.hexdigest().upper()


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
    result = 0
    for target, source in enumerate(positions):
        result |= ((graph >> source) & 1) << target
    return result


def build_closure() -> tuple[tuple[frozenset[int], ...], dict[int, int]]:
    if sha256(COVER_PATH) != EXPECTED_COVER_SHA256:
        raise ValueError("cover SHA-256 mismatch")
    records = cover_records()
    if records != EXPECTED_RECORDS:
        raise ValueError("cover records changed")
    orbits = tuple(orbit(record) for record in records)
    if tuple(map(len, orbits)) != EXPECTED_ORBIT_SIZES:
        raise ValueError("selected orbit sizes changed")
    full = (1 << 21) - 1
    for pair in range(3):
        left = orbits[2 * pair]
        right = orbits[2 * pair + 1]
        if {full ^ mask for mask in left} != right:
            raise ValueError(f"cover pair {pair} is not exactly complement-closed")
    owner: dict[int, int] = {}
    for motif, labelled_orbit in enumerate(orbits):
        for mask in labelled_orbit:
            previous = owner.setdefault(mask, motif)
            if previous != motif:
                raise ValueError("selected motif classes overlap")
    if len(owner) != EXPECTED_CLOSURE_SIZE:
        raise ValueError("selected closure size changed")
    if digest_masks(owner) != EXPECTED_CLOSURE_SHA256:
        raise ValueError("selected closure SHA-256 mismatch")
    return orbits, owner


def selected_pair_signature(record: str, owner: dict[int, int]) -> tuple[int, ...]:
    graph = decode_graph6(record, 12)
    pairs = {
        motif // 2
        for positions in subset_positions()
        if (motif := owner.get(induced_mask(graph, positions))) is not None
    }
    return tuple(sorted(pairs))


def verify(source12_path: Path) -> dict[str, object]:
    started = time.perf_counter()
    source_digest = sha256(source12_path)
    if source_digest != EXPECTED_SOURCE12_SHA256:
        raise ValueError("order-twelve source SHA-256 mismatch")
    orbits, owner = build_closure()
    distribution = [0] * len(orbits)
    witness_records = {index: record for _pair, index, record, _holes in REMOVAL_WITNESSES}
    seen_witnesses: set[int] = set()
    graph_count = 0
    with source12_path.open("rt", encoding="ascii") as stream:
        for graph_index, raw_line in enumerate(stream):
            record = raw_line.strip()
            if graph_index in witness_records:
                if record != witness_records[graph_index]:
                    raise ValueError(f"removal witness changed at source row {graph_index}")
                seen_witnesses.add(graph_index)
            graph = decode_graph6(record, 12)
            for positions in subset_positions():
                motif = owner.get(induced_mask(graph, positions))
                if motif is not None:
                    distribution[motif] += 1
                    break
            else:
                raise ValueError(
                    f"cover misses catalogue graph {graph_index}: {record}"
                )
            graph_count += 1
    if graph_count != EXPECTED_GRAPHS:
        raise ValueError(f"order-twelve source count changed: {graph_count}")
    if tuple(distribution) != EXPECTED_FIRST_HIT_DISTRIBUTION:
        raise ValueError(f"first-hit distribution changed: {distribution}")
    if seen_witnesses != set(witness_records):
        raise ValueError("one or more removal witnesses were absent")

    removal_checks = []
    for external_pair_id, index, record, catalogue_holes in REMOVAL_WITNESSES:
        local_signature = selected_pair_signature(record, owner)
        expected_local = EXPECTED_COVER_PAIR_IDS.index(external_pair_id)
        if local_signature != (expected_local,):
            raise ValueError(
                f"removal witness {index} has selected-pair signature {local_signature}"
            )
        removal_checks.append(
            {
                "external_pair_id_zero_based": external_pair_id,
                "catalogue_index_zero_based": index,
                "graph6": record,
                "selected_pair_signature_local": list(local_signature),
                "catalogue_holes_when_pair_removed": catalogue_holes,
            }
        )
    return {
        "schema_version": 1,
        "status": "PASS",
        "source": {
            "path": str(source12_path),
            "sha256": source_digest,
            "graphs": graph_count,
        },
        "cover": {
            "path": str(COVER_PATH),
            "sha256": sha256(COVER_PATH),
            "records": list(EXPECTED_RECORDS),
            "orbit_sizes": list(map(len, orbits)),
            "labelled_closure": len(owner),
            "labelled_closure_sha256": digest_masks(owner),
            "exact_complement_pairs": True,
        },
        "direct_replay": {
            "subsets_per_graph": len(subset_positions()),
            "covered": graph_count,
            "uncovered": 0,
            "first_hit_distribution": distribution,
            "incidence_read": False,
            "witness_file_read": False,
            "removal_witnesses": removal_checks,
        },
        "elapsed_seconds": time.perf_counter() - started,
        "scope": (
            "Direct exhaustive replay on the frozen official R(4,4,12) catalogue; "
            "catalogue-relative structural upper bound."
        ),
    }


# External IDs of the three selected complement pairs in the 181-pair ordering.
EXPECTED_COVER_PAIR_IDS = (40, 138, 144)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source12", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.source12), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
