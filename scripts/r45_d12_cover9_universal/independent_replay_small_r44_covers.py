#!/usr/bin/env python3
"""Independent stdlib replay of the explicit R(4,4;10/11) motif covers.

This verifier intentionally imports no project generator.  It uses adjacency
rows rather than the pilot's graph6 integer representation, reconstructs every
labelled motif orbit, validates every source record as R(4,4), and scans all
seven-subsets until each declared family is witnessed.
"""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import hashlib
import itertools
import json
import time
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
DEFAULT_MANIFEST = HERE / "R44_SMALL_ORDER_MOTIF_COVERS_2026-08-07.json"
DEFAULT_MANIFEST_SHA = HERE / "R44_SMALL_ORDER_MOTIF_COVERS_2026-08-07.sha256"
EXPECTED_ACTIVE_STRATA = tuple(
    [(20, common) for common in range(2, 10)]
    + [(22, common) for common in range(4, 11)]
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def checked_identity(path: Path, entry: dict[str, object]) -> None:
    observed = (path.stat().st_size, sha256(path))
    expected = (entry["bytes"], entry["sha256"])
    if observed != expected:
        raise ValueError(f"frozen identity mismatch for {path}: {observed} != {expected}")


def decode_graph6_rows(record: str, expected_order: int) -> tuple[int, ...]:
    edge_count = expected_order * (expected_order - 1) // 2
    expected_length = 1 + (edge_count + 5) // 6
    if len(record) != expected_length or ord(record[0]) - 63 != expected_order:
        raise ValueError(f"wrong graph6 order or length: {record!r}")
    bits: list[int] = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 character: {record!r}")
        bits.extend(value >> shift & 1 for shift in range(5, -1, -1))
    if any(bits[edge_count:]):
        raise ValueError(f"nonzero graph6 padding: {record!r}")
    rows = [0] * expected_order
    position = 0
    for right in range(1, expected_order):
        for left in range(right):
            if bits[position]:
                rows[left] |= 1 << right
                rows[right] |= 1 << left
            position += 1
    return tuple(rows)


def local_mask(rows: Sequence[int], vertices: Sequence[int]) -> int:
    result = 0
    target = 0
    for right in range(1, len(vertices)):
        for left in range(right):
            result |= ((rows[vertices[left]] >> vertices[right]) & 1) << target
            target += 1
    return result


def labelled_orbit(record: str) -> frozenset[int]:
    rows = decode_graph6_rows(record, 7)
    return frozenset(local_mask(rows, permutation) for permutation in itertools.permutations(range(7)))


def build_closure(records: Sequence[str]) -> frozenset[int]:
    if len(set(records)) != len(records):
        raise ValueError("motif family contains duplicate graph6 records")
    masks4 = clique_masks(7)
    for record in records:
        assert_r44(decode_graph6_rows(record, 7), masks4, record)
    orbits = [labelled_orbit(record) for record in records]
    result = frozenset().union(*orbits)
    if sum(map(len, orbits)) != len(result):
        raise ValueError("motif family repeats an isomorphism class")
    return result


def assert_complement_closed(closure: frozenset[int]) -> None:
    full = (1 << 21) - 1
    if {full ^ mask for mask in closure} != closure:
        raise ValueError("declared complement-closed family is not closed")


def tsv_records(path: Path) -> tuple[str, ...]:
    records = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="ascii").splitlines(), 1
    ):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise ValueError(f"invalid order-seven cover row {line_number}")
        records.append(fields[1])
    return tuple(records)


def clique_masks(order: int) -> tuple[int, ...]:
    def position(left: int, right: int) -> int:
        if left > right:
            left, right = right, left
        return right * (right - 1) // 2 + left

    return tuple(
        sum(1 << position(left, right) for left, right in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(order), 4)
    )


def global_mask(rows: Sequence[int]) -> int:
    result = 0
    position = 0
    for right in range(1, len(rows)):
        for left in range(right):
            result |= ((rows[left] >> right) & 1) << position
            position += 1
    return result


def assert_r44(rows: Sequence[int], masks4: Sequence[int], record: str) -> None:
    graph = global_mask(rows)
    for mask in masks4:
        observed = graph & mask
        if observed == 0 or observed == mask:
            raise ValueError(f"source contains a non-R44 record: {record}")


def verify_catalogue(
    source: Path,
    order: int,
    expected_source: dict[str, object],
    individual: frozenset[int],
    closed: frozenset[int],
) -> dict[str, object]:
    identity = (source.stat().st_size, sha256(source))
    expected_identity = (expected_source["bytes"], expected_source["sha256"])
    if identity != expected_identity:
        raise ValueError(f"R(4,4;{order}) identity mismatch")
    subsets = tuple(itertools.combinations(range(order), 7))
    masks4 = clique_masks(order)
    graph_count = 0
    individual_first_hits = 0
    closed_first_hits = 0
    with gzip.open(source, "rt", encoding="ascii", newline="") as stream:
        for raw_line in stream:
            record = raw_line.strip()
            rows = decode_graph6_rows(record, order)
            assert_r44(rows, masks4, record)
            hit_individual = False
            hit_closed = False
            for vertices in subsets:
                induced = local_mask(rows, vertices)
                if not hit_individual and induced in individual:
                    hit_individual = True
                    individual_first_hits += 1
                if not hit_closed and induced in closed:
                    hit_closed = True
                    closed_first_hits += 1
                if hit_individual and hit_closed:
                    break
            if not hit_individual or not hit_closed:
                raise ValueError(
                    f"declared cover misses R(4,4;{order}) record {graph_count}: {record}"
                )
            graph_count += 1
    if graph_count != expected_source["records"]:
        raise ValueError(f"R(4,4;{order}) record count mismatch")
    return {
        "order": order,
        "graphs": graph_count,
        "subsets_per_graph": len(subsets),
        "all_sources_r44": True,
        "individual_covered": individual_first_hits,
        "complement_closed_covered": closed_first_hits,
        "uncovered": 0,
    }


def verify(
    manifest_path: Path,
    manifest_sha_path: Path,
    source10: Path,
    source11: Path,
) -> dict[str, object]:
    started = time.perf_counter()
    manifest_digest = sha256(manifest_path)
    expected_manifest_digest = manifest_sha_path.read_text(encoding="ascii").strip()
    if manifest_digest != expected_manifest_digest:
        raise ValueError("small-order cover manifest SHA-256 mismatch")
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1 or data.get("proof_level") != 1:
        raise ValueError("unexpected small-order cover manifest schema")
    for name, entry in data["programs"].items():
        checked_identity((manifest_path.parent / name).resolve(), entry)
    dependencies = data["dependencies"]
    vacuity = dependencies["minimum_anchor_vacuity_document"]
    if sha256((manifest_path.parent / vacuity["path"]).resolve()) != vacuity["sha256"]:
        raise ValueError("minimum-anchor vacuity document identity mismatch")
    cover5_dependency = dependencies["cover5_order12_replay"]
    cover5_path = (manifest_path.parent / cover5_dependency["tsv_path"]).resolve()
    if sha256(cover5_path) != cover5_dependency["tsv_sha256"]:
        raise ValueError("order-twelve cover5 identity mismatch")
    cover5_report = (manifest_path.parent / cover5_dependency["report_path"]).resolve()
    if sha256(cover5_report) != cover5_dependency["report_sha256"]:
        raise ValueError("order-twelve cover5 report identity mismatch")
    cover6_dependency = dependencies["cover6_order12_replay"]
    cover6_path = (manifest_path.parent / cover6_dependency["tsv_path"]).resolve()
    if sha256(cover6_path) != cover6_dependency["tsv_sha256"]:
        raise ValueError("order-twelve cover6 identity mismatch")
    cover6_manifest = (manifest_path.parent / cover6_dependency["manifest_path"]).resolve()
    if sha256(cover6_manifest) != cover6_dependency["manifest_sha256"]:
        raise ValueError("order-twelve cover6 manifest identity mismatch")
    if tsv_records(cover5_path) != tuple(data["q_at_least_12"]["individual_records"]):
        raise ValueError("q>=12 individual motif family changed")
    if tsv_records(cover6_path) != tuple(data["q_at_least_12"]["complement_closed_records"]):
        raise ValueError("q>=12 complement-closed motif family changed")
    build_closure(tuple(data["q_at_least_12"]["individual_records"]))
    q12_closed = build_closure(tuple(data["q_at_least_12"]["complement_closed_records"]))
    assert_complement_closed(q12_closed)
    closures = {}
    for order in (10, 11):
        entry = data[f"q{order}"]
        individual_records = tuple(entry["individual_records"])
        closed_records = tuple(entry["complement_closed_records"])
        if len(individual_records) != entry["individual_motifs"]:
            raise ValueError(f"q{order} individual motif count mismatch")
        if len(closed_records) != entry["complement_closed_motifs"]:
            raise ValueError(f"q{order} closed motif count mismatch")
        individual = build_closure(individual_records)
        closed = build_closure(closed_records)
        assert_complement_closed(closed)
        closures[order] = (individual, closed)
    sources = {10: source10, 11: source11}
    results = [
        verify_catalogue(
            sources[order],
            order,
            data["official_sources"][f"r44_{order}_gzip"],
            *closures[order],
        )
        for order in (10, 11)
    ]
    architecture = data["k45_architecture"]
    active = architecture["active_strata"]
    observed_strata = tuple((row["degree"], row["common"]) for row in active)
    if observed_strata != EXPECTED_ACTIVE_STRATA:
        raise ValueError("active K45 numerical strata changed")
    if any(row["q"] != row["degree"] - 1 - row["common"] for row in active):
        raise ValueError("exclusive-block order q is inconsistent")
    if sum(row["typed_types"] for row in active) != architecture["typed_minimum_anchor_branches_before"]:
        raise ValueError("typed K45 branch total is inconsistent")
    q_counts = Counter(row["q"] for row in active)
    if sum(count for q, count in q_counts.items() if q >= 12) != 12:
        raise ValueError("q>=12 stratum multiplicity changed")
    if q_counts[11] != 2 or q_counts[10] != 1:
        raise ValueError("q10/q11 stratum multiplicity changed")
    if data["dependencies"]["eliminated_q9_stratum"] != {"degree": 20, "common": 10, "q": 9}:
        raise ValueError("d20,c10 vacuity dependency changed")
    individual_total = (
        sum(count for q, count in q_counts.items() if q >= 12)
        * data["q_at_least_12"]["individual_motifs"]
        + q_counts[11] * data["q11"]["individual_motifs"]
        + q_counts[10] * data["q10"]["individual_motifs"]
    )
    closed_total = (
        sum(count for q, count in q_counts.items() if q >= 12)
        * data["q_at_least_12"]["complement_closed_motifs"]
        + q_counts[11] * data["q11"]["complement_closed_motifs"]
        + q_counts[10] * data["q10"]["complement_closed_motifs"]
    )
    if individual_total != 112:
        raise ValueError("individual K45 obligation arithmetic mismatch")
    if closed_total != 126:
        raise ValueError("closed K45 obligation arithmetic mismatch")
    if architecture["individual_motif_obligations"] != 112 or architecture["complement_closed_motif_obligations"] != 126:
        raise ValueError("recorded K45 obligation totals changed")
    return {
        "schema_version": 1,
        "status": "PASS",
        "proof_level": 1,
        "manifest": {
            "path": str(manifest_path),
            "sha256": manifest_digest,
            "sha_file": str(manifest_sha_path),
        },
        "catalogues": results,
        "k45_obligation_arithmetic": {"individual": 112, "complement_closed": 126},
        "scope": "Independent catalogue-relative replay; no minimality, universal theorem, SAT closure, formal K45 bridge, or new Ramsey bound.",
        "elapsed_seconds": time.perf_counter() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--manifest-sha", type=Path, default=DEFAULT_MANIFEST_SHA)
    parser.add_argument("--source10", type=Path, required=True)
    parser.add_argument("--source11", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = verify(args.manifest, args.manifest_sha, args.source10, args.source11)
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        if args.output.exists():
            raise FileExistsError(f"refusing to replace replay report: {args.output}")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
