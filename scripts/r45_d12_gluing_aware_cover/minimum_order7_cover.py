#!/usr/bin/env python3
"""Verify a five-pattern upper bound and a 25-graph lower-bound kernel.

The lower bound is independent of the large native incidence file.  It
reconstructs all labelled copies of the 362 official order-seven records,
checks their completeness by exhaustive enumeration of all 2^21 labelled
graphs, recomputes the motif signature of 25 explicit order-twelve graphs,
and proves that those 25 signatures have no hitting set of size at most four.
"""

from __future__ import annotations

import argparse
import functools
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence

from scripts.r45_d12_gluing_aware_cover import cover_audit
from scripts.r45_d12_gluing_aware_cover import verify_mixed_witness as independent
from scripts.r45_d12_structural_cover import structural_cover


HERE = Path(__file__).resolve().parent
COVER_PATH = HERE / "cover5_order7.tsv"
KERNEL_GRAPH_INDICES = (
    1_448_862,
    1_448_866,
    1_246_299,
    851_821,
    779_948,
    1_448_784,
    851_531,
    1_328_688,
    921_547,
    1_356_066,
    1_246_345,
    1_378_667,
    851_617,
    1_448_700,
    1_329_441,
    1_382_774,
    1_345_697,
    974_534,
    1_357_167,
    1_381_004,
    1_435_409,
    841_589,
    1_448_872,
    1_432_998,
    121_111,
)


def clique_masks(order: int, size: int) -> tuple[int, ...]:
    result = []
    for vertices in itertools.combinations(range(order), size):
        mask = 0
        for right_position in range(1, size):
            for left_position in range(right_position):
                mask |= 1 << independent.edge_position(
                    vertices[left_position], vertices[right_position]
                )
        result.append(mask)
    return tuple(result)


K4_MASKS_7 = clique_masks(7, 4)


def is_r44_order7_mask(mask: int) -> bool:
    return all(mask & clique not in (0, clique) for clique in K4_MASKS_7)


def labelled_catalogue_map(records: Sequence[str]) -> dict[int, int]:
    mapping: dict[int, int] = {}
    for candidate_id, record in enumerate(records):
        mask = independent.decode_graph6_mask(record, 7)
        if not is_r44_order7_mask(mask):
            raise ValueError(f"official candidate is not R(4,4,7): {record}")
        for permutation in itertools.permutations(range(7)):
            labelled = independent.relabelled_mask(mask, permutation)
            previous = mapping.setdefault(labelled, candidate_id)
            if previous != candidate_id:
                raise ValueError(
                    f"official records {previous} and {candidate_id} are isomorphic"
                )
    return mapping


def verify_order7_completeness(mapping: dict[int, int]) -> int:
    valid_count = 0
    for mask in range(1 << 21):
        valid = is_r44_order7_mask(mask)
        if valid:
            valid_count += 1
        if valid != (mask in mapping):
            raise ValueError(f"order-seven catalogue completeness failed at mask {mask}")
    if valid_count != len(mapping):
        raise AssertionError("labelled-map count mismatch")
    return valid_count


def source_records_at(path: Path, indices: Iterable[int]) -> dict[int, str]:
    wanted = set(indices)
    result: dict[int, str] = {}
    with path.open("rt", encoding="ascii") as stream:
        for index, line in enumerate(stream):
            if index in wanted:
                result[index] = line.strip()
    if result.keys() != wanted:
        raise ValueError("kernel graph index missing from source catalogue")
    return result


def kernel_signature(record: str, mapping: dict[int, int]) -> tuple[int, ...]:
    graph = independent.decode_graph6_mask(record, 12)
    k4_masks = clique_masks(12, 4)
    if any(graph & clique in (0, clique) for clique in k4_masks):
        raise ValueError("kernel witness is not an R(4,4,12) graph")
    signature: set[int] = set()
    for positions in independent.subset_positions(7):
        induced = independent.induced_mask(graph, positions)
        candidate = mapping.get(induced)
        if candidate is None:
            raise ValueError("kernel induced order-seven graph absent from complete map")
        signature.add(candidate)
    return tuple(sorted(signature))


def disjoint_clause_lower_bound(unhit: Sequence[int], stop_after: int) -> int:
    used = 0
    count = 0
    for clause in sorted(unhit, key=int.bit_count):
        if not clause & used:
            used |= clause
            count += 1
            if count > stop_after:
                return count
    return count


def find_hitting_set(
    clauses: Sequence[Sequence[int]], candidate_count: int, limit: int
) -> tuple[tuple[int, ...] | None, int]:
    clause_masks = tuple(sum(1 << candidate for candidate in clause) for clause in clauses)
    if any(not clause for clause in clause_masks):
        raise ValueError("empty hitting-set clause")
    explored = 0

    @functools.cache
    def search(selected: int) -> int | None:
        nonlocal explored
        explored += 1
        unhit = tuple(clause for clause in clause_masks if not clause & selected)
        if not unhit:
            return selected
        remaining = limit - selected.bit_count()
        if remaining <= 0:
            return None
        if disjoint_clause_lower_bound(unhit, remaining) > remaining:
            return None
        branch = min(unhit, key=int.bit_count)
        candidates = tuple(
            candidate for candidate in range(candidate_count) if branch >> candidate & 1
        )
        candidates = tuple(
            sorted(
                candidates,
                key=lambda candidate: sum(clause >> candidate & 1 for clause in unhit),
                reverse=True,
            )
        )
        for candidate in candidates:
            result = search(selected | 1 << candidate)
            if result is not None:
                return result
        return None

    result = search(0)
    selected = None if result is None else tuple(
        candidate for candidate in range(candidate_count) if result >> candidate & 1
    )
    return selected, explored


def sequential_at_most(candidate_count: int, limit: int) -> tuple[int, list[tuple[int, ...]]]:
    """Sinz sequential-counter encoding of sum(x_1..x_n) <= limit."""
    if candidate_count < 2 or not 1 <= limit < candidate_count:
        raise ValueError("unsupported sequential-counter dimensions")

    def auxiliary(prefix: int, count: int) -> int:
        if not 1 <= prefix < candidate_count or not 1 <= count <= limit:
            raise ValueError("invalid sequential-counter auxiliary")
        return candidate_count + (prefix - 1) * limit + count

    clauses: list[tuple[int, ...]] = []
    for index in range(1, candidate_count):
        clauses.append((-index, auxiliary(index, 1)))
    for index in range(2, candidate_count):
        for count in range(1, limit + 1):
            clauses.append((-auxiliary(index - 1, count), auxiliary(index, count)))
        for count in range(2, limit + 1):
            clauses.append(
                (-index, -auxiliary(index - 1, count - 1), auxiliary(index, count))
            )
    for index in range(2, candidate_count + 1):
        clauses.append((-index, -auxiliary(index - 1, limit)))
    return candidate_count + (candidate_count - 1) * limit, clauses


def cnf_bytes(candidate_count: int, signatures: Sequence[Sequence[int]], limit: int) -> bytes:
    variables, cardinality = sequential_at_most(candidate_count, limit)
    coverage = [tuple(candidate + 1 for candidate in signature) for signature in signatures]
    clauses = coverage + cardinality
    body = "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses)
    return f"p cnf {variables} {len(clauses)}\n".encode("ascii") + body.encode("ascii")


def verify(source: Path, exhaustive_order7: bool) -> dict[str, object]:
    sources = structural_cover.validate_source(source, (7, 8, 12))
    records7 = structural_cover.records(source / "r44_7.g6")
    if len(records7) != 362:
        raise ValueError("unexpected order-seven catalogue size")
    mapping = labelled_catalogue_map(records7)
    labelled_count = verify_order7_completeness(mapping) if exhaustive_order7 else None
    witnesses = source_records_at(source / "r44_12.g6", KERNEL_GRAPH_INDICES)
    signatures = tuple(kernel_signature(witnesses[index], mapping) for index in KERNEL_GRAPH_INDICES)
    hitting4, explored4 = find_hitting_set(signatures, len(records7), 4)
    if hitting4 is not None:
        raise ValueError(f"lower-bound kernel has a size-four hitting set: {hitting4}")
    cover = cover_audit.cover_records(COVER_PATH)
    cover_ids = tuple(records7.index(record) for order, record in cover if order == 7)
    if len(cover_ids) != 5 or any(not set(cover_ids) & set(signature) for signature in signatures):
        raise ValueError("frozen cover5 does not hit its lower-bound kernel")
    kernel_rows = [
        {
            "catalogue_index_zero_based": index,
            "graph6": witnesses[index],
            "signature_candidate_ids_zero_based": list(signature),
            "signature_graph6": [records7[candidate] for candidate in signature],
        }
        for index, signature in zip(KERNEL_GRAPH_INDICES, signatures, strict=True)
    ]
    return {
        "schema_version": 1,
        "status": "PASS",
        "claim": (
            "The 25 explicit R(4,4,12) witnesses cannot all contain one of at most "
            "four order-seven R(4,4) motifs; the frozen five-motif set hits the kernel."
        ),
        "scope": (
            "Absolute lower bound for order-seven motif covers, conditional only on "
            "the independently checked graph6 records; not a mixed order-7/8 minimum."
        ),
        "sources": sources,
        "order7_completeness": {
            "checked_exhaustively": exhaustive_order7,
            "all_labelled_graphs_examined": (1 << 21) if exhaustive_order7 else None,
            "valid_labelled_r44_graphs": labelled_count,
            "catalogue_unlabelled_records": len(records7),
            "labelled_closure_size": len(mapping),
        },
        "upper_bound": {
            "cover_path": str(COVER_PATH),
            "cover_sha256": structural_cover.sha256(COVER_PATH),
            "candidate_ids_zero_based": list(cover_ids),
            "size": 5,
        },
        "lower_bound": {
            "maximum_forbidden_size": 4,
            "kernel_graphs": len(kernel_rows),
            "dfs_states_explored": explored4,
            "hitting_set_found": False,
            "rows": kernel_rows,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--exhaustive-order7", action="store_true")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--cnf", type=Path)
    args = parser.parse_args()
    report = verify(args.source, args.exhaustive_order7)
    if args.cnf:
        structural_cover.ensure_ssd(args.cnf)
        signatures = [row["signature_candidate_ids_zero_based"] for row in report["lower_bound"]["rows"]]
        payload = cnf_bytes(362, signatures, 4)
        if args.cnf.exists():
            raise FileExistsError(f"refusing to overwrite {args.cnf}")
        args.cnf.parent.mkdir(parents=True, exist_ok=True)
        args.cnf.write_bytes(payload)
        report["lower_bound"]["cnf"] = {
            "path": str(args.cnf),
            "sha256": structural_cover.sha256(args.cnf),
            "bytes": len(payload),
        }
    if args.report:
        structural_cover.ensure_ssd(args.report)
        if args.report.exists():
            raise FileExistsError(f"refusing to overwrite {args.report}")
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
