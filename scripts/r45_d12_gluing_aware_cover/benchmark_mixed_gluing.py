#!/usr/bin/env python3
"""Proof-free bounded SAT benchmark for order-7/order-8 motif covers."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
from pathlib import Path

from scripts.r45_d12_conditioned_cover import conditioned_cover_probe as probe
from scripts.r45_d12_gluing_aware_cover import cover_audit
from scripts.r45_d12_structural_cover import structural_cover


POLARITIES = ("raw_dimacs", "complemented_dimacs")


def motif_units(order: int, record: str, polarity: str) -> tuple[int, ...]:
    if polarity not in POLARITIES:
        raise ValueError(f"unknown polarity {polarity!r}")
    graph = structural_cover.ramsey.decode_graph6(record)
    if len(graph) != order or order not in (7, 8):
        raise ValueError("motif order mismatch")
    units: list[int] = []
    for left in range(order):
        for right in range(left + 1, order):
            variable = structural_cover.ramsey.edge_var(
                probe.ORDER, probe.B_OFFSET + left, probe.B_OFFSET + right
            )
            edge = bool((graph[left] >> right) & 1)
            positive = edge if polarity == "raw_dimacs" else not edge
            units.append(variable if positive else -variable)
    expected = order * (order - 1) // 2
    if len(units) != expected or len(set(map(abs, units))) != expected:
        raise AssertionError("motif units are not distinct")
    if any(not 211 <= abs(literal) <= 276 for literal in units):
        raise AssertionError("motif unit escaped the B block")
    return tuple(sorted(units, key=abs))


def run(args: argparse.Namespace) -> dict[str, object]:
    output = probe.require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "benchmark.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    source_leaf = args.leaf_directory / f"leaf_{args.type_index + 1:02d}.cnf"
    if probe.cnf_header(source_leaf) != (probe.BASE_VARIABLES, probe.EXPECTED_BASE_CLAUSES):
        raise ValueError(f"unexpected frozen leaf header: {source_leaf}")
    records = cover_audit.cover_records(args.cover.resolve())

    def execute(job: tuple[int, tuple[int, str]]) -> dict[str, object]:
        motif_index, (order, record) = job
        units = motif_units(order, record, args.polarity)
        stem = f"motif_{motif_index:02d}_order_{order}"
        cnf, log = output / f"{stem}.cnf", output / f"{stem}.log"
        probe.write_conditioned_cnf(source_leaf, cnf, units)
        result = probe.solve(
            args.solver,
            cnf,
            conflict_limit=args.conflicts,
            timeout_seconds=args.timeout,
            log=log,
        )
        return {
            "motif_index_zero_based": motif_index,
            "order": order,
            "graph6": record,
            "edges": structural_cover.edge_count(record),
            "unit_count": len(units),
            "units": list(units),
            "cnf": {
                "path": str(cnf),
                "sha256": probe.sha256_file(cnf),
                "clauses": probe.EXPECTED_BASE_CLAUSES + len(units),
            },
            "solver": result,
        }

    rows: list[dict[str, object]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = [executor.submit(execute, job) for job in enumerate(records)]
        for future in concurrent.futures.as_completed(futures):
            row = future.result()
            rows.append(row)
            print(
                f"motif={row['motif_index_zero_based']} order={row['order']} "
                f"status={row['solver']['status']} conflicts={row['solver']['conflicts']} "
                f"wall={row['solver']['wall_seconds']}s",
                flush=True,
            )
    rows.sort(key=lambda row: row["motif_index_zero_based"])
    statuses = ("UNSAT", "SAT", "UNKNOWN", "TIMEOUT")
    report = {
        "schema_version": 1,
        "status": "PROOF_FREE_BOUNDED_GLUING_BENCHMARK",
        "warning": "Bounded solver outcomes are not LRAT proofs and close no cover case.",
        "cover": {"path": str(args.cover.resolve()), "sha256": probe.sha256_file(args.cover)},
        "leaf_type_index_zero_based": args.type_index,
        "polarity": args.polarity,
        "limits": {"conflicts_per_leaf": args.conflicts, "timeout_seconds": args.timeout},
        "workers": args.workers,
        "status_counts": {
            status: sum(row["solver"]["status"] == status for row in rows)
            for status in statuses
        },
        "rows": rows,
    }
    probe.write_new_bytes(report_path, probe.json_bytes(report))
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--leaf-directory", type=Path, required=True)
    parser.add_argument("--cover", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--type-index", type=int, default=0)
    parser.add_argument("--polarity", choices=POLARITIES, default="raw_dimacs")
    parser.add_argument("--conflicts", type=int, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if not 0 <= args.type_index < 12 or args.workers < 1:
        raise ValueError("invalid type index or worker count")
    report = run(args)
    print(json.dumps({"report": str(args.output / 'benchmark.json'), "status_counts": report["status_counts"]}, indent=2))


if __name__ == "__main__":
    main()
