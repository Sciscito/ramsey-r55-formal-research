#!/usr/bin/env python3
"""Bounded SAT benchmark for the nine-pattern degree-twelve cover.

This is a proof-free strategy probe.  It fixes one labelled copy of each
order-seven motif on the first seven vertices of the twelve-vertex B block
and solves selected frozen left-catalogue leaves.  CNFs, logs, and reports
are required to live on the external S: drive.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
from pathlib import Path
from typing import Sequence

from scripts.r45_d12_conditioned_cover import conditioned_cover_probe as probe
from scripts.r45_d12_structural_cover import structural_cover
from scripts.r45_d12_structural_cover import verify_cover9


POLARITIES = ("raw_dimacs", "complemented_dimacs")


def motif_units(record: str, polarity: str) -> tuple[int, ...]:
    """Return the 21 B-block units for one labelled order-seven motif."""
    if polarity not in POLARITIES:
        raise ValueError(f"unknown graph6/DIMACS polarity {polarity!r}")
    graph = structural_cover.ramsey.decode_graph6(record)
    if len(graph) != 7:
        raise ValueError("cover motif must have order seven")
    units: list[int] = []
    for left in range(7):
        for right in range(left + 1, 7):
            variable = structural_cover.ramsey.edge_var(
                probe.ORDER, probe.B_OFFSET + left, probe.B_OFFSET + right
            )
            edge = bool((graph[left] >> right) & 1)
            positive = edge if polarity == "raw_dimacs" else not edge
            units.append(variable if positive else -variable)
    if len(units) != 21 or len(set(map(abs, units))) != 21:
        raise AssertionError("motif did not produce 21 distinct units")
    if any(not 211 <= abs(literal) <= 256 for literal in units):
        raise AssertionError("motif unit escaped the first seven B vertices")
    return tuple(sorted(units, key=abs))


def parse_types(specification: str) -> tuple[int, ...]:
    result: set[int] = set()
    for field in specification.split(","):
        field = field.strip()
        if not field:
            continue
        if "-" in field:
            start_text, end_text = field.split("-", 1)
            start, end = int(start_text), int(end_text)
            result.update(range(start, end + 1))
        else:
            result.add(int(field))
    selected = tuple(sorted(result))
    if not selected or any(not 0 <= index < 12 for index in selected):
        raise ValueError("types must be a nonempty subset of 0..11")
    return selected


def run(args: argparse.Namespace) -> dict[str, object]:
    output = probe.require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "benchmark.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    cover_path = args.cover.resolve()
    records = verify_cover9.cover_records(cover_path)
    if records != verify_cover9.EXPECTED_RECORDS:
        raise ValueError("benchmark requires the frozen cover9 record order")
    selected_types = parse_types(args.types)
    jobs: list[tuple[int, int, str, Path, tuple[int, ...]]] = []
    for type_index in selected_types:
        source = args.leaf_directory / f"leaf_{type_index + 1:02d}.cnf"
        if probe.cnf_header(source) != (probe.BASE_VARIABLES, probe.EXPECTED_BASE_CLAUSES):
            raise ValueError(f"unexpected frozen leaf header: {source}")
        for motif_index, record in enumerate(records):
            jobs.append(
                (type_index, motif_index, record, source, motif_units(record, args.polarity))
            )

    def execute(job: tuple[int, int, str, Path, tuple[int, ...]]) -> dict[str, object]:
        type_index, motif_index, record, source, units = job
        stem = f"type_{type_index:02d}_motif_{motif_index:02d}"
        cnf = output / f"{stem}.cnf"
        log = output / f"{stem}.log"
        probe.write_conditioned_cnf(source, cnf, units)
        solver_result = probe.solve(
            args.solver,
            cnf,
            conflict_limit=args.conflicts,
            timeout_seconds=args.timeout,
            log=log,
        )
        return {
            "type_index_zero_based": type_index,
            "motif_index_zero_based": motif_index,
            "graph6": record,
            "polarity": args.polarity,
            "units": list(units),
            "source": {"path": str(source), "sha256": probe.sha256_file(source)},
            "cnf": {
                "path": str(cnf),
                "sha256": probe.sha256_file(cnf),
                "bytes": cnf.stat().st_size,
                "clauses": probe.EXPECTED_BASE_CLAUSES + 21,
            },
            "solver": solver_result,
        }

    rows: list[dict[str, object]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {executor.submit(execute, job): job for job in jobs}
        for future in concurrent.futures.as_completed(futures):
            row = future.result()
            rows.append(row)
            print(
                f"type={row['type_index_zero_based']} motif={row['motif_index_zero_based']} "
                f"status={row['solver']['status']} conflicts={row['solver']['conflicts']} "
                f"wall={row['solver']['wall_seconds']}s",
                flush=True,
            )
    rows.sort(key=lambda row: (row["type_index_zero_based"], row["motif_index_zero_based"]))
    statuses = ("UNSAT", "SAT", "UNKNOWN", "TIMEOUT")
    report = {
        "schema_version": 1,
        "status": "PROOF_FREE_BOUNDED_GLUING_BENCHMARK",
        "scope": "frozen degree-twelve left leaves crossed with labelled cover9 motifs",
        "warning": "bounded solver outcomes are not LRAT proofs and do not close a cover case",
        "cover": {"path": str(cover_path), "sha256": probe.sha256_file(cover_path)},
        "polarity": {
            "name": args.polarity,
            "raw_dimacs": "graph6 edge -> positive DIMACS/red literal",
            "complemented_dimacs": "graph6 edge -> negative DIMACS literal",
        },
        "solver": str(args.solver),
        "limits": {
            "conflicts_per_leaf": args.conflicts,
            "timeout_seconds_per_leaf": args.timeout,
            "workers": args.workers,
        },
        "types": list(selected_types),
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
    parser.add_argument(
        "--cover", type=Path, default=Path(__file__).with_name("cover9.tsv")
    )
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--types", default="0")
    parser.add_argument("--polarity", choices=POLARITIES, default="raw_dimacs")
    parser.add_argument("--conflicts", type=int, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError("workers must be positive")
    report = run(args)
    print(json.dumps({"report": str(args.output / 'benchmark.json'), "status_counts": report["status_counts"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
