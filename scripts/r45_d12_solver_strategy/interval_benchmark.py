#!/usr/bin/env python3
"""Bounded solver benchmark for the exact cross-row interval cubes."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import time
from pathlib import Path

import cross_interval_cover as intervals
import cube_benchmark as benchmark
import strategy_probe as strategy


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--catalogue-index", type=int, required=True)
    parser.add_argument("--b-vertex", type=int, default=12)
    parser.add_argument("--conflicts", type=int, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    output = benchmark.require_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / "results.json"
    if result_path.exists():
        raise FileExistsError(f"refusing to overwrite {result_path}")
    records = tuple(
        line.strip()
        for line in intervals.CATALOGUE_PATH.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    if not 0 <= args.catalogue_index < len(records):
        raise ValueError("catalogue index outside 0..11")
    graph = intervals.ramsey.decode_graph6(records[args.catalogue_index])
    blocks = intervals.independent_four_masks(graph)
    abstract_cubes = intervals.optimal_disjoint_cover(blocks)
    variable_count, clause_count = benchmark.header(args.input)
    work: list[tuple[Path, int, tuple[int, ...]]] = []
    for index, (red, blue) in enumerate(abstract_cubes):
        cube: list[int] = []
        for a_vertex in range(12):
            variable = strategy.ramsey.edge_var(24, a_vertex, args.b_vertex)
            if (red >> a_vertex) & 1:
                cube.append(variable)
            elif (blue >> a_vertex) & 1:
                cube.append(-variable)
        cnf = output / f"interval_{index:03d}.cnf"
        benchmark.materialize_cube(
            args.input, cnf, variable_count, clause_count, tuple(cube)
        )
        work.append((cnf, index, tuple(cube)))
    started = time.perf_counter()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = [
            executor.submit(
                benchmark.solve_one,
                args.solver,
                cnf,
                index,
                cube,
                args.conflicts,
                args.timeout,
            )
            for cnf, index, cube in work
        ]
        rows = [future.result() for future in futures]
    rows.sort(key=lambda row: int(row["cube_index"]))
    summary = {
        "schema_version": 1,
        "proof_status": "PROOF_FREE_SEARCH_PROBE_ONLY",
        "input": str(args.input),
        "input_sha256": benchmark.sha256(args.input),
        "catalogue_index": args.catalogue_index,
        "catalogue_record": records[args.catalogue_index],
        "b_vertex": args.b_vertex,
        "admissible_interval_cubes": len(rows),
        "invalid_blue_K4_cubes_needed_for_unconditional_cover": len(blocks),
        "conflict_limit_per_cube": args.conflicts,
        "timeout_seconds_per_cube": args.timeout,
        "jobs": args.jobs,
        "wall_seconds_total": round(time.perf_counter() - started, 3),
        "status_counts": {
            status: sum(row["status"] == status for row in rows)
            for status in ("UNSAT", "SAT", "UNKNOWN", "TIMEOUT")
        },
        "total_reported_conflicts": sum(
            int(row["conflicts"]) for row in rows if row["conflicts"] is not None
        ),
        "rows": rows,
    }
    partial = result_path.with_name(result_path.name + ".partial")
    partial.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    partial.replace(result_path)
    print(json.dumps({key: summary[key] for key in (
        "catalogue_index", "admissible_interval_cubes",
        "invalid_blue_K4_cubes_needed_for_unconditional_cover",
        "conflict_limit_per_cube", "jobs", "wall_seconds_total",
        "status_counts", "total_reported_conflicts",
    )}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
