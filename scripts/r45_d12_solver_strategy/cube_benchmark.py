#!/usr/bin/env python3
"""Run a bounded, proof-free cube-and-conquer probe on one d12 leaf.

All generated CNFs and the JSON result must live under an explicit S: path.
The cubes form the complete truth table of the requested variables, so this
experiment has a simple future iCNF/LRAT cover.  The current command does not
write proofs and therefore only measures search difficulty.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path, PureWindowsPath


def require_ssd(path: Path) -> Path:
    if PureWindowsPath(str(path)).drive.upper() != "S:":
        raise ValueError(f"path must be explicitly rooted on S:, got {path}")
    return path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def header(path: Path) -> tuple[int, int]:
    with path.open("r", encoding="ascii") as stream:
        for line in stream:
            if line.startswith("p cnf "):
                fields = line.split()
                return int(fields[2]), int(fields[3])
    raise ValueError(f"missing DIMACS header in {path}")


def materialize_cube(source: Path, target: Path, variables: int, clauses: int,
                     cube: tuple[int, ...]) -> None:
    if target.exists():
        return
    partial = target.with_name(target.name + ".partial")
    with source.open("r", encoding="ascii") as input_stream, partial.open(
        "w", encoding="ascii", newline="\n"
    ) as output_stream:
        replaced = False
        for line in input_stream:
            if line.startswith("p cnf "):
                if replaced:
                    raise ValueError("multiple DIMACS headers")
                output_stream.write(f"p cnf {variables} {clauses + len(cube)}\n")
                replaced = True
            else:
                output_stream.write(line)
        if not replaced:
            raise ValueError("missing DIMACS header")
        for literal in cube:
            output_stream.write(f"{literal} 0\n")
    partial.replace(target)


def parse_solver(output: str, returncode: int) -> tuple[str, int | None, float | None]:
    if returncode == 20 or "s UNSATISFIABLE" in output:
        status = "UNSAT"
    elif returncode == 10 or "s SATISFIABLE" in output:
        status = "SAT"
    else:
        status = "UNKNOWN"
    conflicts = re.findall(r"^c conflicts:\s+([0-9]+)", output, re.MULTILINE)
    seconds = re.findall(
        r"^c total process time since initialization:\s+([0-9.]+)",
        output,
        re.MULTILINE,
    )
    return (
        status,
        int(conflicts[-1]) if conflicts else None,
        float(seconds[-1]) if seconds else None,
    )


def solve_one(solver: Path, cnf: Path, cube_index: int, cube: tuple[int, ...],
              conflict_limit: int, timeout: float) -> dict[str, object]:
    command = [
        str(solver), "--unsat", "--walk=false", "-n", "-c",
        str(conflict_limit), str(cnf),
    ]
    started = time.perf_counter()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            check=False,
        )
        output = completed.stdout
        returncode = completed.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        output = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        returncode = None
    wall = time.perf_counter() - started
    status, conflicts, solver_seconds = parse_solver(output, returncode or 0)
    if timed_out:
        status = "TIMEOUT"
    return {
        "cube_index": cube_index,
        "cube": list(cube),
        "status": status,
        "conflicts": conflicts,
        "wall_seconds": round(wall, 3),
        "solver_seconds": solver_seconds,
        "returncode": returncode,
        "cnf": cnf.name,
        "cnf_sha256": sha256(cnf),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--variables", required=True,
                        help="comma-separated DIMACS variables")
    parser.add_argument("--conflicts", type=int, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    output = require_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / "results.json"
    if result_path.exists():
        raise FileExistsError(f"refusing to overwrite {result_path}")
    cube_variables = tuple(int(value) for value in args.variables.split(","))
    variable_count, clause_count = header(args.input)
    if not cube_variables or len(set(cube_variables)) != len(cube_variables):
        raise ValueError("cube variables must be nonempty and distinct")
    if any(variable < 1 or variable > variable_count for variable in cube_variables):
        raise ValueError("cube variable outside DIMACS header")
    work: list[tuple[Path, int, tuple[int, ...]]] = []
    for index in range(1 << len(cube_variables)):
        cube = tuple(
            variable if (index >> bit) & 1 else -variable
            for bit, variable in enumerate(cube_variables)
        )
        cnf = output / f"cube_{index:0{max(2, len(cube_variables))}d}.cnf"
        materialize_cube(args.input, cnf, variable_count, clause_count, cube)
        work.append((cnf, index, cube))
    started = time.perf_counter()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = [
            executor.submit(
                solve_one, args.solver, cnf, index, cube,
                args.conflicts, args.timeout,
            )
            for cnf, index, cube in work
        ]
        rows = [future.result() for future in futures]
    rows.sort(key=lambda row: int(row["cube_index"]))
    summary = {
        "schema_version": 1,
        "proof_status": "PROOF_FREE_SEARCH_PROBE_ONLY",
        "input": str(args.input),
        "input_sha256": sha256(args.input),
        "solver": str(args.solver),
        "cube_variables": list(cube_variables),
        "cube_count": len(rows),
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
        "cube_variables", "cube_count", "conflict_limit_per_cube", "jobs",
        "wall_seconds_total", "status_counts", "total_reported_conflicts",
    )}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
