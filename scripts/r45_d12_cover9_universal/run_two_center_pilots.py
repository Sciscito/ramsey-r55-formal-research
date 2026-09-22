#!/usr/bin/env python3
"""Run bounded proof-free pilots on every uncertified two-centre case."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

from . import generate_two_center_branches as two
from . import generate_universal as universal
from .run_solver_pilot import classify, profile_flags, sha256


CERTIFIED_CASE = (2, 0)
PROGRESS_SYMBOLS = set("*{}-iIBFO#sw^0")


def write_new_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def parse_metrics(log_text: str) -> dict[str, float | int | None]:
    parse_match = re.search(r"parsed \d+ clauses in ([0-9.]+) seconds", log_text)
    conflicts_match = re.search(r"^c conflicts:\s+(\d+)", log_text, re.MULTILINE)
    search_match = re.search(
        r"^c\s+([0-9.]+)\s+[0-9.]+% solve$", log_text, re.MULTILINE
    )
    last_time: float | None = None
    last_conflicts: int | None = None
    for line in log_text.splitlines():
        fields = line.split()
        if (
            len(fields) >= 8
            and fields[0] == "c"
            and fields[1] in PROGRESS_SYMBOLS
        ):
            try:
                last_time = float(fields[2])
                last_conflicts = int(fields[7])
            except ValueError:
                continue
    parse_seconds = float(parse_match.group(1)) if parse_match else None
    conflicts = int(conflicts_match.group(1)) if conflicts_match else last_conflicts
    search_seconds = float(search_match.group(1)) if search_match else None
    if search_seconds is None and last_time is not None and parse_seconds is not None:
        search_seconds = max(0.0, last_time - parse_seconds)
    return {
        "parse_seconds": parse_seconds,
        "search_seconds": search_seconds,
        "conflicts": conflicts,
        "last_solver_seconds": last_time,
    }


def run_case(
    directory: Path,
    batch: Path,
    solver: Path,
    solver_hash: str,
    row: dict[str, object],
    conflicts: int,
    timeout: float,
    profile: str,
) -> dict[str, object]:
    p, q = int(row["p"]), int(row["q"])
    formula = row["formula"]
    if not isinstance(formula, dict):
        raise ValueError("malformed formula metadata")
    path = directory / str(formula["name"])
    stem = f"p{p}_q{q}_c{conflicts}_t{timeout:g}"
    log_path = batch / f"{stem}.log"
    json_path = batch / f"{stem}.json"
    flags = profile_flags(profile)
    command = [str(solver), *flags, "-c", str(conflicts), str(path)]
    started = dt.datetime.now(dt.timezone.utc)
    before = time.perf_counter()
    timed_out = False
    returncode: int | None = None
    with log_path.open("xb") as stream:
        try:
            completed = subprocess.run(
                command,
                stdout=stream,
                stderr=subprocess.STDOUT,
                timeout=timeout,
                check=False,
            )
            returncode = completed.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
    elapsed = time.perf_counter() - before
    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    if timed_out:
        status = "TIMEOUT"
    else:
        try:
            status = classify(returncode, log_text)  # type: ignore[arg-type]
        except RuntimeError:
            status = f"ERROR_RETURN_CODE_{returncode}"
    result = {
        "schema_version": 1,
        "status": status,
        "certified": False,
        "proof_emitted": False,
        "case": {"p": p, "q": q},
        "started_utc": started.isoformat(),
        "elapsed_seconds": elapsed,
        "timeout_seconds": timeout,
        "conflict_limit": conflicts,
        "returncode": returncode,
        "command": [solver.name, *flags, "-c", str(conflicts), path.name],
        "solver": {"path": str(solver), "sha256": solver_hash},
        "formula": formula,
        "metrics": parse_metrics(log_text),
        "log": {
            "name": log_path.name,
            "bytes": log_path.stat().st_size,
            "sha256": sha256(log_path),
        },
    }
    write_new_json(json_path, result)
    result["result_manifest"] = {
        "name": json_path.name,
        "bytes": json_path.stat().st_size,
        "sha256": sha256(json_path),
    }
    return result


def run(
    output: Path,
    solver: Path,
    batch_name: str,
    conflicts: int,
    timeout: float,
    profile: str,
) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    if Path(batch_name).name != batch_name:
        raise ValueError("batch name must be local")
    if conflicts <= 0 or timeout <= 0:
        raise ValueError("limits must be positive")
    if not solver.is_file():
        raise FileNotFoundError(solver)
    two.verify(output)
    directory = output / two.OUTPUT_DIRECTORY
    manifest_path = directory / two.SUMMARY_NAME
    source_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    batch = directory / batch_name
    if batch.exists():
        raise FileExistsError(f"refusing existing batch directory: {batch}")
    batch.mkdir()
    solver_hash = sha256(solver)
    results = []
    before = time.perf_counter()
    for row in source_manifest["cases"]:
        case = (int(row["p"]), int(row["q"]))
        if case == CERTIFIED_CASE:
            continue
        result = run_case(
            directory,
            batch,
            solver,
            solver_hash,
            row,
            conflicts,
            timeout,
            profile,
        )
        results.append(result)
        metrics = result["metrics"]
        print(
            f"p={case[0]} q={case[1]} {result['status']} "
            f"conflicts={metrics['conflicts']} elapsed={result['elapsed_seconds']:.3f}s",
            flush=True,
        )
    summary = {
        "schema_version": 1,
        "status": "PROOF_FREE_BATCH_COMPLETE",
        "warning": "No LRAT was requested or emitted; UNSAT statuses are performance evidence only.",
        "excluded_certified_case": list(CERTIFIED_CASE),
        "source_manifest": {
            "path": str(manifest_path),
            "sha256": sha256(manifest_path),
        },
        "solver": {"path": str(solver), "sha256": solver_hash},
        "profile": profile,
        "conflict_limit": conflicts,
        "timeout_seconds_per_case": timeout,
        "total_elapsed_seconds": time.perf_counter() - before,
        "results": results,
    }
    write_new_json(batch / "batch_manifest.json", summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--batch-name", required=True)
    parser.add_argument("--conflicts", required=True, type=int)
    parser.add_argument("--timeout", required=True, type=float)
    parser.add_argument(
        "--profile", choices=("unsat", "plain", "default"), default="unsat"
    )
    args = parser.parse_args()
    result = run(
        args.output,
        args.solver,
        args.batch_name,
        args.conflicts,
        args.timeout,
        args.profile,
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
