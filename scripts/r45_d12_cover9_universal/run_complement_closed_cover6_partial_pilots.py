#!/usr/bin/env python3
"""Run bounded proof-free pilots on an explicitly partial cover6 snapshot."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import time
from pathlib import Path

from . import generate_complement_closed_cover6_two_center as two
from . import generate_universal as universal
from . import run_complement_closed_cover6_pilots as pilots
from . import snapshot_complement_closed_cover6_partial as snapshot
from .run_solver_pilot import sha256


def run(
    output: Path,
    solver: Path,
    batch_name: str,
    conflicts: int,
    timeout: float,
    profile: str,
    degree: int = 8,
) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    if Path(batch_name).name != batch_name:
        raise ValueError("batch name must be local")
    if conflicts <= 0 or timeout <= 0:
        raise ValueError("limits must be positive")
    if not solver.is_file():
        raise FileNotFoundError(solver)
    verified = snapshot.verify(output, degree)
    directory = output / two.DIRECTORY_TEMPLATE.format(degree=degree)
    manifest_path = directory / snapshot.PARTIAL_MANIFEST
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    batch = directory / batch_name
    if batch.exists():
        raise FileExistsError(f"refusing existing batch directory: {batch}")
    batch.mkdir()
    temporary = batch / "tmp"
    temporary.mkdir()
    solver_hash = sha256(solver)
    version = subprocess.run(
        [str(solver), "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()
    results = []
    before = time.perf_counter()
    for row in manifest["cases"]:
        result = pilots.run_case(
            directory,
            batch,
            temporary,
            solver,
            solver_hash,
            row,
            conflicts,
            timeout,
            profile,
        )
        results.append(result)
        case = result["case"]
        print(
            f"partial d={case['degree']} p={case['p']} q={case['q']} "
            f"{result['status']} elapsed={result['elapsed_seconds']:.3f}s",
            flush=True,
        )
    summary = {
        "schema_version": 1,
        "status": "PARTIAL_PROOF_FREE_BATCH_COMPLETE",
        "warning": "Only completed snapshot cases were run; this is not a complete case cover and no LRAT was emitted.",
        "degree": degree,
        "completed_cases": manifest["completed_case_order"],
        "missing_cases": manifest["missing_case_order"],
        "partial_manifest": {"path": str(manifest_path), "sha256": sha256(manifest_path)},
        "pre_run_verification": verified,
        "solver": {"path": str(solver), "sha256": solver_hash, "version": version},
        "profile": profile,
        "conflict_limit": conflicts,
        "timeout_seconds_per_case": timeout,
        "temporary_directory": str(temporary),
        "total_elapsed_seconds": time.perf_counter() - before,
        "results": results,
        "certified": False,
        "proof_emitted": False,
    }
    pilots.write_new_json(batch / "batch_manifest.json", summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--batch-name", required=True)
    parser.add_argument("--degree", type=int, choices=two.DEGREES, default=8)
    parser.add_argument("--conflicts", type=int, default=100_000)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--profile", choices=("unsat", "plain", "default"), default="unsat")
    args = parser.parse_args()
    result = run(
        args.output,
        args.solver,
        args.batch_name,
        args.conflicts,
        args.timeout,
        args.profile,
        args.degree,
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
