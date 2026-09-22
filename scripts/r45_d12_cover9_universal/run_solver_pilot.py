#!/usr/bin/env python3
"""Run bounded, proof-free CaDiCaL pilots on an SSD-resident target."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import Sequence

from . import generate_universal as universal


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def classify(returncode: int, log_text: str) -> str:
    unsat = "s UNSATISFIABLE" in log_text
    sat = "s SATISFIABLE" in log_text and not unsat
    if returncode == 20 and unsat:
        return "UNSAT_WITHOUT_PROOF"
    if returncode == 10 and sat:
        return "SAT"
    if returncode == 0 and not unsat and not sat:
        return "UNKNOWN_LIMIT"
    raise RuntimeError(f"inconsistent CaDiCaL exit/log status: exit={returncode}")


def profile_flags(profile: str) -> tuple[str, ...]:
    if profile == "default":
        return ()
    if profile not in ("unsat", "plain"):
        raise ValueError(f"unsupported solver profile: {profile}")
    return (f"--{profile}",)


def load_formula(output: Path, manifest_name: str) -> tuple[Path, dict[str, object]]:
    manifest_path = output / manifest_name
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    metadata = manifest["files"]["formula"]
    formula = output / metadata["name"]
    if not formula.is_file():
        raise FileNotFoundError(formula)
    actual_hash = sha256(formula)
    actual_size = formula.stat().st_size
    if actual_hash != metadata["sha256"] or actual_size != metadata["bytes"]:
        raise ValueError("formula hash or size differs from manifest")
    expected_header = f"p cnf {metadata['variables']} {metadata['clauses']}"
    with formula.open("rt", encoding="ascii") as stream:
        if stream.readline().rstrip("\r\n") != expected_header:
            raise ValueError("formula DIMACS header differs from manifest")
    return formula, metadata


def run(
    output: Path,
    solver: Path,
    conflicts: int,
    timeout_seconds: float,
    *,
    manifest_name: str = "manifest.json",
    profile: str = "unsat",
    extra_flags: Sequence[str] = (),
) -> dict[str, object]:
    if conflicts <= 0:
        raise ValueError("conflict limit must be positive")
    if timeout_seconds <= 0:
        raise ValueError("timeout must be positive")
    output = universal.ensure_ssd(output)
    if Path(manifest_name).name != manifest_name:
        raise ValueError("manifest must be a local filename")
    if not solver.is_file():
        raise FileNotFoundError(solver)
    formula, formula_metadata = load_formula(output, manifest_name)
    flags = profile_flags(profile) + tuple(extra_flags)
    flag_tag = hashlib.sha256("\0".join(flags).encode("utf-8")).hexdigest()[:8]
    stem = f"pilot_{formula.stem}_{profile}_{flag_tag}_c{conflicts}_t{timeout_seconds:g}"
    log_path = output / f"{stem}.log"
    result_path = output / f"{stem}.json"
    for path in (log_path, result_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace pilot artifact: {path}")

    version_run = subprocess.run(
        [str(solver), "--version"], capture_output=True, text=True, check=True
    )
    command = [str(solver), *flags, "-c", str(conflicts), str(formula)]
    started = dt.datetime.now(dt.timezone.utc)
    before = time.perf_counter()
    returncode: int | None = None
    timed_out = False
    with log_path.open("xb") as log_stream:
        try:
            completed = subprocess.run(
                command,
                stdout=log_stream,
                stderr=subprocess.STDOUT,
                timeout=timeout_seconds,
            )
            returncode = completed.returncode
        except subprocess.TimeoutExpired:
            # subprocess.run has already killed and waited for the child.
            timed_out = True
    elapsed = time.perf_counter() - before
    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    status = "TIMEOUT" if timed_out else classify(returncode, log_text)  # type: ignore[arg-type]
    result = {
        "schema_version": 1,
        "status": status,
        "certified": False,
        "warning": (
            "This run deliberately emitted no proof. Even UNSAT_WITHOUT_PROOF "
            "is only a performance signal until the exact CNF has an LRAT "
            "trace and independent replay."
        ),
        "started_utc": started.isoformat(),
        "elapsed_seconds": elapsed,
        "timeout_seconds": timeout_seconds,
        "conflict_limit": conflicts,
        "returncode": returncode,
        "command": [solver.name, *flags, "-c", str(conflicts), formula.name],
        "solver": {
            "path": str(solver),
            "version": version_run.stdout.strip(),
            "sha256": sha256(solver),
        },
        "formula": {
            "path": str(formula),
            "manifest": manifest_name,
            "bytes": formula_metadata["bytes"],
            "sha256": formula_metadata["sha256"],
            "clauses": formula_metadata["clauses"],
            "variables": formula_metadata["variables"],
        },
        "log": {
            "path": str(log_path),
            "bytes": log_path.stat().st_size,
            "sha256": sha256(log_path),
        },
    }
    result_path.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--conflicts", required=True, type=int)
    parser.add_argument("--timeout", required=True, type=float)
    parser.add_argument("--manifest", default="manifest.json")
    parser.add_argument("--profile", choices=("unsat", "plain", "default"), default="unsat")
    parser.add_argument(
        "--solver-flag",
        action="append",
        default=[],
        help="extra CaDiCaL flag; use --solver-flag=--name=value",
    )
    args = parser.parse_args()
    print(
        json.dumps(
            run(
                args.output,
                args.solver,
                args.conflicts,
                args.timeout,
                manifest_name=args.manifest,
                profile=args.profile,
                extra_flags=args.solver_flag,
            ),
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
