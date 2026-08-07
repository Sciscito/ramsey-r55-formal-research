#!/usr/bin/env python3
"""Generate and Lean-replay one LRAT for each remaining two-centre case."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

from . import generate_two_center_branches as two
from . import generate_universal as universal
from .run_solver_pilot import sha256
from .run_two_center_pilots import parse_metrics


CASE_ORDER = (
    (1, 3),
    (0, 3),
    (0, 2),
    (1, 2),
    (1, 1),
    (3, 0),
    (3, 2),
    (2, 1),
    (3, 1),
    (3, 3),
    (2, 2),
    (2, 3),
)
SOLVER_FLAGS = (
    "--lrat",
    "--no-binary",
    "--checkproof=2",
    "--unsat",
    "--walk=false",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPOSITORY = Path(__file__).resolve().parents[2]


class TotalBudgetExceeded(RuntimeError):
    pass


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    os.replace(temporary, path)


def theorem_identity(p: int, q: int) -> tuple[str, str, str]:
    namespace = f"LRATCatcher.Tests.R45D12Cover9UniversalP{p}Q{q}Replay"
    theorem = f"cover9_d8_two_center_p{p}_q{q}_unsat"
    return namespace, theorem, f"{namespace}.{theorem}"


def parse_case_specification(value: str) -> tuple[int, int]:
    fields = value.split(",")
    if len(fields) != 2:
        raise argparse.ArgumentTypeError("case must have spelling p,q")
    try:
        case = (int(fields[0]), int(fields[1]))
    except ValueError as error:
        raise argparse.ArgumentTypeError("case coordinates must be integers") from error
    if case not in two.CASES:
        raise argparse.ArgumentTypeError(f"case is not a two-centre branch: {case}")
    return case


def lean_source(cnf: Path, lrat: Path, p: int, q: int) -> bytes:
    namespace, theorem, _ = theorem_identity(p, q)
    cnf_text = str(cnf).replace("\\", "/")
    lrat_text = str(lrat).replace("\\", "/")
    return (
        "import LRATCatcher.ReflectTrim\n\n"
        f"namespace {namespace}\n\n"
        f"lrat_reflect_trim {theorem}\n"
        f"  \"{cnf_text}\"\n"
        f"  \"{lrat_text}\"\n\n"
        f"#print axioms {theorem}\n\n"
        f"end {namespace}\n"
    ).encode("utf-8")


def parse_axioms(log_text: str) -> list[str]:
    match = re.search(r"depends on axioms: \[(.*?)\]", log_text, re.DOTALL)
    if not match:
        raise ValueError("Lean log has no #print axioms result")
    return [item.strip() for item in match.group(1).split(",") if item.strip()]


def axioms_allowed(axioms: list[str], p: int, q: int) -> bool:
    _, theorem, _ = theorem_identity(p, q)
    native_pattern = re.compile(
        rf"{re.escape(theorem)}\._native\.native_decide\.ax_[0-9]+_[0-9]+"
    )
    return all(
        axiom in ALLOWED_AXIOMS or native_pattern.fullmatch(axiom) is not None
        for axiom in axioms
    )


def monitor_solver(
    command: list[str],
    log_path: Path,
    proof_partial: Path,
    timeout: float,
    proof_limit: int,
    completed_proof_bytes: int,
    total_limit: int,
) -> tuple[int | None, float, str | None]:
    before = time.perf_counter()
    reason: str | None = None
    with log_path.open("xb") as log_stream:
        process = subprocess.Popen(
            command,
            stdout=log_stream,
            stderr=subprocess.STDOUT,
        )
        while process.poll() is None:
            time.sleep(0.1)
            partial_bytes = proof_partial.stat().st_size if proof_partial.exists() else 0
            if partial_bytes >= proof_limit:
                reason = "PROOF_SIZE_LIMIT"
                process.kill()
                break
            if completed_proof_bytes + partial_bytes >= total_limit:
                reason = "TOTAL_PROOF_BUDGET"
                process.kill()
                break
            if time.perf_counter() - before >= timeout:
                reason = "SOLVER_TIMEOUT"
                process.kill()
                break
        process.wait()
        returncode = process.returncode
    return returncode, time.perf_counter() - before, reason


def replay_lean(
    cnf: Path,
    proof: Path,
    case_dir: Path,
    p: int,
    q: int,
    lake: Path,
    timeout: float,
    environment: dict[str, str],
) -> dict[str, object]:
    lean_path = case_dir / "Replay.lean"
    log_path = case_dir / "lean_replay.log"
    lean_path.write_bytes(lean_source(cnf, proof, p, q))
    before = time.perf_counter()
    try:
        completed = subprocess.run(
            [str(lake), "env", "lean", str(lean_path)],
            cwd=REPOSITORY / "vendor" / "lrat-catcher",
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            check=False,
            env=environment,
        )
        returncode: int | None = completed.returncode
        log_text = completed.stdout
        timed_out = False
    except subprocess.TimeoutExpired as error:
        raw = error.stdout or ""
        log_text = raw if isinstance(raw, str) else raw.decode("utf-8", "replace")
        returncode = None
        timed_out = True
    elapsed = time.perf_counter() - before
    log_path.write_text(log_text, encoding="utf-8", newline="\n")
    _, _, qualified = theorem_identity(p, q)
    trim = re.search(
        r"trimmed (\d+) to (\d+) actions; (\d+) to (\d+) UTF-8 bytes",
        log_text,
    )
    try:
        axioms = parse_axioms(log_text)
    except ValueError:
        axioms = []
    succeeded = (
        returncode == 0
        and not timed_out
        and qualified in log_text
        and trim is not None
        and "sorryAx" not in log_text
        and bool(axioms)
        and axioms_allowed(axioms, p, q)
    )
    return {
        "status": "LEAN_LRAT_REPLAY_SUCCEEDED" if succeeded else "LEAN_LRAT_REPLAY_FAILED",
        "theorem": qualified,
        "returncode": returncode,
        "timed_out": timed_out,
        "wall_seconds": round(elapsed, 3),
        "axioms": axioms,
        "axioms_allowed": bool(axioms) and axioms_allowed(axioms, p, q),
        "trim": None
        if trim is None
        else {
            "original_actions": int(trim.group(1)),
            "trimmed_actions": int(trim.group(2)),
            "original_utf8_bytes": int(trim.group(3)),
            "trimmed_utf8_bytes": int(trim.group(4)),
        },
        "lean_source": {
            "name": lean_path.name,
            "bytes": lean_path.stat().st_size,
            "sha256": sha256(lean_path),
        },
        "log": {
            "name": log_path.name,
            "bytes": log_path.stat().st_size,
            "sha256": sha256(log_path),
        },
    }


def certify_case(
    row: dict[str, object],
    directory: Path,
    batch: Path,
    solver: Path,
    solver_hash: str,
    lake: Path,
    lake_hash: str,
    conflicts: int,
    solver_timeout: float,
    replay_timeout: float,
    proof_limit: int,
    completed_proof_bytes: int,
    total_limit: int,
    environment: dict[str, str],
) -> dict[str, object]:
    p, q = int(row["p"]), int(row["q"])
    metadata = row["formula"]
    if not isinstance(metadata, dict):
        raise ValueError("malformed formula metadata")
    cnf = directory / str(metadata["name"])
    case_dir = batch / f"p{p}_q{q}"
    case_dir.mkdir()
    proof = case_dir / f"cover9_d8_two_center_p{p}_q{q}.lrat"
    partial = proof.with_suffix(".lrat.partial")
    solver_log = case_dir / "cadical.log"
    command = [
        str(solver),
        *SOLVER_FLAGS,
        "-c",
        str(conflicts),
        str(cnf),
        str(partial),
    ]
    returncode, elapsed, stop_reason = monitor_solver(
        command,
        solver_log,
        partial,
        solver_timeout,
        proof_limit,
        completed_proof_bytes,
        total_limit,
    )
    log_text = solver_log.read_text(encoding="utf-8", errors="replace")
    partial_bytes = partial.stat().st_size if partial.exists() else 0
    if stop_reason is None and partial_bytes >= proof_limit:
        stop_reason = "PROOF_SIZE_LIMIT"
    if stop_reason is None and completed_proof_bytes + partial_bytes >= total_limit:
        stop_reason = "TOTAL_PROOF_BUDGET"
    solver_ok = (
        stop_reason is None
        and returncode == 20
        and "s UNSATISFIABLE" in log_text
        and "--checkproof=2" in log_text
        and partial.is_file()
        and partial.stat().st_size > 0
    )
    record: dict[str, object] = {
        "schema_version": 1,
        "case": {"p": p, "q": q},
        "formula": metadata,
        "solver": {
            "path": str(solver),
            "sha256": solver_hash,
            "flags": list(SOLVER_FLAGS),
            "conflict_limit": conflicts,
            "timeout_seconds": solver_timeout,
            "proof_byte_limit": proof_limit,
            "returncode": returncode,
            "stop_reason": stop_reason,
            "elapsed_seconds": round(elapsed, 6),
            "metrics": parse_metrics(log_text),
            "log": {
                "name": solver_log.name,
                "bytes": solver_log.stat().st_size,
                "sha256": sha256(solver_log),
            },
        },
        "lake": {"path": str(lake), "sha256": lake_hash},
    }
    if not solver_ok:
        record["status"] = "LRAT_GENERATION_FAILED"
        if partial.exists():
            partial.unlink()
        record["lrat"] = None
        atomic_json(case_dir / "certificate.json", record)
        if stop_reason == "TOTAL_PROOF_BUDGET":
            raise TotalBudgetExceeded(f"aggregate proof budget reached in p={p},q={q}")
        return record
    os.replace(partial, proof)
    record["lrat"] = {
        "name": proof.name,
        "bytes": proof.stat().st_size,
        "sha256": sha256(proof),
    }
    replay = replay_lean(
        cnf,
        proof,
        case_dir,
        p,
        q,
        lake,
        replay_timeout,
        environment,
    )
    record["replay"] = replay
    record["status"] = replay["status"]
    atomic_json(case_dir / "certificate.json", record)
    return record


def run(
    output: Path,
    solver: Path,
    lake: Path,
    batch_name: str,
    conflicts: int,
    solver_timeout: float,
    replay_timeout: float,
    proof_limit: int,
    total_limit: int,
    selected_order: tuple[tuple[int, int], ...] = CASE_ORDER,
) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    if Path(batch_name).name != batch_name:
        raise ValueError("batch name must be local")
    if min(conflicts, solver_timeout, replay_timeout, proof_limit, total_limit) <= 0:
        raise ValueError("limits must be positive")
    if not solver.is_file() or not lake.is_file():
        raise FileNotFoundError("solver or lake executable missing")
    two.verify(output)
    directory = output / two.OUTPUT_DIRECTORY
    source_manifest_path = directory / two.SUMMARY_NAME
    source = json.loads(source_manifest_path.read_text(encoding="utf-8"))
    rows = {(int(row["p"]), int(row["q"])): row for row in source["cases"]}
    if set(CASE_ORDER) != set(two.CASES) - {(2, 0)}:
        raise ValueError("certification order does not cover the 12 remaining cases")
    if not selected_order or len(set(selected_order)) != len(selected_order):
        raise ValueError("selected cases must be nonempty and unique")
    if not set(selected_order) <= set(two.CASES):
        raise ValueError("selected cases contain an unsupported branch")
    batch = directory / batch_name
    if batch.exists():
        raise FileExistsError(f"refusing existing certification batch: {batch}")
    batch.mkdir()
    temporary = batch / "tmp"
    temporary.mkdir()
    environment = os.environ.copy()
    environment["TEMP"] = str(temporary)
    environment["TMP"] = str(temporary)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    solver_hash, lake_hash = sha256(solver), sha256(lake)
    results: list[dict[str, object]] = []
    completed_bytes = 0
    before = time.perf_counter()
    unattempted: list[list[int]] = []
    for index, case in enumerate(selected_order, 1):
        try:
            record = certify_case(
                rows[case],
                directory,
                batch,
                solver,
                solver_hash,
                lake,
                lake_hash,
                conflicts,
                solver_timeout,
                replay_timeout,
                proof_limit,
                completed_bytes,
                total_limit,
                environment,
            )
        except TotalBudgetExceeded as error:
            unattempted = [list(item) for item in selected_order[index:]]
            print(f"TOTAL_BUDGET_STOP {error}", flush=True)
            break
        results.append(record)
        lrat = record.get("lrat")
        if isinstance(lrat, dict):
            completed_bytes += int(lrat["bytes"])
        replay = record.get("replay")
        trim = replay.get("trim") if isinstance(replay, dict) else None
        print(
            f"CERT {index}/{len(selected_order)} p={case[0]} q={case[1]} "
            f"status={record['status']} proof_bytes="
            f"{lrat['bytes'] if isinstance(lrat, dict) else 0} "
            f"trimmed_actions={trim['trimmed_actions'] if isinstance(trim, dict) else None}",
            flush=True,
        )
        if len(selected_order) > 1 and index == 5:
            print("CHECKPOINT_FIVE_EASIEST_COMPLETE", flush=True)
        if isinstance(lrat, dict) and int(lrat["bytes"]) > 100 * 1024 * 1024:
            print(f"LARGE_PROOF p={case[0]} q={case[1]} bytes={lrat['bytes']}", flush=True)
        summary = {
            "schema_version": 1,
            "status": "CERTIFICATION_BATCH_IN_PROGRESS",
            "case_order": [list(item) for item in selected_order],
            "results": results,
            "completed_lrat_bytes": completed_bytes,
            "total_proof_byte_limit": total_limit,
        }
        atomic_json(batch / "batch_manifest.json", summary)
    success_count = sum(
        record.get("status") == "LEAN_LRAT_REPLAY_SUCCEEDED" for record in results
    )
    final = {
        "schema_version": 1,
        "status": (
            "ALL_SELECTED_CASES_LEAN_LRAT_CERTIFIED"
            if success_count == len(selected_order)
            else "PARTIAL_CERTIFICATION_BATCH"
        ),
        "case_order": [list(item) for item in selected_order],
        "source_manifest": {
            "sha256": sha256(source_manifest_path),
            "path": str(source_manifest_path),
        },
        "solver": {"path": str(solver), "sha256": solver_hash},
        "lake": {"path": str(lake), "sha256": lake_hash},
        "limits": {
            "conflicts": conflicts,
            "solver_timeout_seconds": solver_timeout,
            "replay_timeout_seconds": replay_timeout,
            "proof_bytes_per_case": proof_limit,
            "proof_bytes_total": total_limit,
        },
        "completed_cases": len(results),
        "certified_cases": success_count,
        "completed_lrat_bytes": completed_bytes,
        "unattempted_cases": unattempted,
        "elapsed_seconds": round(time.perf_counter() - before, 3),
        "results": results,
    }
    atomic_json(batch / "batch_manifest.json", final)
    return final


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--batch-name", required=True)
    parser.add_argument("--conflicts", type=int, default=100_000)
    parser.add_argument("--solver-timeout", type=float, default=300)
    parser.add_argument("--replay-timeout", type=float, default=600)
    parser.add_argument("--proof-limit", type=int, default=1024**3)
    parser.add_argument("--total-limit", type=int, default=20 * 1024**3)
    parser.add_argument("--only-case", action="append", type=parse_case_specification)
    args = parser.parse_args()
    result = run(
        args.output,
        args.solver,
        args.lake,
        args.batch_name,
        args.conflicts,
        args.solver_timeout,
        args.replay_timeout,
        args.proof_limit,
        args.total_limit,
        tuple(args.only_case) if args.only_case else CASE_ORDER,
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
