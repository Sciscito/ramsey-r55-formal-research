#!/usr/bin/env python3
"""Replay the frozen universal-cover p=2,q=0 LRAT in Lean."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

from . import generate_universal as universal


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
NAMESPACE = "LRATCatcher.Tests.R45D12Cover9UniversalP2Q0Replay"
THEOREM = "cover9_d8_two_center_p2_q0_unsat"
QUALIFIED_THEOREM = f"{NAMESPACE}.{THEOREM}"
EXPECTED_CNF_SHA256 = "D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315"
EXPECTED_CNF_BYTES = 44_764_698
EXPECTED_CNF_LINES = 758_925
EXPECTED_LRAT_SHA256 = "4C65A4480E9BDD8B0F526DE496A774795905C23DD1067D1B4574D267388403C5"
EXPECTED_LRAT_BYTES = 10_683_195


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def write_new(path: Path, payload: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(payload)


def verify_inputs(cnf: Path, lrat: Path) -> dict[str, object]:
    cnf = universal.ensure_ssd(cnf)
    lrat = universal.ensure_ssd(lrat)
    cnf_hash, cnf_bytes, cnf_lines = universal.sha256_file(cnf, count_lines=True)
    if (cnf_hash, cnf_bytes, cnf_lines) != (
        EXPECTED_CNF_SHA256,
        EXPECTED_CNF_BYTES,
        EXPECTED_CNF_LINES,
    ):
        raise ValueError("frozen p=2,q=0 CNF identity mismatch")
    if (sha256(lrat), lrat.stat().st_size) != (
        EXPECTED_LRAT_SHA256,
        EXPECTED_LRAT_BYTES,
    ):
        raise ValueError("frozen p=2,q=0 LRAT identity mismatch")
    with cnf.open("rt", encoding="ascii") as stream:
        if stream.readline().rstrip() != "p cnf 66 758924":
            raise ValueError("unexpected p=2,q=0 DIMACS header")
    with lrat.open("rb") as stream:
        stream.seek(max(0, lrat.stat().st_size - 4096))
        lines = [line for line in stream.read().splitlines() if line.strip()]
    final = lines[-1].split()
    if len(final) < 4 or final[1] != b"0" or final[-1] != b"0":
        raise ValueError("LRAT does not end in an empty-clause addition")
    return {
        "cnf": {"bytes": cnf_bytes, "lines": cnf_lines, "sha256": cnf_hash},
        "lrat": {
            "bytes": lrat.stat().st_size,
            "sha256": EXPECTED_LRAT_SHA256,
            "final_clause_id": int(final[0]),
        },
    }


def lean_source(cnf: Path, lrat: Path) -> bytes:
    cnf_text = str(cnf).replace("\\", "/")
    lrat_text = str(lrat).replace("\\", "/")
    return (
        "import LRATCatcher.ReflectTrim\n\n"
        f"namespace {NAMESPACE}\n\n"
        f"lrat_reflect_trim {THEOREM}\n"
        f"  \"{cnf_text}\"\n"
        f"  \"{lrat_text}\"\n\n"
        f"#print axioms {THEOREM}\n\n"
        f"end {NAMESPACE}\n"
    ).encode("utf-8")


def replay(cnf: Path, lrat: Path, lake: Path, output: Path, timeout: float) -> dict[str, object]:
    inputs = verify_inputs(cnf, lrat)
    output = universal.ensure_ssd(output)
    if timeout <= 0:
        raise ValueError("timeout must be positive")
    if output.exists():
        raise FileExistsError(f"refusing existing replay directory: {output}")
    if not lake.is_file():
        raise FileNotFoundError(lake)
    output.mkdir(parents=True)
    lean_path = output / "ReplayP2Q0.lean"
    log_path = output / "replay.log"
    report_path = output / "replay.json"
    write_new(lean_path, lean_source(cnf, lrat))
    started = time.perf_counter()
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
        )
        returncode: int | None = completed.returncode
        log_text = completed.stdout
        timed_out = False
    except subprocess.TimeoutExpired as error:
        raw = error.stdout or ""
        log_text = raw if isinstance(raw, str) else raw.decode("utf-8", "replace")
        returncode = None
        timed_out = True
    elapsed = time.perf_counter() - started
    write_new(log_path, log_text.encode("utf-8"))
    succeeded = (
        returncode == 0
        and not timed_out
        and QUALIFIED_THEOREM in log_text
        and "lrat_reflect_trim: trimmed" in log_text
    )
    report = {
        "schema_version": 1,
        "status": "LEAN_LRAT_REPLAY_SUCCEEDED" if succeeded else "LEAN_LRAT_REPLAY_FAILED",
        "claim": "the exact universal-cover degree-eight two-centre p=2,q=0 CNF is unsatisfiable",
        "theorem": QUALIFIED_THEOREM,
        "inputs": inputs,
        "paths": {"cnf": str(cnf), "lrat": str(lrat)},
        "lean_source": {"path": str(lean_path), "sha256": sha256(lean_path)},
        "log": {"path": str(log_path), "sha256": sha256(log_path)},
        "returncode": returncode,
        "timed_out": timed_out,
        "wall_seconds": round(elapsed, 3),
    }
    write_new(report_path, (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8"))
    if not succeeded:
        raise RuntimeError(f"Lean LRAT replay failed; see {log_path}")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", required=True, type=Path)
    parser.add_argument("--lrat", required=True, type=Path)
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", required=True, type=float)
    args = parser.parse_args()
    print(json.dumps(replay(args.cnf, args.lrat, args.lake, args.output, args.timeout), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
