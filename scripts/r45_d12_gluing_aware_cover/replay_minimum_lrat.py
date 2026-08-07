#!/usr/bin/env python3
"""Replay the no-order7-cover4 LRAT with an exact theorem identity."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

from scripts.r45_d12_structural_cover import structural_cover


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
NAMESPACE = "LRATCatcher.Tests.R45OrderSevenCoverMinimumReplay"
THEOREM = "no_order7_cover_of_size_four"
QUALIFIED_THEOREM = f"{NAMESPACE}.{THEOREM}"
EXPECTED_CNF_SHA256 = "84E1BE500A85AD2B6F63F780063116F4AF0DE3239C63710AFF8816057AC6EF82"
EXPECTED_LRAT_SHA256 = "4FD1F02297F5019B9EADBE9BC20E29DF326B0B7F99B8A539C140FD9911F15793"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def write_new(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(payload)


def lean_source(cnf: Path, lrat: Path) -> bytes:
    cnf_path = str(cnf).replace("\\", "/")
    lrat_path = str(lrat).replace("\\", "/")
    return (
        "import LRATCatcher.ReflectTrim\n\n"
        f"namespace {NAMESPACE}\n\n"
        f"lrat_reflect_trim {THEOREM}\n"
        f"  \"{cnf_path}\"\n"
        f"  \"{lrat_path}\"\n\n"
        f"#print axioms {THEOREM}\n\n"
        f"end {NAMESPACE}\n"
    ).encode("utf-8")


def replay(cnf: Path, lrat: Path, lake: Path, output: Path, timeout: float) -> dict[str, object]:
    for path in (cnf, lrat, output):
        structural_cover.ensure_ssd(path)
    if timeout <= 0:
        raise ValueError("timeout must be positive")
    if sha256(cnf) != EXPECTED_CNF_SHA256:
        raise ValueError("no-cover4 CNF SHA-256 mismatch")
    if sha256(lrat) != EXPECTED_LRAT_SHA256:
        raise ValueError("no-cover4 LRAT SHA-256 mismatch")
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "replay.json"
    lean_path = output / "ReplayOrderSevenMinimum.lean"
    log_path = output / "replay.log"
    if any(path.exists() for path in (report_path, lean_path, log_path)):
        raise FileExistsError(f"refusing to overwrite replay artifacts in {output}")
    source = lean_source(cnf, lrat)
    legacy_label = "d12_type0_core24"
    if legacy_label.encode("ascii") in source:
        raise AssertionError("legacy conditioned-core theorem label leaked into replay")
    write_new(lean_path, source)
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
    wall_seconds = time.perf_counter() - started
    write_new(log_path, log_text.encode("utf-8"))
    succeeded = returncode == 0 and not timed_out
    if succeeded and QUALIFIED_THEOREM not in log_text:
        raise RuntimeError("Lean replay log does not identify the expected theorem")
    if legacy_label in log_text:
        raise RuntimeError("Lean replay log contains the legacy theorem label")
    report = {
        "schema_version": 1,
        "status": "LEAN_LRAT_REPLAY_SUCCEEDED" if succeeded else "LEAN_LRAT_REPLAY_FAILED",
        "claim": "the 25-graph hitting-set CNF has no solution selecting at most four order-seven motifs",
        "theorem": QUALIFIED_THEOREM,
        "cnf": {"path": str(cnf), "sha256": sha256(cnf), "bytes": cnf.stat().st_size},
        "lrat": {"path": str(lrat), "sha256": sha256(lrat), "bytes": lrat.stat().st_size},
        "lean_source": {"path": str(lean_path), "sha256": sha256(lean_path)},
        "log": {"path": str(log_path), "sha256": sha256(log_path)},
        "returncode": returncode,
        "timed_out": timed_out,
        "wall_seconds": round(wall_seconds, 3),
        "legacy_label_absent": True,
    }
    write_new(report_path, (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8"))
    if not succeeded:
        raise RuntimeError(f"Lean LRAT replay failed; see {log_path}")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--lrat", type=Path, required=True)
    parser.add_argument("--lake", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    args = parser.parse_args()
    print(json.dumps(replay(args.cnf, args.lrat, args.lake, args.output, args.timeout), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
