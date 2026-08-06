#!/usr/bin/env python3
"""Reproducible, resumable CaDiCaL pilot runner for the typed R(5,5) cases.

The runner deliberately defaults to a small pilot.  It generates each selected
CNF through ``ramsey.py``, records the exact generator and solver commands, and
appends one ``start`` and one ``result`` object to a JSONL journal.  A completed
run is identified by the hashes of all material inputs and by its options, so a
later invocation can skip it safely.

CaDiCaL's conventional exit codes are interpreted conservatively: 10 is SAT,
20 is UNSAT, and 0 is UNKNOWN.  In particular, reaching the conflict limit is
never reported as UNSAT.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import ctypes
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import time
from typing import Any, Iterable, Sequence


HERE = Path(__file__).resolve().parent
SCHEMA_VERSION = 1
DEFAULT_SAMPLE_SIZE = 8
DEFAULT_MEMORY_PER_JOB_MB = 600
COMPLETED_STATUSES = {"SAT", "UNSAT", "UNKNOWN", "TIMEOUT", "MEMORY_LIMIT"}

STATUS_RE = re.compile(r"^s\s+(SATISFIABLE|UNSATISFIABLE|UNKNOWN)\s*$", re.MULTILINE)
CONFLICT_RE = re.compile(r"^c\s+conflicts:\s*([0-9]+)\b", re.MULTILINE)
RSS_RE = re.compile(
    r"^c\s+maximum resident set size of process:\s*([0-9]+(?:\.[0-9]+)?)\s+MB\s*$",
    re.MULTILINE,
)
REAL_TIME_RE = re.compile(
    r"^c\s+total real time since initialization:\s*([0-9]+(?:\.[0-9]+)?)\s+seconds\s*$",
    re.MULTILINE,
)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="milliseconds")


def sha256_file(path: Path, chunk_size: int = 1024 * 1024) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(chunk_size):
            digest.update(chunk)
    return digest.hexdigest()


def stable_hash(seed: str, branch_id: str) -> str:
    return hashlib.sha256(f"{seed}\0{branch_id}".encode("utf-8")).hexdigest()


def deterministic_sample(
    branches: Sequence[dict[str, Any]],
    sample_size: int,
    seed: str,
    stratified: bool = True,
) -> list[dict[str, Any]]:
    """Select a stable sample, independent of manifest branch ordering.

    Stratification round-robins over ``(degree, codegree)`` groups.  Within a
    group, SHA-256 ranks branch IDs using the supplied seed.
    """

    if sample_size < 1:
        raise ValueError("sample size must be positive")
    if sample_size >= len(branches):
        return sorted(branches, key=lambda branch: str(branch["id"]))

    rank = lambda branch: (stable_hash(seed, str(branch["id"])), str(branch["id"]))
    if not stratified:
        return sorted(sorted(branches, key=rank)[:sample_size], key=lambda branch: str(branch["id"]))

    groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for branch in branches:
        key = (int(branch["degree"]), int(branch["codegree"]))
        groups.setdefault(key, []).append(branch)
    for group in groups.values():
        group.sort(key=rank)

    selected: list[dict[str, Any]] = []
    # Interleave degrees even when the requested sample is smaller than the
    # number of strata.  Hash-ranking codegrees avoids always favouring the
    # smallest c values while remaining exactly reproducible.
    keys_by_degree: dict[int, list[tuple[int, int]]] = {}
    for key in groups:
        keys_by_degree.setdefault(key[0], []).append(key)
    for degree, keys in keys_by_degree.items():
        keys.sort(key=lambda key: (stable_hash(seed, f"stratum:{degree}:{key[1]}"), key))
    group_keys: list[tuple[int, int]] = []
    stratum_offset = 0
    while True:
        added_key = False
        for degree in sorted(keys_by_degree):
            keys = keys_by_degree[degree]
            if stratum_offset < len(keys):
                group_keys.append(keys[stratum_offset])
                added_key = True
        if not added_key:
            break
        stratum_offset += 1
    offset = 0
    while len(selected) < sample_size:
        added = False
        for key in group_keys:
            group = groups[key]
            if offset < len(group):
                selected.append(group[offset])
                added = True
                if len(selected) == sample_size:
                    break
        if not added:  # Defensive: sample_size was already bounded above.
            break
        offset += 1
    return sorted(selected, key=lambda branch: str(branch["id"]))


def parse_solver_output(text: str) -> dict[str, Any]:
    statuses = STATUS_RE.findall(text)
    parsed_status: str | None = None
    if statuses:
        unique = set(statuses)
        if len(unique) == 1:
            parsed_status = {
                "SATISFIABLE": "SAT",
                "UNSATISFIABLE": "UNSAT",
                "UNKNOWN": "UNKNOWN",
            }[statuses[-1]]
        else:
            parsed_status = "CONFLICTING_OUTPUT"

    conflicts = CONFLICT_RE.findall(text)
    rss = RSS_RE.findall(text)
    real_times = REAL_TIME_RE.findall(text)
    return {
        "reported_status": parsed_status,
        "conflicts": int(conflicts[-1]) if conflicts else None,
        "reported_max_rss_mb": float(rss[-1]) if rss else None,
        "solver_real_seconds": float(real_times[-1]) if real_times else None,
    }


def decode_solver_bytes(data: bytes) -> str:
    """Decode direct solver output and PowerShell-created UTF-16 logs."""

    if data.startswith((b"\xff\xfe", b"\xfe\xff")):
        return data.decode("utf-16", errors="replace")
    if data.startswith(b"\xef\xbb\xbf"):
        return data.decode("utf-8-sig", errors="replace")
    return data.decode("utf-8", errors="replace")


def classify_solver_result(
    return_code: int | None,
    reported_status: str | None,
    *,
    timed_out: bool = False,
    memory_limited: bool = False,
) -> tuple[str, str]:
    """Return ``(status, reason)`` without ever promoting UNKNOWN to UNSAT."""

    if memory_limited:
        return "MEMORY_LIMIT", "runner_rss_limit"
    if timed_out:
        return "TIMEOUT", "runner_wall_timeout"
    if reported_status == "CONFLICTING_OUTPUT":
        return "ERROR", "conflicting_status_lines"

    by_exit = {10: "SAT", 20: "UNSAT", 0: "UNKNOWN"}.get(return_code)
    if by_exit is None:
        return "ERROR", f"unexpected_exit_code_{return_code}"
    if reported_status is not None and reported_status != by_exit:
        return "ERROR", f"status_exit_mismatch_{reported_status}_{return_code}"
    return by_exit, "cadical_exit_code"


def effective_job_count(jobs: int, max_memory_mb: int | None, memory_per_job_mb: int) -> int:
    if jobs < 1:
        raise ValueError("jobs must be positive")
    if memory_per_job_mb < 1:
        raise ValueError("memory per job must be positive")
    if max_memory_mb is None:
        return jobs
    if max_memory_mb < memory_per_job_mb:
        raise ValueError("max memory is smaller than the reservation for one job")
    return min(jobs, max_memory_mb // memory_per_job_mb)


class Journal:
    def __init__(self, path: Path):
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.Lock()

    def append(self, record: dict[str, Any]) -> None:
        encoded = json.dumps(record, sort_keys=True, separators=(",", ":"))
        with self._lock, self.path.open("a", encoding="utf-8", newline="\n") as output:
            output.write(encoded + "\n")
            output.flush()
            os.fsync(output.fileno())


def repair_truncated_journal_tail(path: Path) -> Path | None:
    """Remove only a malformed final record, preserving its bytes in a sidecar.

    A power loss can interrupt one append despite flushing.  Malformed records
    anywhere else remain a hard error; silently skipping interior corruption
    could make resume decisions untrustworthy.
    """

    if not path.exists() or not path.stat().st_size:
        return None
    data = path.read_bytes()
    lines = data.splitlines(keepends=True)
    nonempty = [index for index, line in enumerate(lines) if line.strip(b"\r\n \t")]
    if not nonempty:
        return None
    last_nonempty = nonempty[-1]
    invalid: list[int] = []
    for index in nonempty:
        raw = lines[index].rstrip(b"\r\n")
        try:
            json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            invalid.append(index)
    if not invalid:
        if not data.endswith((b"\n", b"\r")):
            with path.open("ab") as output:
                output.write(b"\n")
                output.flush()
                os.fsync(output.fileno())
        return None
    if invalid != [last_nonempty]:
        line_numbers = ", ".join(str(index + 1) for index in invalid)
        raise ValueError(f"invalid non-terminal JSONL record(s) at {path}:{line_numbers}")

    byte_offset = sum(len(line) for line in lines[:last_nonempty])
    fragment = data[byte_offset:]
    sidecar = path.with_name(path.name + ".truncated")
    with sidecar.open("ab") as backup:
        backup.write(fragment)
        if fragment and not fragment.endswith((b"\n", b"\r")):
            backup.write(b"\n")
        backup.flush()
        os.fsync(backup.fileno())
    with path.open("r+b") as output:
        output.truncate(byte_offset)
        output.flush()
        os.fsync(output.fileno())
    return sidecar


def completed_run_ids(path: Path) -> set[str]:
    completed: set[str] = set()
    if not path.exists():
        return completed
    lines = path.read_text(encoding="utf-8").splitlines()
    last_nonempty = max((index for index, line in enumerate(lines, 1) if line.strip()), default=0)
    for line_number, line in enumerate(lines, 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            # A crash can leave only the final line truncated.  Older
            # malformed records are unsafe and should be repaired first.
            if line_number == last_nonempty:
                continue
            raise ValueError(f"invalid JSONL record at {path}:{line_number}")
        if record.get("event") == "result" and record.get("status") in COMPLETED_STATUSES:
            run_id = record.get("run_id")
            if isinstance(run_id, str):
                completed.add(run_id)
    return completed


def discover_cadical() -> Path | None:
    configured = os.environ.get("CADICAL")
    if configured:
        return Path(configured)
    on_path = shutil.which("cadical") or shutil.which("cadical.exe")
    if on_path:
        return Path(on_path)
    toolchain_root = HERE.parent / "toolchains"
    if toolchain_root.exists():
        candidates = sorted(toolchain_root.glob("**/bin/cadical.exe"))
        if candidates:
            return candidates[-1]
    return None


def _linux_rss_mb(pid: int) -> float | None:
    try:
        status = Path(f"/proc/{pid}/status").read_text(encoding="ascii")
    except (OSError, UnicodeError):
        return None
    match = re.search(r"^VmRSS:\s*([0-9]+)\s+kB$", status, re.MULTILINE)
    return int(match.group(1)) / 1024 if match else None


def _windows_rss_mb(pid: int) -> float | None:
    if os.name != "nt":
        return None

    class PROCESS_MEMORY_COUNTERS(ctypes.Structure):
        _fields_ = [
            ("cb", ctypes.c_ulong),
            ("PageFaultCount", ctypes.c_ulong),
            ("PeakWorkingSetSize", ctypes.c_size_t),
            ("WorkingSetSize", ctypes.c_size_t),
            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
            ("PagefileUsage", ctypes.c_size_t),
            ("PeakPagefileUsage", ctypes.c_size_t),
        ]

    process_query_information = 0x0400
    process_vm_read = 0x0010
    kernel32 = ctypes.windll.kernel32
    psapi = ctypes.windll.psapi
    handle = kernel32.OpenProcess(process_query_information | process_vm_read, False, pid)
    if not handle:
        return None
    try:
        counters = PROCESS_MEMORY_COUNTERS()
        counters.cb = ctypes.sizeof(counters)
        if not psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
            return None
        return counters.WorkingSetSize / (1024 * 1024)
    finally:
        kernel32.CloseHandle(handle)


def process_rss_mb(pid: int) -> float | None:
    return _windows_rss_mb(pid) if os.name == "nt" else _linux_rss_mb(pid)


def wait_for_process(
    process: subprocess.Popen[bytes],
    timeout_seconds: float | None,
    per_process_rss_mb: int | None,
) -> tuple[int, bool, bool, float | None]:
    deadline = None if timeout_seconds is None else time.monotonic() + timeout_seconds
    peak_rss: float | None = None
    timed_out = False
    memory_limited = False
    try:
        while process.poll() is None:
            try:
                rss = process_rss_mb(process.pid)
            except (OSError, AttributeError, ctypes.Error):
                rss = None
            if rss is not None:
                peak_rss = rss if peak_rss is None else max(peak_rss, rss)
                if per_process_rss_mb is not None and rss > per_process_rss_mb:
                    memory_limited = True
                    process.kill()
                    break
            if deadline is not None and time.monotonic() >= deadline:
                timed_out = True
                process.kill()
                break
            time.sleep(0.05)
        return_code = process.wait()
    except BaseException:
        if process.poll() is None:
            process.kill()
        process.wait()
        raise
    return return_code, timed_out, memory_limited, peak_rss


def load_manifest(path: Path) -> tuple[dict[str, Any], str]:
    document = json.loads(path.read_text(encoding="utf-8"))
    branches = document.get("branches")
    if not isinstance(branches, list) or not branches:
        raise ValueError("manifest has no branches")
    required = {"id", "degree", "codegree", "type_index", "catalogue", "catalogue_sha256"}
    ids: set[str] = set()
    for index, branch in enumerate(branches):
        if not isinstance(branch, dict) or not required.issubset(branch):
            raise ValueError(f"manifest branch {index} is missing required fields")
        branch_id = str(branch["id"])
        if branch_id in ids:
            raise ValueError(f"duplicate branch id {branch_id!r}")
        ids.add(branch_id)
    if document.get("branch_count") not in (None, len(branches)):
        raise ValueError("manifest branch_count does not match branches")
    return document, sha256_file(path)


def catalogue_path(manifest_path: Path, manifest: dict[str, Any], branch: dict[str, Any]) -> Path:
    directory = Path(str(manifest.get("catalogue_directory", ".")))
    if not directory.is_absolute():
        directory = manifest_path.parent / directory
    return (directory / str(branch["catalogue"])).resolve()


def run_identity(
    *,
    manifest_sha256: str,
    ramsey_sha256: str,
    cadical_sha256: str,
    branch: dict[str, Any],
    conflict_limit: int,
    timeout_seconds: float | None,
    per_process_rss_mb: int | None,
    cadical_options: Sequence[str],
    generator_options: dict[str, Any],
) -> tuple[str, dict[str, Any]]:
    payload = {
        "schema_version": SCHEMA_VERSION,
        "manifest_sha256": manifest_sha256,
        "ramsey_sha256": ramsey_sha256,
        "cadical_sha256": cadical_sha256,
        "branch": {
            "id": branch["id"],
            "degree": branch["degree"],
            "codegree": branch["codegree"],
            "type_index": branch["type_index"],
            "catalogue_sha256": branch["catalogue_sha256"],
        },
        "conflict_limit": conflict_limit,
        "timeout_seconds": timeout_seconds,
        "per_process_rss_mb": per_process_rss_mb,
        "cadical_options": list(cadical_options),
        "generator_options": generator_options,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()[:24], payload


def generator_command(
    python: Path,
    ramsey_script: Path,
    manifest: dict[str, Any],
    branch: dict[str, Any],
    catalogue: Path,
    cnf_path: Path,
    args: argparse.Namespace,
) -> list[str]:
    command = [
        str(python),
        str(ramsey_script),
        "write-typed-case-cnf",
        str(manifest["host_order"]),
        str(manifest["forbidden_clique"]),
        str(branch["degree"]),
        str(catalogue),
        str(branch["type_index"]),
        str(cnf_path),
        "--max-colour-degree",
        str(args.max_colour_degree),
        "--degree-encoding",
        args.degree_encoding,
    ]
    if args.edge_common_bound is not None:
        command.extend(("--edge-common-bound", str(args.edge_common_bound)))
    for flag in (
        "anchor_minimum_degree",
        "anchor_minimum_degree_specialized",
        "d20_c10_regularity",
        "signature_lex",
        "w5_first_signature_symmetry",
        "internal_cuts",
        "internal_star_cuts",
        "internal_edge_cuts",
        "internal_triangle_cuts",
    ):
        if getattr(args, flag):
            command.append("--" + flag.replace("_", "-"))
    return command


def _max_optional(left: float | None, right: float | None) -> float | None:
    values = [value for value in (left, right) if value is not None]
    return max(values) if values else None


def run_branch(
    *,
    args: argparse.Namespace,
    journal: Journal,
    manifest_path: Path,
    manifest: dict[str, Any],
    manifest_sha256: str,
    ramsey_script: Path,
    ramsey_sha256: str,
    cadical: Path,
    cadical_sha256: str,
    branch: dict[str, Any],
    run_id: str,
    identity: dict[str, Any],
) -> dict[str, Any]:
    branch_id = str(branch["id"])
    cnf_dir = args.work_dir / "cnfs"
    log_dir = args.work_dir / "logs"
    cnf_dir.mkdir(parents=True, exist_ok=True)
    log_dir.mkdir(parents=True, exist_ok=True)
    cnf_path = (cnf_dir / f"{run_id}_{branch_id}.cnf").resolve()
    generator_log = (log_dir / f"{run_id}.generator.log").resolve()
    stdout_log = (log_dir / f"{run_id}.stdout.log").resolve()
    stderr_log = (log_dir / f"{run_id}.stderr.log").resolve()
    catalogue = catalogue_path(manifest_path, manifest, branch)
    generate = generator_command(
        Path(sys.executable).resolve(), ramsey_script, manifest, branch, catalogue, cnf_path, args
    )
    solve = [str(cadical), *args.cadical_option, "-c", str(args.conflicts), str(cnf_path)]

    base_record = {
        "schema_version": SCHEMA_VERSION,
        "run_id": run_id,
        "branch_id": branch_id,
        "degree": int(branch["degree"]),
        "codegree": int(branch["codegree"]),
        "type_index": int(branch["type_index"]),
        "config_name": args.config_name,
        "conflict_limit": args.conflicts,
        "manifest": str(manifest_path),
        "manifest_sha256": manifest_sha256,
        "ramsey_sha256": ramsey_sha256,
        "cadical_sha256": cadical_sha256,
        "catalogue": str(catalogue),
        "catalogue_sha256": branch["catalogue_sha256"],
        "generator_command": generate,
        "command": solve,
        "identity": identity,
        "cnf_path": str(cnf_path),
        "generator_log": str(generator_log),
        "stdout_log": str(stdout_log),
        "stderr_log": str(stderr_log),
    }
    run_started_at = utc_now()
    run_start = time.monotonic()
    journal.append({**base_record, "event": "start", "started_at": run_started_at})

    result: dict[str, Any]
    cnf_sha256: str | None = None
    try:
        if not catalogue.is_file():
            raise FileNotFoundError(f"catalogue not found: {catalogue}")
        actual_catalogue_sha256 = sha256_file(catalogue)
        if actual_catalogue_sha256 != branch["catalogue_sha256"]:
            raise ValueError(
                f"catalogue hash mismatch: expected {branch['catalogue_sha256']}, "
                f"got {actual_catalogue_sha256}"
            )

        generation_start = time.monotonic()
        generated = subprocess.run(
            generate,
            cwd=manifest_path.parent,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        generation_elapsed = time.monotonic() - generation_start
        generator_log.write_bytes(generated.stdout)
        if generated.returncode != 0 or not cnf_path.is_file():
            result = {
                **base_record,
                "event": "result",
                "started_at": run_started_at,
                "finished_at": utc_now(),
                "stage": "generate",
                "status": "ERROR",
                "status_reason": f"generator_exit_code_{generated.returncode}",
                "exit_code": generated.returncode,
                "cnf_sha256": None,
                "elapsed_seconds": None,
                "generation_elapsed_seconds": round(generation_elapsed, 6),
                "total_elapsed_seconds": round(time.monotonic() - run_start, 6),
                "conflicts": None,
                "max_rss_mb": None,
            }
            journal.append(result)
            return result

        cnf_sha256 = sha256_file(cnf_path)
        solver_started_at = utc_now()
        start = time.monotonic()
        with stdout_log.open("wb") as stdout, stderr_log.open("wb") as stderr:
            process = subprocess.Popen(
                solve,
                cwd=manifest_path.parent,
                stdout=stdout,
                stderr=stderr,
            )
            return_code, timed_out, memory_limited, monitored_rss = wait_for_process(
                process, args.timeout_seconds, args.per_process_rss_mb
            )
        elapsed = time.monotonic() - start
        output_text = decode_solver_bytes(stdout_log.read_bytes())
        error_text = decode_solver_bytes(stderr_log.read_bytes())
        parsed = parse_solver_output(output_text + "\n" + error_text)
        status, reason = classify_solver_result(
            return_code,
            parsed["reported_status"],
            timed_out=timed_out,
            memory_limited=memory_limited,
        )
        result = {
            **base_record,
            "event": "result",
            "started_at": run_started_at,
            "solver_started_at": solver_started_at,
            "finished_at": utc_now(),
            "stage": "solve",
            "status": status,
            "status_reason": reason,
            "reported_status": parsed["reported_status"],
            "exit_code": return_code,
            "timed_out": timed_out,
            "memory_limited": memory_limited,
            "cnf_sha256": cnf_sha256,
            "elapsed_seconds": round(elapsed, 6),
            "generation_elapsed_seconds": round(generation_elapsed, 6),
            "total_elapsed_seconds": round(time.monotonic() - run_start, 6),
            "solver_real_seconds": parsed["solver_real_seconds"],
            "conflicts": parsed["conflicts"],
            "max_rss_mb": _max_optional(monitored_rss, parsed["reported_max_rss_mb"]),
            "reported_max_rss_mb": parsed["reported_max_rss_mb"],
        }
        journal.append(result)
        return result
    except Exception as error:  # Preserve enough context to retry and diagnose.
        result = {
            **base_record,
            "event": "result",
            "started_at": run_started_at,
            "finished_at": utc_now(),
            "stage": "runner",
            "status": "ERROR",
            "status_reason": type(error).__name__,
            "error": str(error),
            "exit_code": None,
            "cnf_sha256": cnf_sha256,
            "elapsed_seconds": None,
            "generation_elapsed_seconds": None,
            "total_elapsed_seconds": round(time.monotonic() - run_start, 6),
            "conflicts": None,
            "max_rss_mb": None,
        }
        journal.append(result)
        return result
    finally:
        if not args.keep_cnfs:
            try:
                cnf_path.unlink(missing_ok=True)
            except OSError:
                pass


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return parsed


def positive_float(value: str) -> float:
    parsed = float(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=HERE / "typed_manifest_tight.json")
    parser.add_argument("--ramsey-script", type=Path, default=HERE / "ramsey.py")
    parser.add_argument("--cadical", type=Path, help="CaDiCaL executable (or set CADICAL)")
    parser.add_argument("--output", type=Path, default=HERE / "pilot_results.jsonl")
    parser.add_argument("--work-dir", type=Path, default=HERE / "pilot_work")
    parser.add_argument("--conflicts", type=positive_int, default=1_000_000)
    parser.add_argument("--jobs", type=positive_int, default=1)
    parser.add_argument(
        "--max-memory-mb",
        type=positive_int,
        help="aggregate scheduling budget; jobs reserve --memory-per-job-mb each",
    )
    parser.add_argument(
        "--memory-per-job-mb", type=positive_int, default=DEFAULT_MEMORY_PER_JOB_MB
    )
    parser.add_argument(
        "--per-process-rss-mb",
        type=positive_int,
        help="kill a solver whose observed resident set exceeds this value",
    )
    parser.add_argument("--timeout-seconds", type=positive_float)
    parser.add_argument("--seed", default="r55-pilot-v1")
    parser.add_argument("--sampling", choices=("stratified", "global"), default="stratified")
    parser.add_argument("--select-degree", type=int, choices=(18, 20), action="append")
    parser.add_argument("--select-codegree", type=int, action="append")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--sample-size", type=positive_int)
    selection.add_argument("--all", action="store_true", help="explicitly select every branch")
    parser.add_argument(
        "--branch",
        action="append",
        default=[],
        help="select an exact branch ID; repeat for several (overrides sampling)",
    )
    parser.add_argument("--config-name", default="default")
    parser.add_argument(
        "--cadical-option",
        action="append",
        default=[],
        help="repeatable solver option; use --cadical-option=--unsat for leading dashes",
    )
    parser.add_argument("--max-colour-degree", type=positive_int, default=24)
    parser.add_argument("--degree-encoding", choices=("global", "rooted"), default="rooted")
    minimum = parser.add_mutually_exclusive_group()
    minimum.add_argument("--anchor-minimum-degree", action="store_true")
    minimum.add_argument("--anchor-minimum-degree-specialized", action="store_true")
    parser.add_argument("--d20-c10-regularity", action="store_true")
    parser.add_argument("--signature-lex", action="store_true")
    parser.add_argument("--w5-first-signature-symmetry", action="store_true")
    parser.add_argument("--edge-common-bound", type=positive_int)
    parser.add_argument("--internal-cuts", action="store_true")
    parser.add_argument("--internal-star-cuts", action="store_true")
    parser.add_argument("--internal-edge-cuts", action="store_true")
    parser.add_argument("--internal-triangle-cuts", action="store_true")
    parser.add_argument("--keep-cnfs", action="store_true")
    parser.add_argument("--rerun", action="store_true", help="ignore completed journal records")
    parser.add_argument("--dry-run", action="store_true", help="print the plan without generating CNFs")
    return parser


def _check_solver_options(parser: argparse.ArgumentParser, options: Iterable[str]) -> None:
    options = list(options)
    for option in options:
        if option == "-c" or option.startswith("--conflict"):
            parser.error("set the conflict budget with --conflicts, not --cadical-option")


def run_cli(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    _check_solver_options(parser, args.cadical_option)

    manifest_path = args.manifest.resolve()
    ramsey_script = args.ramsey_script.resolve()
    args.output = args.output.resolve()
    args.work_dir = args.work_dir.resolve()
    manifest, manifest_sha256 = load_manifest(manifest_path)
    branches: list[dict[str, Any]] = manifest["branches"]
    if args.select_degree:
        allowed_degrees = set(args.select_degree)
        branches = [branch for branch in branches if int(branch["degree"]) in allowed_degrees]
    if args.select_codegree:
        if any(codegree < 0 for codegree in args.select_codegree):
            parser.error("--select-codegree values must be non-negative")
        allowed_codegrees = set(args.select_codegree)
        branches = [branch for branch in branches if int(branch["codegree"]) in allowed_codegrees]
    if not branches:
        parser.error("branch filters selected no manifest entries")

    if args.branch:
        by_id = {str(branch["id"]): branch for branch in branches}
        missing = sorted(set(args.branch) - by_id.keys())
        if missing:
            parser.error("unknown branch ID(s): " + ", ".join(missing))
        selected = [by_id[branch_id] for branch_id in sorted(set(args.branch))]
    else:
        sample_size = len(branches) if args.all else (args.sample_size or DEFAULT_SAMPLE_SIZE)
        selected = deterministic_sample(
            branches,
            min(sample_size, len(branches)),
            args.seed,
            stratified=args.sampling == "stratified",
        )

    try:
        workers = effective_job_count(args.jobs, args.max_memory_mb, args.memory_per_job_mb)
    except ValueError as error:
        parser.error(str(error))

    cadical = args.cadical.resolve() if args.cadical else discover_cadical()
    plan = {
        "manifest": str(manifest_path),
        "manifest_sha256": manifest_sha256,
        "selected_count": len(selected),
        "selected_branch_ids": [branch["id"] for branch in selected],
        "seed": args.seed,
        "sampling": args.sampling,
        "select_degree": args.select_degree,
        "select_codegree": args.select_codegree,
        "conflict_limit": args.conflicts,
        "requested_jobs": args.jobs,
        "effective_jobs": workers,
        "max_memory_mb": args.max_memory_mb,
        "memory_per_job_mb": args.memory_per_job_mb,
        "per_process_rss_mb": args.per_process_rss_mb,
        "cadical": str(cadical.resolve()) if cadical else None,
        "cadical_options": args.cadical_option,
    }
    if args.dry_run:
        print(json.dumps(plan, indent=2, sort_keys=True))
        return 0

    if cadical is None or not cadical.is_file():
        parser.error("CaDiCaL was not found; pass --cadical or set CADICAL")
    if not ramsey_script.is_file():
        parser.error(f"ramsey.py not found: {ramsey_script}")

    ramsey_sha256 = sha256_file(ramsey_script)
    cadical_sha256 = sha256_file(cadical)
    generator_options = {
        "max_colour_degree": args.max_colour_degree,
        "degree_encoding": args.degree_encoding,
        "anchor_minimum_degree": args.anchor_minimum_degree,
        "anchor_minimum_degree_specialized": args.anchor_minimum_degree_specialized,
        "d20_c10_regularity": args.d20_c10_regularity,
        "signature_lex": args.signature_lex,
        "w5_first_signature_symmetry": args.w5_first_signature_symmetry,
        "edge_common_bound": args.edge_common_bound,
        "internal_cuts": args.internal_cuts,
        "internal_star_cuts": args.internal_star_cuts,
        "internal_edge_cuts": args.internal_edge_cuts,
        "internal_triangle_cuts": args.internal_triangle_cuts,
    }
    repaired_fragment = repair_truncated_journal_tail(args.output)
    if repaired_fragment is not None:
        print(f"recovered truncated journal tail to {repaired_fragment}", file=sys.stderr)
    jobs: list[tuple[dict[str, Any], str, dict[str, Any]]] = []
    already_completed = set() if args.rerun else completed_run_ids(args.output)
    for branch in selected:
        run_id, identity = run_identity(
            manifest_sha256=manifest_sha256,
            ramsey_sha256=ramsey_sha256,
            cadical_sha256=cadical_sha256,
            branch=branch,
            conflict_limit=args.conflicts,
            timeout_seconds=args.timeout_seconds,
            per_process_rss_mb=args.per_process_rss_mb,
            cadical_options=args.cadical_option,
            generator_options=generator_options,
        )
        if run_id not in already_completed:
            jobs.append((branch, run_id, identity))

    print(
        json.dumps(
            {
                **plan,
                "journal": str(args.output),
                "skipped_completed": len(selected) - len(jobs),
                "scheduled": len(jobs),
            },
            sort_keys=True,
        )
    )
    if not jobs:
        return 0

    journal = Journal(args.output)
    results: list[dict[str, Any]] = []
    common = {
        "args": args,
        "journal": journal,
        "manifest_path": manifest_path,
        "manifest": manifest,
        "manifest_sha256": manifest_sha256,
        "ramsey_script": ramsey_script,
        "ramsey_sha256": ramsey_sha256,
        "cadical": cadical.resolve(),
        "cadical_sha256": cadical_sha256,
    }
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures = {
            executor.submit(
                run_branch,
                **common,
                branch=branch,
                run_id=run_id,
                identity=identity,
            ): branch["id"]
            for branch, run_id, identity in jobs
        }
        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            results.append(result)
            print(
                json.dumps(
                    {
                        "branch_id": result["branch_id"],
                        "status": result["status"],
                        "elapsed_seconds": result.get("elapsed_seconds"),
                        "conflicts": result.get("conflicts"),
                        "max_rss_mb": result.get("max_rss_mb"),
                    },
                    sort_keys=True,
                )
            )

    counts: dict[str, int] = {}
    for result in results:
        counts[result["status"]] = counts.get(result["status"], 0) + 1
    print(json.dumps({"completed": len(results), "status_counts": counts}, sort_keys=True))
    return 1 if counts.get("ERROR", 0) else 0


def main() -> None:
    raise SystemExit(run_cli())


if __name__ == "__main__":
    main()
