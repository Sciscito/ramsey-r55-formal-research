#!/usr/bin/env python3
"""Optionally run one tightly bounded LRAT pilot on the frozen F`GOW leaf.

The default command is a solver-free preflight.  The only solver-launching
command is the explicit ``run`` subcommand.  It accepts only an existing
absolute S: directory and an exact, absolute-S: CaDiCaL binary.  Formula,
binary, output collisions, and residual partials are checked before launch.

This runner records a CaDiCaL-checked LRAT candidate.  It does not replay the
proof independently and therefore cannot establish a Lean theorem or a new
Ramsey bound by itself.
"""

from __future__ import annotations

import argparse
import ctypes
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import threading
import time
from ctypes import wintypes
from dataclasses import dataclass
from pathlib import Path, PureWindowsPath
from typing import BinaryIO

from . import materialize_cover6_d7_r34_fgravegow_leaf as leaf


SOLVER_NAME = "CaDiCaL"
SOLVER_VERSION = "2.1.2"
SOLVER_SHA256 = "AE6156A9C3BB46D8AC5E0A3892A5F11999EF6FD5F346304FD53DB9160FD5743B"
SOLVER_FLAGS = (
    "--lrat",
    "--no-binary",
    "--checkproof=2",
    "--unsat",
    "--walk=false",
)

# CaDiCaL 2.1.2 does not always print an ``lrat checker statistics`` section
# when ``--checkproof=2`` is active.  Success therefore relies on the stable
# option echo, process return code, UNSAT line, closed-proof line, exact proof
# byte count, and the absence of known fatal/checking diagnostics.
REQUIRED_CHECKPROOF2_MARKERS = (
    "unsatisfiable_status",
    "checkproof_option_echoed",
    "proof_closed",
    "no_cadical_error_diagnostic",
)
CADICAL_ERROR_DIAGNOSTICS = (
    b"*** cadical error:",
    b"cadical: error:",
    b"fatal error",
    b"assertion failed",
    b"proof check failed",
    b"proof checker failed",
    b"proof checking failed",
    b"failed to check proof",
    b"invalid proof",
    b"internal error",
)

CONFLICT_LIMIT = 25_000
WALL_LIMIT_SECONDS = 300.0
RSS_LIMIT_MIB = 1_536
RSS_LIMIT_BYTES = RSS_LIMIT_MIB * 1024 * 1024
PROOF_LIMIT_MIB = 512
PROOF_LIMIT_BYTES = PROOF_LIMIT_MIB * 1024 * 1024
LOG_LIMIT_MIB = 8
LOG_LIMIT_BYTES = LOG_LIMIT_MIB * 1024 * 1024
JOBS = 1
POLL_SECONDS = 0.05

ARTIFACT_STEM = "cover6_closed_f7_r34_i6_FgraveGOW_c25k"
PROOF_NAME = f"{ARTIFACT_STEM}.lrat"
STDOUT_NAME = f"{ARTIFACT_STEM}.cadical.stdout.log"
STDERR_NAME = f"{ARTIFACT_STEM}.cadical.stderr.log"
REPORT_NAME = f"{ARTIFACT_STEM}.lrat-run.json"
PARTIAL_SUFFIX = ".partial"
READ_BLOCK_BYTES = 1024 * 1024
PIPE_BLOCK_BYTES = 64 * 1024


class FgraveGowLratRunnerError(RuntimeError):
    """Raised at the first runner policy, identity, or supervision failure."""


@dataclass(frozen=True)
class RunPaths:
    formula: Path
    formula_partial: Path
    proof: Path
    proof_partial: Path
    stdout: Path
    stdout_partial: Path
    stderr: Path
    stderr_partial: Path
    report: Path
    report_partial: Path


@dataclass(frozen=True)
class MonitorResult:
    returncode: int | None
    stop_reason: str | None
    wall_seconds: float
    sampled_peak_rss_bytes: int
    maximum_observed_proof_bytes: int
    rss_sample_count: int
    monitor_error: str | None


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb", buffering=READ_BLOCK_BYTES) as stream:
        for block in iter(lambda: stream.read(READ_BLOCK_BYTES), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def file_identity(path: Path) -> dict[str, int | str]:
    return {
        "name": path.name,
        "bytes": path.stat().st_size,
        "sha256": sha256_file(path),
    }


def require_absolute_s_path(path: Path, label: str) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise FgraveGowLratRunnerError(
            f"{label} must be an absolute S: path, got {path}"
        )
    return path


def run_paths(directory: Path) -> RunPaths:
    formula = directory / leaf.TARGET_NAME
    proof = directory / PROOF_NAME
    stdout = directory / STDOUT_NAME
    stderr = directory / STDERR_NAME
    report = directory / REPORT_NAME
    return RunPaths(
        formula=formula,
        formula_partial=directory / f"{leaf.TARGET_NAME}{leaf.PARTIAL_SUFFIX}",
        proof=proof,
        proof_partial=directory / f"{PROOF_NAME}{PARTIAL_SUFFIX}",
        stdout=stdout,
        stdout_partial=directory / f"{STDOUT_NAME}{PARTIAL_SUFFIX}",
        stderr=stderr,
        stderr_partial=directory / f"{STDERR_NAME}{PARTIAL_SUFFIX}",
        report=report,
        report_partial=directory / f"{REPORT_NAME}{PARTIAL_SUFFIX}",
    )


def refuse_artifact_collisions(paths: RunPaths) -> None:
    if paths.formula_partial.exists():
        raise FileExistsError(
            f"refusing residual formula partial: {paths.formula_partial}"
        )
    for final, partial in (
        (paths.proof, paths.proof_partial),
        (paths.stdout, paths.stdout_partial),
        (paths.stderr, paths.stderr_partial),
        (paths.report, paths.report_partial),
    ):
        if final.exists():
            raise FileExistsError(f"refusing to overwrite runner artifact: {final}")
        if partial.exists():
            raise FileExistsError(f"refusing residual runner partial: {partial}")


def solver_command(solver: Path, formula: Path, proof_partial: Path) -> list[str]:
    return [
        str(solver),
        *SOLVER_FLAGS,
        "-c",
        str(CONFLICT_LIMIT),
        str(formula),
        str(proof_partial),
    ]


def _match_integer(log_text: str, name: str) -> int | None:
    match = re.search(rf"^c {re.escape(name)}:\s+(\d+)", log_text, re.MULTILINE)
    return int(match.group(1)) if match else None


def _match_float(log_text: str, pattern: str) -> float | None:
    match = re.search(pattern, log_text, re.MULTILINE)
    return float(match.group(1)) if match else None


def parse_metrics(log_text: str) -> dict[str, int | float | None]:
    return {
        "conflicts": _match_integer(log_text, "conflicts"),
        "decisions": _match_integer(log_text, "decisions"),
        "fixed_variables": _match_integer(log_text, "fixed"),
        "learned_clauses": _match_integer(log_text, "learned"),
        "lrat_added_clauses": (
            int(match.group(1))
            if (match := re.search(r"^c LRAT (\d+) added clauses", log_text, re.MULTILINE))
            else None
        ),
        "lrat_deleted_clauses": (
            int(match.group(1))
            if (match := re.search(r"^c LRAT (\d+) deleted clauses", log_text, re.MULTILINE))
            else None
        ),
        "solver_reported_lrat_bytes": (
            int(match.group(1))
            if (match := re.search(r"^c LRAT (\d+) bytes", log_text, re.MULTILINE))
            else None
        ),
        "total_process_seconds": _match_float(
            log_text,
            r"^c total process time since initialization:\s+([0-9.]+)\s+seconds",
        ),
        "total_real_seconds": _match_float(
            log_text,
            r"^c total real time since initialization:\s+([0-9.]+)\s+seconds",
        ),
        "solver_reported_maximum_resident_mib": _match_float(
            log_text,
            r"^c maximum resident set size of process:\s+([0-9.]+)\s+MB",
        ),
    }


def proof_check_markers(
    log_data: bytes, stderr_data: bytes = b""
) -> dict[str, bool]:
    combined_lower = log_data.lower() + b"\n" + stderr_data.lower()
    return {
        "unsatisfiable_status": re.search(
            rb"(?m)^s UNSATISFIABLE\r?$", log_data
        )
        is not None,
        "checkproof_option_echoed": b"--checkproof=2" in log_data,
        "proof_closed": re.search(
            rb"(?m)^c LRAT proof file .* closed\r?$", log_data
        )
        is not None,
        "no_cadical_error_diagnostic": not any(
            diagnostic in combined_lower
            for diagnostic in CADICAL_ERROR_DIAGNOSTICS
        ),
        "optional_lrat_checker_statistics_present": (
            b"--- [ lrat checker statistics ]" in log_data
        ),
    }


def markers_establish_cadical_checked_lrat(markers: dict[str, bool]) -> bool:
    return all(markers.get(name, False) for name in REQUIRED_CHECKPROOF2_MARKERS)


def classify_outcome(
    stop_reason: str | None,
    returncode: int | None,
    proof_bytes: int,
    proof_size_matches_solver_log: bool,
    markers: dict[str, bool],
) -> str:
    if stop_reason is not None:
        return stop_reason
    if returncode != 20:
        return "SOLVER_DID_NOT_RETURN_UNSAT"
    if proof_bytes <= 0:
        return "LRAT_MISSING_OR_EMPTY"
    if proof_bytes >= PROOF_LIMIT_BYTES:
        return "PROOF_SIZE_LIMIT"
    if not proof_size_matches_solver_log:
        return "LRAT_SIZE_DISAGREES_WITH_SOLVER_LOG"
    if not markers_establish_cadical_checked_lrat(markers):
        return "CADICAL_SELF_CHECK_MARKERS_INCOMPLETE"
    return "CADICAL_CHECKED_LRAT_CANDIDATE"


class CombinedLogBudget:
    """Copy two process pipes while enforcing one exact combined byte budget."""

    def __init__(self, limit_bytes: int) -> None:
        if limit_bytes <= 0:
            raise ValueError("combined log limit must be positive")
        self.limit_bytes = limit_bytes
        self.total_bytes = 0
        self.limit_reached = threading.Event()
        self._lock = threading.Lock()
        self._errors: list[str] = []

    @property
    def errors(self) -> tuple[str, ...]:
        with self._lock:
            return tuple(self._errors)

    def accepted_prefix(self, block: bytes) -> bytes:
        with self._lock:
            remaining = max(0, self.limit_bytes - self.total_bytes)
            accepted = block[:remaining]
            self.total_bytes += len(accepted)
            if len(block) > remaining or self.total_bytes >= self.limit_bytes:
                self.limit_reached.set()
            return accepted

    def copy(self, source: BinaryIO, target: BinaryIO) -> None:
        try:
            while True:
                block = source.read(PIPE_BLOCK_BYTES)
                if not block:
                    break
                accepted = self.accepted_prefix(block)
                if accepted:
                    target.write(accepted)
        except BaseException as error:
            with self._lock:
                self._errors.append(f"{type(error).__name__}: {error}")
            self.limit_reached.set()


class WindowsProcessMemory:
    """Read current and peak working set for one direct Windows process."""

    PROCESS_QUERY_INFORMATION = 0x0400
    PROCESS_VM_READ = 0x0010

    class PROCESS_MEMORY_COUNTERS_EX(ctypes.Structure):
        _fields_ = (
            ("cb", wintypes.DWORD),
            ("PageFaultCount", wintypes.DWORD),
            ("PeakWorkingSetSize", ctypes.c_size_t),
            ("WorkingSetSize", ctypes.c_size_t),
            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
            ("PagefileUsage", ctypes.c_size_t),
            ("PeakPagefileUsage", ctypes.c_size_t),
            ("PrivateUsage", ctypes.c_size_t),
        )

    def __init__(self, pid: int) -> None:
        if os.name != "nt":
            raise FgraveGowLratRunnerError("RSS supervision requires Windows")
        self._kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        self._psapi = ctypes.WinDLL("psapi", use_last_error=True)
        self._kernel32.OpenProcess.argtypes = (
            wintypes.DWORD,
            wintypes.BOOL,
            wintypes.DWORD,
        )
        self._kernel32.OpenProcess.restype = wintypes.HANDLE
        self._kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
        self._kernel32.CloseHandle.restype = wintypes.BOOL
        self._psapi.GetProcessMemoryInfo.argtypes = (
            wintypes.HANDLE,
            ctypes.POINTER(self.PROCESS_MEMORY_COUNTERS_EX),
            wintypes.DWORD,
        )
        self._psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
        access = self.PROCESS_QUERY_INFORMATION | self.PROCESS_VM_READ
        self._handle = self._kernel32.OpenProcess(access, False, pid)
        if not self._handle:
            raise ctypes.WinError(ctypes.get_last_error())

    def sample(self) -> tuple[int, int]:
        counters = self.PROCESS_MEMORY_COUNTERS_EX()
        counters.cb = ctypes.sizeof(counters)
        if not self._psapi.GetProcessMemoryInfo(
            self._handle, ctypes.byref(counters), counters.cb
        ):
            raise ctypes.WinError(ctypes.get_last_error())
        return int(counters.WorkingSetSize), int(counters.PeakWorkingSetSize)

    def close(self) -> None:
        if self._handle:
            self._kernel32.CloseHandle(self._handle)
            self._handle = None

    def __enter__(self) -> "WindowsProcessMemory":
        return self

    def __exit__(self, *_unused: object) -> None:
        self.close()


class _JOBOBJECT_BASIC_LIMIT_INFORMATION(ctypes.Structure):
    _fields_ = (
        ("PerProcessUserTimeLimit", ctypes.c_int64),
        ("PerJobUserTimeLimit", ctypes.c_int64),
        ("LimitFlags", wintypes.DWORD),
        ("MinimumWorkingSetSize", ctypes.c_size_t),
        ("MaximumWorkingSetSize", ctypes.c_size_t),
        ("ActiveProcessLimit", wintypes.DWORD),
        ("Affinity", ctypes.c_size_t),
        ("PriorityClass", wintypes.DWORD),
        ("SchedulingClass", wintypes.DWORD),
    )


class _IO_COUNTERS(ctypes.Structure):
    _fields_ = (
        ("ReadOperationCount", ctypes.c_uint64),
        ("WriteOperationCount", ctypes.c_uint64),
        ("OtherOperationCount", ctypes.c_uint64),
        ("ReadTransferCount", ctypes.c_uint64),
        ("WriteTransferCount", ctypes.c_uint64),
        ("OtherTransferCount", ctypes.c_uint64),
    )


class _JOBOBJECT_EXTENDED_LIMIT_INFORMATION(ctypes.Structure):
    _fields_ = (
        ("BasicLimitInformation", _JOBOBJECT_BASIC_LIMIT_INFORMATION),
        ("IoInfo", _IO_COUNTERS),
        ("ProcessMemoryLimit", ctypes.c_size_t),
        ("JobMemoryLimit", ctypes.c_size_t),
        ("PeakProcessMemoryUsed", ctypes.c_size_t),
        ("PeakJobMemoryUsed", ctypes.c_size_t),
    )


class WindowsJobObject:
    """Hard-limit one process and kill it if the supervising handle closes."""

    JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x00000100
    JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000
    JOB_OBJECT_EXTENDED_LIMIT_INFORMATION_CLASS = 9

    def __init__(self, process_memory_limit_bytes: int) -> None:
        if os.name != "nt":
            raise FgraveGowLratRunnerError("Job Object supervision requires Windows")
        if process_memory_limit_bytes <= 0:
            raise ValueError("Job Object process memory limit must be positive")
        self.process_memory_limit_bytes = process_memory_limit_bytes
        self._kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        self._kernel32.CreateJobObjectW.argtypes = (
            ctypes.c_void_p,
            wintypes.LPCWSTR,
        )
        self._kernel32.CreateJobObjectW.restype = wintypes.HANDLE
        self._kernel32.SetInformationJobObject.argtypes = (
            wintypes.HANDLE,
            ctypes.c_int,
            ctypes.c_void_p,
            wintypes.DWORD,
        )
        self._kernel32.SetInformationJobObject.restype = wintypes.BOOL
        self._kernel32.AssignProcessToJobObject.argtypes = (
            wintypes.HANDLE,
            wintypes.HANDLE,
        )
        self._kernel32.AssignProcessToJobObject.restype = wintypes.BOOL
        self._kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
        self._kernel32.CloseHandle.restype = wintypes.BOOL
        self._handle = self._kernel32.CreateJobObjectW(None, None)
        if not self._handle:
            raise ctypes.WinError(ctypes.get_last_error())
        information = _JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        information.BasicLimitInformation.LimitFlags = (
            self.JOB_OBJECT_LIMIT_PROCESS_MEMORY
            | self.JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
        )
        information.ProcessMemoryLimit = process_memory_limit_bytes
        if not self._kernel32.SetInformationJobObject(
            self._handle,
            self.JOB_OBJECT_EXTENDED_LIMIT_INFORMATION_CLASS,
            ctypes.byref(information),
            ctypes.sizeof(information),
        ):
            error = ctypes.WinError(ctypes.get_last_error())
            self.close()
            raise error
        self.assigned = False

    def assign(self, process: subprocess.Popen[bytes]) -> None:
        process_handle = getattr(process, "_handle", None)
        if process_handle is None:
            raise FgraveGowLratRunnerError("Popen has no Windows process handle")
        if not self._kernel32.AssignProcessToJobObject(
            self._handle, wintypes.HANDLE(int(process_handle))
        ):
            raise ctypes.WinError(ctypes.get_last_error())
        self.assigned = True

    def close(self) -> None:
        if self._handle:
            self._kernel32.CloseHandle(self._handle)
            self._handle = None

    def __enter__(self) -> "WindowsJobObject":
        return self

    def __exit__(self, *_unused: object) -> None:
        self.close()


def _proof_size(path: Path) -> int:
    try:
        return path.stat().st_size
    except FileNotFoundError:
        return 0


def monitor_process(
    process: subprocess.Popen[bytes],
    proof_partial: Path,
    logs: CombinedLogBudget,
) -> MonitorResult:
    started = time.perf_counter()
    stop_reason: str | None = None
    peak_rss = 0
    max_proof = 0
    sample_count = 0
    monitor_error: str | None = None
    try:
        memory_context = WindowsProcessMemory(process.pid)
    except BaseException as error:
        process.kill()
        process.wait()
        return MonitorResult(
            process.returncode,
            "RSS_MONITOR_UNAVAILABLE",
            time.perf_counter() - started,
            0,
            _proof_size(proof_partial),
            0,
            f"{type(error).__name__}: {error}",
        )
    with memory_context as memory:
        while True:
            returncode = process.poll()
            elapsed = time.perf_counter() - started
            proof_bytes = _proof_size(proof_partial)
            max_proof = max(max_proof, proof_bytes)
            try:
                _current_rss, process_peak = memory.sample()
                peak_rss = max(peak_rss, process_peak)
                sample_count += 1
            except BaseException as error:
                if returncode is None:
                    stop_reason = "RSS_MONITOR_ERROR"
                    monitor_error = f"{type(error).__name__}: {error}"
            if returncode is not None:
                break
            if stop_reason is None and logs.errors:
                stop_reason = "LOG_CAPTURE_ERROR"
                monitor_error = "; ".join(logs.errors)
            if stop_reason is None and elapsed >= WALL_LIMIT_SECONDS:
                stop_reason = "WALL_LIMIT"
            if stop_reason is None and peak_rss >= RSS_LIMIT_BYTES:
                stop_reason = "RSS_LIMIT"
            if stop_reason is None and proof_bytes >= PROOF_LIMIT_BYTES:
                stop_reason = "PROOF_SIZE_LIMIT"
            if stop_reason is None and logs.limit_reached.is_set():
                stop_reason = "LOG_BYTES_LIMIT"
            if stop_reason is not None:
                process.kill()
                break
            time.sleep(POLL_SECONDS)
        if process.poll() is None:
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        else:
            process.wait()
        elapsed = time.perf_counter() - started
        max_proof = max(max_proof, _proof_size(proof_partial))
    if stop_reason is None and elapsed >= WALL_LIMIT_SECONDS:
        stop_reason = "WALL_LIMIT"
    if stop_reason is None and peak_rss >= RSS_LIMIT_BYTES:
        stop_reason = "RSS_LIMIT"
    if stop_reason is None and max_proof >= PROOF_LIMIT_BYTES:
        stop_reason = "PROOF_SIZE_LIMIT"
    if stop_reason is None and logs.limit_reached.is_set():
        stop_reason = "LOG_BYTES_LIMIT"
    return MonitorResult(
        process.returncode,
        stop_reason,
        elapsed,
        peak_rss,
        max_proof,
        sample_count,
        monitor_error,
    )


def publish_new(partial: Path, final: Path) -> None:
    if final.exists():
        raise FileExistsError(f"refusing publish race over existing artifact: {final}")
    os.rename(partial, final)


def cleanup_owned_partials(owned: set[Path]) -> None:
    """Delete only partial paths exclusively reserved by this invocation."""

    failures: list[str] = []
    for path in tuple(owned):
        try:
            if path.exists():
                path.unlink()
            owned.remove(path)
        except OSError as error:
            failures.append(f"{path}: {error}")
    if failures:
        raise FgraveGowLratRunnerError(
            "failed to clean runner-owned partials: " + "; ".join(failures)
        )


def reserve_runner_partials(paths: RunPaths) -> set[Path]:
    """Exclusively reserve proof/stdout/stderr partials or clean all new ones."""

    owned: set[Path] = set()
    try:
        for path in (
            paths.proof_partial,
            paths.stdout_partial,
            paths.stderr_partial,
        ):
            stream = path.open("xb")
            owned.add(path)
            stream.close()
        return owned
    except BaseException:
        cleanup_owned_partials(owned)
        raise


def publish_owned(partial: Path, final: Path, owned: set[Path]) -> None:
    if partial not in owned:
        raise FgraveGowLratRunnerError(
            f"refusing to publish an unowned partial: {partial}"
        )
    publish_new(partial, final)
    owned.remove(partial)


def discard_owned_partial(path: Path, owned: set[Path]) -> None:
    if path not in owned:
        raise FgraveGowLratRunnerError(
            f"refusing to delete an unowned partial: {path}"
        )
    if path.exists():
        path.unlink()
    owned.remove(path)


def atomic_write_new_json(path: Path, partial: Path, value: object) -> None:
    if path.exists():
        raise FileExistsError(f"refusing to overwrite runner report: {path}")
    if partial.exists():
        raise FileExistsError(f"refusing residual report partial: {partial}")
    data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    created = False
    try:
        with partial.open("xb") as stream:
            created = True
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        publish_new(partial, path)
        created = False
    finally:
        if created and partial.exists():
            partial.unlink()


def preflight() -> dict[str, object]:
    leaf_result = leaf.preflight()
    placeholder = Path(r"S:\ABSOLUTE\RUN")
    paths = run_paths(placeholder)
    command = solver_command(
        Path(r"S:\ABSOLUTE\cadical.exe"), paths.formula, paths.proof_partial
    )
    return {
        "status": "PREFLIGHT_ONLY_NO_SOLVER_INVOKED",
        "formula": leaf_result["target"],
        "selection": leaf_result["selection"],
        "solver": {
            "name": SOLVER_NAME,
            "version": SOLVER_VERSION,
            "required_binary_sha256": SOLVER_SHA256,
            "flags": list(SOLVER_FLAGS),
            "conflict_limit": CONFLICT_LIMIT,
            "jobs": JOBS,
        },
        "supervision": {
            "wall_limit_seconds": WALL_LIMIT_SECONDS,
            "rss_limit_mib": RSS_LIMIT_MIB,
            "proof_limit_mib": PROOF_LIMIT_MIB,
            "combined_log_limit_mib": LOG_LIMIT_MIB,
            "poll_seconds": POLL_SECONDS,
            "threshold_semantics": "every wrapper cap triggers at observed value >= limit",
            "windows_job_object": {
                "required": True,
                "process_memory_limit_mib": RSS_LIMIT_MIB,
                "kill_on_job_close": True,
                "memory_measure": "hard per-process committed-memory ceiling",
            },
            "rss_sampling": {
                "scope": "direct CaDiCaL process; CaDiCaL launches no child jobs",
                "memory_measure": "working-set RSS",
                "stop_at_or_above_limit": True,
            },
        },
        "outputs": {
            "proof": PROOF_NAME,
            "stdout": STDOUT_NAME,
            "stderr": STDERR_NAME,
            "report": REPORT_NAME,
            "partial_suffix": PARTIAL_SUFFIX,
        },
        "path_policy": "formula, solver, proof, logs, and report must be on absolute S: paths",
        "overwrite_policy": "all final artifacts and .partial names must be absent",
        "command_template": command,
        "launch_policy": "only the explicit run command can invoke CaDiCaL",
        "success_policy": (
            "return code 20; exact UNSAT status; --checkproof=2 echoed; LRAT "
            "closed; solver-reported LRAT bytes equal file bytes; no recognized "
            "CaDiCaL error diagnostic. The optional lrat-checker-statistics "
            "section is not required by CaDiCaL 2.1.2."
        ),
        "formal_boundary": (
            "a successful run is a CaDiCaL-checked LRAT candidate pending "
            "independent LRAT/Lean replay and semantic S7 composition"
        ),
    }


def execute_supervised_process(
    command: list[str],
    directory: Path,
    environment: dict[str, str],
    paths: RunPaths,
    stdout_stream: BinaryIO,
    stderr_stream: BinaryIO,
    log_budget: CombinedLogBudget,
    *,
    popen_factory=subprocess.Popen,
    job_factory=WindowsJobObject,
    monitor_factory=monitor_process,
) -> tuple[MonitorResult, str | None, bool]:
    """Launch through injectable factories so supervision is solver-free testable."""

    monitor = MonitorResult(None, "LAUNCH_ERROR", 0.0, 0, 0, 0, None)
    launch_error: str | None = None
    threads: list[threading.Thread] = []
    process: subprocess.Popen[bytes] | None = None
    job = None
    job_assigned = False
    try:
        process = popen_factory(
            command,
            cwd=directory,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
        job = job_factory(RSS_LIMIT_BYTES)
        job.assign(process)
        job_assigned = True
        if process.stdout is None or process.stderr is None:
            raise FgraveGowLratRunnerError("CaDiCaL pipes were not created")
        threads = [
            threading.Thread(
                target=log_budget.copy,
                args=(process.stdout, stdout_stream),
                name="fgravegow-cadical-stdout",
            ),
            threading.Thread(
                target=log_budget.copy,
                args=(process.stderr, stderr_stream),
                name="fgravegow-cadical-stderr",
            ),
        ]
        for thread in threads:
            thread.start()
        monitor = monitor_factory(process, paths.proof_partial, log_budget)
    except BaseException as error:
        launch_error = f"{type(error).__name__}: {error}"
        if process is not None and process.poll() is None:
            process.kill()
            process.wait()
        monitor = MonitorResult(
            process.returncode if process is not None else None,
            "LAUNCH_OR_MONITOR_ERROR",
            monitor.wall_seconds,
            monitor.sampled_peak_rss_bytes,
            max(
                monitor.maximum_observed_proof_bytes,
                _proof_size(paths.proof_partial),
            ),
            monitor.rss_sample_count,
            launch_error,
        )
    finally:
        for thread in threads:
            thread.join(timeout=10)
        if any(thread.is_alive() for thread in threads):
            if process is not None and process.poll() is None:
                process.kill()
                process.wait()
            for pipe in (
                process.stdout if process is not None else None,
                process.stderr if process is not None else None,
            ):
                if pipe is not None:
                    pipe.close()
            for thread in threads:
                thread.join(timeout=2)
            launch_error = "log capture thread did not terminate"
            monitor = MonitorResult(
                monitor.returncode,
                "LOG_CAPTURE_THREAD_TIMEOUT",
                monitor.wall_seconds,
                monitor.sampled_peak_rss_bytes,
                monitor.maximum_observed_proof_bytes,
                monitor.rss_sample_count,
                launch_error,
            )
        if launch_error is not None:
            message = ("runner launch/monitor error: " + launch_error + "\n").encode(
                "utf-8", "replace"
            )
            accepted = log_budget.accepted_prefix(message)
            if accepted:
                stderr_stream.write(accepted)
        stdout_stream.flush()
        stderr_stream.flush()
        os.fsync(stdout_stream.fileno())
        os.fsync(stderr_stream.fileno())
        if job is not None:
            job.close()
    return monitor, launch_error, job_assigned


def _publish_logs(
    paths: RunPaths, owned: set[Path]
) -> tuple[dict[str, int | str], dict[str, int | str]]:
    publish_owned(paths.stdout_partial, paths.stdout, owned)
    publish_owned(paths.stderr_partial, paths.stderr, owned)
    return file_identity(paths.stdout), file_identity(paths.stderr)


def _run_reserved(
    paths: RunPaths,
    directory: Path,
    solver: Path,
    observed_solver_hash: str,
    command: list[str],
    environment: dict[str, str],
    formula: dict[str, int | str],
    started_utc: str,
    owned: set[Path],
) -> dict[str, object]:
    log_budget = CombinedLogBudget(LOG_LIMIT_BYTES)
    with paths.stdout_partial.open("r+b") as stdout_stream:
        with paths.stderr_partial.open("r+b") as stderr_stream:
            monitor, launch_error, job_assigned = execute_supervised_process(
                command,
                directory,
                environment,
                paths,
                stdout_stream,
                stderr_stream,
                log_budget,
            )

    stdout_data = paths.stdout_partial.read_bytes()
    stderr_data = paths.stderr_partial.read_bytes()
    markers = proof_check_markers(stdout_data, stderr_data)
    metrics = parse_metrics(stdout_data.decode("utf-8", "replace"))
    stop_reason = monitor.stop_reason
    if stop_reason is None and log_budget.errors:
        stop_reason = "LOG_CAPTURE_ERROR"
    if stop_reason is None and log_budget.limit_reached.is_set():
        stop_reason = "LOG_BYTES_LIMIT"
    reported_rss = metrics["solver_reported_maximum_resident_mib"]
    if (
        stop_reason is None
        and isinstance(reported_rss, float)
        and reported_rss >= RSS_LIMIT_MIB
    ):
        stop_reason = "SOLVER_REPORTED_RSS_LIMIT"
    proof_bytes = _proof_size(paths.proof_partial)
    if stop_reason is None and proof_bytes >= PROOF_LIMIT_BYTES:
        stop_reason = "PROOF_SIZE_LIMIT"
    captured_log_bytes = len(stdout_data) + len(stderr_data)
    if stop_reason is None and captured_log_bytes >= LOG_LIMIT_BYTES:
        stop_reason = "LOG_BYTES_LIMIT"
    reported_lrat_bytes = metrics["solver_reported_lrat_bytes"]
    proof_size_matches_solver_log = (
        isinstance(reported_lrat_bytes, int) and reported_lrat_bytes == proof_bytes
    )
    outcome_reason = classify_outcome(
        stop_reason,
        monitor.returncode,
        proof_bytes,
        proof_size_matches_solver_log,
        markers,
    )
    success = outcome_reason == "CADICAL_CHECKED_LRAT_CANDIDATE"
    discarded_proof: dict[str, object] | None = None
    proof_metadata: dict[str, int | str] | None = None
    if success:
        proof_metadata = file_identity(paths.proof_partial)
        proof_metadata["name"] = paths.proof.name
    else:
        discarded_proof = {
            "name": paths.proof_partial.name,
            "bytes_before_removal": proof_bytes,
            "removed": True,
            "reason": "incomplete or unverified LRAT is never published",
        }
        discard_owned_partial(paths.proof_partial, owned)

    stdout_metadata, stderr_metadata = _publish_logs(paths, owned)
    if success:
        publish_owned(paths.proof_partial, paths.proof, owned)
    report: dict[str, object] = {
        "schema_version": 1,
        "status": (
            "CADICAL_CHECKED_LRAT_CANDIDATE_PENDING_INDEPENDENT_REPLAY"
            if success
            else "INCONCLUSIVE_NO_LRAT_PUBLISHED"
        ),
        "started_utc": started_utc,
        "formula": formula,
        "selection": leaf.audit_selection(),
        "solver": {
            "name": SOLVER_NAME,
            "version": SOLVER_VERSION,
            "path": str(solver),
            "binary_sha256": observed_solver_hash,
            "flags": list(SOLVER_FLAGS),
            "conflict_limit": CONFLICT_LIMIT,
            "jobs": JOBS,
            "command": command,
            "returncode": monitor.returncode,
        },
        "supervision": {
            "wall_limit_seconds": WALL_LIMIT_SECONDS,
            "rss_limit_bytes": RSS_LIMIT_BYTES,
            "proof_limit_bytes": PROOF_LIMIT_BYTES,
            "combined_log_limit_bytes": LOG_LIMIT_BYTES,
            "threshold_semantics": "each wrapper cap triggers at observed value >= limit",
            "windows_job_object": {
                "assigned": job_assigned,
                "process_memory_limit_bytes": RSS_LIMIT_BYTES,
                "kill_on_job_close": True,
                "memory_measure": "hard per-process committed-memory ceiling",
            },
            "rss_sampling": {
                "poll_seconds": POLL_SECONDS,
                "measure": "working-set RSS",
                "stop_at_or_above_limit": True,
            },
            "stop_reason": stop_reason,
            "wall_seconds": round(monitor.wall_seconds, 6),
            "sampled_peak_rss_bytes": monitor.sampled_peak_rss_bytes,
            "rss_sample_count": monitor.rss_sample_count,
            "maximum_observed_proof_bytes": max(
                monitor.maximum_observed_proof_bytes, proof_bytes
            ),
            "captured_combined_log_bytes": captured_log_bytes,
            "log_limit_reached": log_budget.limit_reached.is_set(),
            "monitor_error": monitor.monitor_error or launch_error,
        },
        "result": {
            "outcome_reason": outcome_reason,
            "cadical_checked_lrat_markers": markers,
            "metrics": metrics,
            "proof_size_matches_solver_log": proof_size_matches_solver_log,
            "lrat_published": success,
            "lrat": proof_metadata,
            "discarded_partial_lrat": discarded_proof,
        },
        "logs": {"stdout": stdout_metadata, "stderr": stderr_metadata},
        "formal_boundary": {
            "proof_level": (
                "solver-produced certificate candidate with --checkproof=2 "
                "requested/echoed and no recognized CaDiCaL error diagnostic"
            ),
            "missing": "independent LRAT-Catcher/Lean replay and semantic S7 composition",
            "claim_forbidden": (
                "do not claim a cover6-d7 theorem or Ramsey-number bound from this run"
            ),
        },
    }
    atomic_write_new_json(paths.report, paths.report_partial, report)
    return report


def run(directory: Path, solver: Path) -> dict[str, object]:
    preflight()
    directory = require_absolute_s_path(directory, "runner directory")
    solver = require_absolute_s_path(solver, "CaDiCaL binary")
    if os.name != "nt":
        raise FgraveGowLratRunnerError("the supervised S: runner requires Windows")
    if not directory.is_dir():
        raise FileNotFoundError(f"runner directory does not exist: {directory}")
    if not solver.is_file():
        raise FileNotFoundError(f"CaDiCaL binary does not exist: {solver}")
    paths = run_paths(directory)
    refuse_artifact_collisions(paths)
    formula = leaf.inspect_stream(paths.formula, leaf.TARGET_IDENTITY)
    observed_solver_hash = sha256_file(solver)
    if observed_solver_hash != SOLVER_SHA256:
        raise FgraveGowLratRunnerError(
            f"CaDiCaL binary SHA-256 mismatch: {observed_solver_hash}"
        )
    command = solver_command(solver, paths.formula, paths.proof_partial)
    environment = os.environ.copy()
    environment["TEMP"] = str(directory)
    environment["TMP"] = str(directory)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    started_utc = dt.datetime.now(dt.timezone.utc).isoformat()
    owned = reserve_runner_partials(paths)
    try:
        return _run_reserved(
            paths,
            directory,
            solver,
            observed_solver_hash,
            command,
            environment,
            formula,
            started_utc,
            owned,
        )
    finally:
        cleanup_owned_partials(owned)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", nargs="?", default="preflight", choices=("preflight", "run")
    )
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--solver", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    else:
        if args.directory is None or args.solver is None:
            parser.error("run requires --directory and --solver")
        result = run(args.directory, args.solver)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
