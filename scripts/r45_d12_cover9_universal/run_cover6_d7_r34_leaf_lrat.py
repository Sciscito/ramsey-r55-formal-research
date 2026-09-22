#!/usr/bin/env python3
"""Safely run one bounded LRAT pilot for a pending parameterized R34 leaf.

The default is a solver-free preflight for ``FoDPO``.  Only the explicit
``run`` command can launch CaDiCaL, and it requires exact absolute-``S:``
formula and solver paths.  The process is created suspended, assigned to a
hard-memory Job Object, and only then resumed.  Final artifacts and partials
are never overwritten.  A successful result is only an UNSAT candidate whose
published LRAT bytes still require independent reduction and replay.
"""

from __future__ import annotations

import argparse
import ctypes
import datetime as dt
import json
import os
import secrets
import subprocess
import threading
import time
from ctypes import wintypes
from pathlib import Path
from typing import BinaryIO, Callable

from . import cover6_d7_r34_leaf_registry as registry
from . import cover6_d7_r34_safety as safety
from . import materialize_cover6_d7_r34_leaf as leaf
from . import reduce_cover6_d7_r34_fgravegow_lrat_core as frozen_core
from . import run_cover6_d7_r34_fgravegow_lrat as frozen_runner


SOLVER_NAME = frozen_runner.SOLVER_NAME
SOLVER_VERSION = frozen_runner.SOLVER_VERSION
SOLVER_SHA256 = frozen_runner.SOLVER_SHA256
SOLVER_FLAGS = frozen_runner.SOLVER_FLAGS
CONFLICT_LIMIT = frozen_runner.CONFLICT_LIMIT
WALL_LIMIT_SECONDS = frozen_runner.WALL_LIMIT_SECONDS
RSS_LIMIT_MIB = frozen_runner.RSS_LIMIT_MIB
RSS_LIMIT_BYTES = frozen_runner.RSS_LIMIT_BYTES
PROOF_LIMIT_MIB = frozen_runner.PROOF_LIMIT_MIB
PROOF_LIMIT_BYTES = frozen_runner.PROOF_LIMIT_BYTES
LOG_LIMIT_MIB = frozen_runner.LOG_LIMIT_MIB
LOG_LIMIT_BYTES = frozen_runner.LOG_LIMIT_BYTES
JOBS = frozen_runner.JOBS
POLL_SECONDS = frozen_runner.POLL_SECONDS
PARTIAL_SUFFIX = frozen_runner.PARTIAL_SUFFIX

RunPaths = frozen_runner.RunPaths
MonitorResult = frozen_runner.MonitorResult
CombinedLogBudget = frozen_runner.CombinedLogBudget
WindowsJobObject = frozen_runner.WindowsJobObject
WindowsProcessMemory = frozen_runner.WindowsProcessMemory
WindowsReadLocks = safety.WindowsReadLocks
WindowsDirectoryGuard = safety.WindowsDirectoryGuard


class R34LeafLratRunnerError(RuntimeError):
    """Raised at the first runner policy, identity, or supervision failure."""


def require_absolute_s_path(path: Path, label: str) -> Path:
    try:
        return safety.require_absolute_s_no_parent(path, label)
    except safety.R34PathSafetyError as error:
        raise R34LeafLratRunnerError(str(error)) from error


def artifact_names(spec: registry.LeafSpec) -> dict[str, str]:
    stem = spec.artifact_stem
    return {
        "directory": f"{stem}.run",
        "proof": f"{stem}.lrat",
        "stdout": f"{stem}.cadical.stdout.log",
        "stderr": f"{stem}.cadical.stderr.log",
        "report": f"{stem}.lrat-run.json",
        "commit": f"{stem}.commit.json",
    }


def run_paths(
    directory: Path,
    spec: registry.LeafSpec,
    *,
    run_id: str | None = None,
) -> RunPaths:
    names = artifact_names(spec)
    if run_id is not None and (
        len(run_id) != 32 or any(character not in "0123456789abcdef" for character in run_id)
    ):
        raise R34LeafLratRunnerError("run id must be exactly 32 lowercase hexadecimal characters")
    run_directory = directory / (
        names["directory"] + (f".{run_id}" if run_id is not None else "")
    )
    formula = directory / spec.target_name
    proof = run_directory / names["proof"]
    stdout = run_directory / names["stdout"]
    stderr = run_directory / names["stderr"]
    report = run_directory / names["report"]
    return RunPaths(
        formula=formula,
        formula_partial=directory / f"{spec.target_name}{PARTIAL_SUFFIX}",
        proof=proof,
        proof_partial=run_directory / f"{proof.name}{PARTIAL_SUFFIX}",
        stdout=stdout,
        stdout_partial=run_directory / f"{stdout.name}{PARTIAL_SUFFIX}",
        stderr=stderr,
        stderr_partial=run_directory / f"{stderr.name}{PARTIAL_SUFFIX}",
        report=report,
        report_partial=run_directory / f"{report.name}{PARTIAL_SUFFIX}",
    )


def solver_command(solver: Path, paths: RunPaths) -> list[str]:
    return [
        str(solver),
        *SOLVER_FLAGS,
        "-c",
        str(CONFLICT_LIMIT),
        str(paths.formula),
        str(paths.proof_partial),
    ]


class _THREADENTRY32(ctypes.Structure):
    _fields_ = (
        ("dwSize", wintypes.DWORD),
        ("cntUsage", wintypes.DWORD),
        ("dwThreadID", wintypes.DWORD),
        ("dwOwnerProcessID", wintypes.DWORD),
        ("tpBasePri", wintypes.LONG),
        ("tpDeltaPri", wintypes.LONG),
        ("dwFlags", wintypes.DWORD),
    )


def resume_suspended_process(process: subprocess.Popen[bytes]) -> None:
    """Resume exactly one fresh primary thread after Job assignment."""

    if os.name != "nt":
        raise R34LeafLratRunnerError("suspended CaDiCaL launch requires Windows")
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateToolhelp32Snapshot.argtypes = (wintypes.DWORD, wintypes.DWORD)
    kernel32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
    kernel32.Thread32First.argtypes = (wintypes.HANDLE, ctypes.POINTER(_THREADENTRY32))
    kernel32.Thread32First.restype = wintypes.BOOL
    kernel32.Thread32Next.argtypes = (wintypes.HANDLE, ctypes.POINTER(_THREADENTRY32))
    kernel32.Thread32Next.restype = wintypes.BOOL
    kernel32.OpenThread.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
    kernel32.OpenThread.restype = wintypes.HANDLE
    kernel32.ResumeThread.argtypes = (wintypes.HANDLE,)
    kernel32.ResumeThread.restype = wintypes.DWORD
    kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
    kernel32.CloseHandle.restype = wintypes.BOOL
    snapshot = kernel32.CreateToolhelp32Snapshot(0x00000004, 0)
    invalid = ctypes.c_void_p(-1).value
    if int(snapshot) == invalid:
        raise ctypes.WinError(ctypes.get_last_error())
    resumed = 0
    try:
        entry = _THREADENTRY32()
        entry.dwSize = ctypes.sizeof(entry)
        present = kernel32.Thread32First(snapshot, ctypes.byref(entry))
        if not present:
            raise ctypes.WinError(ctypes.get_last_error())
        while present:
            if int(entry.dwOwnerProcessID) == process.pid:
                handle = kernel32.OpenThread(0x0002, False, entry.dwThreadID)
                if not handle:
                    raise ctypes.WinError(ctypes.get_last_error())
                try:
                    previous = kernel32.ResumeThread(handle)
                    if previous == 0xFFFFFFFF:
                        raise ctypes.WinError(ctypes.get_last_error())
                    if previous != 1:
                        raise R34LeafLratRunnerError(
                            "fresh CaDiCaL primary thread had suspension count "
                            f"{previous}, expected exactly 1"
                        )
                    resumed += 1
                finally:
                    kernel32.CloseHandle(handle)
            entry.dwSize = ctypes.sizeof(entry)
            present = kernel32.Thread32Next(snapshot, ctypes.byref(entry))
    finally:
        kernel32.CloseHandle(snapshot)
    if resumed != 1:
        raise R34LeafLratRunnerError(
            f"expected one suspended CaDiCaL primary thread, resumed {resumed}"
        )


def _terminate_and_wait(process: subprocess.Popen[bytes]) -> list[str]:
    errors: list[str] = []
    if process.poll() is None:
        try:
            process.kill()
        except BaseException as error:
            errors.append(f"process kill failed: {type(error).__name__}: {error}")
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        errors.append("process wait timed out after 10 seconds")
        try:
            process.kill()
            process.wait(timeout=10)
        except BaseException as error:
            errors.append(f"fallback termination failed: {type(error).__name__}: {error}")
    except BaseException as error:
        errors.append(f"process wait failed: {type(error).__name__}: {error}")
    return errors


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
    samples = 0
    monitor_error: str | None = None
    try:
        memory_context = WindowsProcessMemory(process.pid)
    except BaseException as error:
        _terminate_and_wait(process)
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
        while process.poll() is None:
            elapsed = time.perf_counter() - started
            proof_bytes = _proof_size(proof_partial)
            max_proof = max(max_proof, proof_bytes)
            try:
                _current, process_peak = memory.sample()
                peak_rss = max(peak_rss, process_peak)
                samples += 1
            except BaseException as error:
                stop_reason = "RSS_MONITOR_ERROR"
                monitor_error = f"{type(error).__name__}: {error}"
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
                termination_errors = _terminate_and_wait(process)
                if termination_errors:
                    monitor_error = "; ".join(
                        filter(None, (monitor_error, *termination_errors))
                    )
                break
            time.sleep(POLL_SECONDS)
        if process.poll() is not None:
            try:
                process.wait(timeout=10)
            except BaseException as error:
                stop_reason = stop_reason or "TERMINATION_ERROR"
                monitor_error = f"{type(error).__name__}: {error}"
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
        samples,
        monitor_error,
    )


def execute_supervised_process(
    command: list[str],
    directory: Path,
    environment: dict[str, str],
    paths: RunPaths,
    stdout_stream: BinaryIO,
    stderr_stream: BinaryIO,
    log_budget: CombinedLogBudget,
    *,
    popen_factory: Callable[..., subprocess.Popen[bytes]] = subprocess.Popen,
    job_factory: Callable[[int], object] = WindowsJobObject,
    resume_factory: Callable[[subprocess.Popen[bytes]], None] = resume_suspended_process,
    monitor_factory: Callable[[subprocess.Popen[bytes], Path, CombinedLogBudget], MonitorResult] = monitor_process,
) -> tuple[MonitorResult, str | None, bool]:
    """Launch suspended; factories make ordering/caps testable without a solver."""

    monitor = MonitorResult(None, "LAUNCH_ERROR", 0.0, 0, 0, 0, None)
    launch_error: str | None = None
    process: subprocess.Popen[bytes] | None = None
    job = None
    threads: list[threading.Thread] = []
    assigned = False
    try:
        job = job_factory(RSS_LIMIT_BYTES)
        process = popen_factory(
            command,
            cwd=directory,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            creationflags=(
                getattr(subprocess, "CREATE_NO_WINDOW", 0)
                | getattr(subprocess, "CREATE_SUSPENDED", 0x00000004)
            ),
        )
        job.assign(process)  # type: ignore[attr-defined]
        assigned = True
        resume_factory(process)
        if process.stdout is None or process.stderr is None:
            raise R34LeafLratRunnerError("CaDiCaL pipes were not created")
        threads = [
            threading.Thread(
                target=log_budget.copy,
                args=(process.stdout, stdout_stream),
                name="r34-leaf-cadical-stdout",
                daemon=True,
            ),
            threading.Thread(
                target=log_budget.copy,
                args=(process.stderr, stderr_stream),
                name="r34-leaf-cadical-stderr",
                daemon=True,
            ),
        ]
        for thread in threads:
            thread.start()
        monitor = monitor_factory(process, paths.proof_partial, log_budget)
    except BaseException as error:
        launch_error = f"{type(error).__name__}: {error}"
        if process is not None:
            termination_errors = _terminate_and_wait(process)
            if termination_errors:
                launch_error += "; " + "; ".join(termination_errors)
        monitor = MonitorResult(
            process.returncode if process is not None else None,
            "LAUNCH_OR_MONITOR_ERROR",
            monitor.wall_seconds,
            monitor.sampled_peak_rss_bytes,
            max(monitor.maximum_observed_proof_bytes, _proof_size(paths.proof_partial)),
            monitor.rss_sample_count,
            launch_error,
        )
    finally:
        try:
            for thread in threads:
                thread.join(timeout=10)
            if any(thread.is_alive() for thread in threads):
                if process is not None:
                    _terminate_and_wait(process)
                    for pipe in (process.stdout, process.stderr):
                        if pipe is not None:
                            pipe.close()
                for thread in threads:
                    thread.join(timeout=2)
                launch_error = "; ".join(
                    filter(None, (launch_error, "log capture thread did not terminate"))
                )
                monitor = MonitorResult(
                    monitor.returncode,
                    "LOG_CAPTURE_THREAD_TIMEOUT",
                    monitor.wall_seconds,
                    monitor.sampled_peak_rss_bytes,
                    monitor.maximum_observed_proof_bytes,
                    monitor.rss_sample_count,
                    launch_error,
                )
            if launch_error:
                accepted = log_budget.accepted_prefix(
                    ("runner supervision error: " + launch_error + "\n").encode(
                        "utf-8", "replace"
                    )
                )
                if accepted:
                    stderr_stream.write(accepted)
            stdout_stream.flush()
            stderr_stream.flush()
            os.fsync(stdout_stream.fileno())
            os.fsync(stderr_stream.fileno())
        finally:
            if job is not None:
                job.close()  # type: ignore[attr-defined]
    return monitor, launch_error, assigned


def preflight(slug: str = registry.FIRST_LEAF_SLUG) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    formula_preflight = leaf.preflight(slug)["targets"][0]
    placeholder = Path(r"S:\ABSOLUTE\RUN")
    paths = run_paths(placeholder, spec, run_id="0" * 32)
    command = solver_command(Path(r"S:\ABSOLUTE\cadical.exe"), paths)
    return {
        "status": "PREFLIGHT_ONLY_NO_S_NO_SOLVER_INVOKED",
        "formula": formula_preflight["target"],
        "selection": formula_preflight["selection"],
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
            "threshold_semantics": "every cap triggers at observed value >= limit",
            "windows_job_object": {
                "required": True,
                "process_memory_limit_mib": RSS_LIMIT_MIB,
                "kill_on_job_close": True,
                "launch_suspended_until_assignment": True,
            },
        },
        "outputs": artifact_names(spec) | {
            "directory_pattern": artifact_names(spec)["directory"] + ".<32-hex-run-id>",
            "file_partial_suffix": PARTIAL_SUFFIX,
        },
        "command_template": command,
        "path_policy": (
            "all paths are absolute S:, contain no '..', cross no reparse point; "
            "formula and solver remain read-locked against write/delete through publication"
        ),
        "overwrite_policy": (
            "each run uses a fresh unpredictable directory; failed directories are "
            "left quarantined; staged files are validated under locks, their direct "
            "parent guard and locks close for Windows renames, finals are re-locked "
            "and rehashed, and only then does one final atomic commit marker bind "
            "the complete report/log/proof set"
        ),
        "launch_policy": "only explicit run invokes CaDiCaL; preflight never reads S:",
        "formal_boundary": (
            "success captures an UNSAT candidate; CaDiCaL run-log markers do not "
            "causally bind the published LRAT bytes to the internal checkproof run; "
            "full-proof audit, core reduction, Lean replay, and S7 composition remain"
        ),
    }


def _identity_with_name(path: Path, final_name: str) -> dict[str, int | str]:
    metadata = frozen_runner.file_identity(path)
    metadata["name"] = final_name
    return metadata


OwnedFiles = dict[Path, safety.FileObjectIdentity]


def _claim_owned(
    path: Path,
    owned: OwnedFiles,
    identity: safety.FileObjectIdentity | None = None,
) -> None:
    if path in owned:
        raise R34LeafLratRunnerError(f"duplicate ownership claim: {path}")
    try:
        owned[path] = identity or safety.regular_file_object_identity(path)
    except (OSError, safety.R34PathSafetyError) as error:
        raise R34LeafLratRunnerError(f"cannot claim new regular file {path}: {error}") from error


def _require_owned(path: Path, owned: OwnedFiles) -> None:
    expected = owned.get(path)
    if expected is None:
        raise R34LeafLratRunnerError(f"refusing operation on unowned file: {path}")
    try:
        observed = safety.regular_file_object_identity(path)
    except (OSError, safety.R34PathSafetyError) as error:
        raise R34LeafLratRunnerError(f"owned file is unavailable or unsafe {path}: {error}") from error
    if observed != expected:
        raise R34LeafLratRunnerError(
            f"owned file object was replaced: {path}: {observed} != {expected}"
        )


def _rename_owned(partial: Path, final: Path, owned: OwnedFiles) -> None:
    _require_owned(partial, owned)
    if _lexists(final):
        raise FileExistsError(f"refusing to overwrite transaction artifact: {final}")
    identity = owned[partial]
    os.rename(partial, final)
    if safety.regular_file_object_identity(final) != identity:
        raise R34LeafLratRunnerError(f"file object changed across rename: {partial}")
    del owned[partial]
    owned[final] = identity


def _reserve_runner_partials(paths: RunPaths) -> OwnedFiles:
    owned: OwnedFiles = {}
    for path in (paths.proof_partial, paths.stdout_partial, paths.stderr_partial):
        with safety.create_new_exclusive_binary(path) as (stream, identity):
            _claim_owned(path, owned, identity)
            stream.flush()
            os.fsync(stream.fileno())
    return owned


def _write_report_partial(
    path: Path, report: dict[str, object], owned: OwnedFiles
) -> None:
    if _lexists(path):
        raise FileExistsError(f"refusing residual report partial: {path}")
    payload = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
    with safety.create_new_exclusive_binary(path) as (stream, identity):
        _claim_owned(path, owned, identity)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())


def _lexists(path: Path) -> bool:
    try:
        os.lstat(path)
    except FileNotFoundError:
        return False
    return True


def _verify_capture_artifacts_locked(
    paths: RunPaths,
    report: dict[str, object],
    *,
    partial: bool,
) -> dict[str, dict[str, int | str]]:
    """Rehash and reparse either the staged partials or published finals."""

    proof = paths.proof_partial if partial else paths.proof
    stdout = paths.stdout_partial if partial else paths.stdout
    stderr = paths.stderr_partial if partial else paths.stderr
    report_path = paths.report_partial if partial else paths.report
    artifacts = {
        paths.proof.name: _identity_with_name(proof, paths.proof.name),
        paths.stdout.name: _identity_with_name(stdout, paths.stdout.name),
        paths.stderr.name: _identity_with_name(stderr, paths.stderr.name),
        paths.report.name: _identity_with_name(report_path, paths.report.name),
    }
    if json.loads(report_path.read_text(encoding="utf-8")) != report:
        raise R34LeafLratRunnerError("captured report bytes differ from memory")
    logs = report.get("logs")
    result = report.get("result")
    if not isinstance(logs, dict) or not isinstance(result, dict):
        raise R34LeafLratRunnerError("captured report artifact tables are malformed")
    if logs.get("stdout") != artifacts[paths.stdout.name]:
        raise R34LeafLratRunnerError("captured stdout differs from report")
    if logs.get("stderr") != artifacts[paths.stderr.name]:
        raise R34LeafLratRunnerError("captured stderr differs from report")
    if result.get("lrat") != artifacts[paths.proof.name]:
        raise R34LeafLratRunnerError("captured proof differs from report")
    stdout_data = stdout.read_bytes()
    stderr_data = stderr.read_bytes()
    if frozen_runner.proof_check_markers(stdout_data, stderr_data) != result.get(
        "cadical_run_log_markers"
    ):
        raise R34LeafLratRunnerError("captured CaDiCaL run-log markers changed")
    if frozen_runner.parse_metrics(
        stdout_data.decode("utf-8", "replace")
    ) != result.get("metrics"):
        raise R34LeafLratRunnerError("captured solver metrics changed")
    return artifacts


def _commit_stage(
    directory: Path,
    spec: registry.LeafSpec,
    staged_paths: RunPaths,
    report: dict[str, object],
    owned: OwnedFiles,
) -> None:
    stage = staged_paths.report.parent
    commit = stage / artifact_names(spec)["commit"]
    commit_partial = commit.with_name(commit.name + PARTIAL_SUFFIX)
    expected_partials = {
        staged_paths.proof_partial,
        staged_paths.stdout_partial,
        staged_paths.stderr_partial,
        staged_paths.report_partial,
    }
    observed_entries = set(stage.iterdir())
    if observed_entries != expected_partials:
        raise R34LeafLratRunnerError(
            f"transaction stage entries changed: {observed_entries} != {expected_partials}"
        )
    for path in expected_partials:
        _require_owned(path, owned)
    # Validate every staged byte while denying writes/deletes.  Both the file
    # locks and the direct parent guard must close before Windows can rename a
    # child, so publication begins only after this context exits.
    with WindowsDirectoryGuard(stage), WindowsReadLocks(
        sorted(expected_partials, key=str)
    ):
        try:
            safety.reject_absolute_s_reparse(stage, "staged run directory")
            for path in expected_partials:
                safety.reject_absolute_s_reparse(path, f"staged output {path.name}")
        except safety.R34PathSafetyError as error:
            raise R34LeafLratRunnerError(str(error)) from error
        if set(stage.iterdir()) != expected_partials:
            raise R34LeafLratRunnerError("staged transaction inventory changed")
        staged_artifacts = _verify_capture_artifacts_locked(
            staged_paths, report, partial=True
        )
    # Report becomes visible first.  Proof/logs are never present without it,
    # and none of these names is accepted until the commit marker exists.
    publications = [(staged_paths.report_partial, staged_paths.report)]
    publications.extend(
        [
            (staged_paths.stdout_partial, staged_paths.stdout),
            (staged_paths.stderr_partial, staged_paths.stderr),
        ]
    )
    publications.append((staged_paths.proof_partial, staged_paths.proof))
    for partial, final in publications:
        _rename_owned(partial, final, owned)

    # The partial locks and direct parent guard are now closed.  A failure in
    # this sequence leaves a mixed-name quarantine without a commit marker.
    expected_finals = {
        staged_paths.proof,
        staged_paths.stdout,
        staged_paths.stderr,
        staged_paths.report,
    }
    for path in expected_finals:
        _require_owned(path, owned)
    with WindowsDirectoryGuard(stage), WindowsReadLocks(
        sorted(expected_finals, key=str)
    ):
        try:
            safety.reject_absolute_s_reparse(stage, "committed run directory")
            for path in expected_finals:
                safety.reject_absolute_s_reparse(path, f"run output {path.name}")
        except safety.R34PathSafetyError as error:
            raise R34LeafLratRunnerError(str(error)) from error
        if set(stage.iterdir()) != expected_finals:
            raise R34LeafLratRunnerError("finalized transaction directory is incomplete")
        artifacts = _verify_capture_artifacts_locked(
            staged_paths, report, partial=False
        )
        if artifacts != staged_artifacts:
            raise R34LeafLratRunnerError(
                "captured artifacts changed across Windows publication renames"
            )
        commit_payload = {
            "schema_version": 1,
            "status": "COMMITTED_UNSAT_CANDIDATE_CAPTURE",
            "artifact_directory": stage.name,
            "selection": leaf.selection_payload(spec),
            "artifacts": artifacts,
            "report": artifacts[staged_paths.report.name],
        }
        _write_report_partial(commit_partial, commit_payload, owned)
        if _lexists(commit):
            raise FileExistsError(f"commit marker appeared: {commit}")
        _require_owned(commit_partial, owned)
        with WindowsReadLocks([commit_partial]):
            try:
                safety.reject_absolute_s_reparse(
                    commit_partial, "run commit-marker partial"
                )
            except safety.R34PathSafetyError as error:
                raise R34LeafLratRunnerError(str(error)) from error
            if json.loads(commit_partial.read_text(encoding="utf-8")) != commit_payload:
                raise R34LeafLratRunnerError("run commit-marker partial changed")
            if set(stage.iterdir()) != expected_finals | {commit_partial}:
                raise R34LeafLratRunnerError("precommit run inventory changed")
            for path in expected_finals:
                if _identity_with_name(path, path.name) != artifacts[path.name]:
                    raise R34LeafLratRunnerError("run output changed before commit publication")
    if _lexists(commit):
        raise FileExistsError(f"commit marker appeared after validation: {commit}")
    # All direct-parent and file locks are closed.  Point of linearization and
    # final fallible filesystem operation; the reducer re-verifies every byte.
    os.rename(commit_partial, commit)


def _verify_committed_stage_locked(
    spec: registry.LeafSpec,
    paths: RunPaths,
    report: dict[str, object],
    owned: OwnedFiles,
) -> None:
    stage = paths.report.parent
    commit = stage / artifact_names(spec)["commit"]
    outputs = {paths.proof, paths.stdout, paths.stderr, paths.report}
    for path in outputs | {commit}:
        _require_owned(path, owned)
        try:
            safety.reject_absolute_s_reparse(path, f"locked committed output {path.name}")
        except safety.R34PathSafetyError as error:
            raise R34LeafLratRunnerError(str(error)) from error
    if set(stage.iterdir()) != outputs | {commit}:
        raise R34LeafLratRunnerError("committed run inventory changed before return")
    artifacts = {
        path.name: _identity_with_name(path, path.name)
        for path in sorted(outputs, key=str)
    }
    commit_payload = json.loads(commit.read_text(encoding="utf-8"))
    expected_commit = {
        "schema_version": 1,
        "status": "COMMITTED_UNSAT_CANDIDATE_CAPTURE",
        "artifact_directory": stage.name,
        "selection": leaf.selection_payload(spec),
        "artifacts": artifacts,
        "report": artifacts[paths.report.name],
    }
    if commit_payload != expected_commit:
        raise R34LeafLratRunnerError("committed run marker or artifacts changed")
    if json.loads(paths.report.read_text(encoding="utf-8")) != report:
        raise R34LeafLratRunnerError("committed report changed before return")
    logs = report.get("logs")
    if not isinstance(logs, dict):
        raise R34LeafLratRunnerError("committed report log table is malformed")
    for key, path in (("stdout", paths.stdout), ("stderr", paths.stderr)):
        if logs.get(key) != artifacts[path.name]:
            raise R34LeafLratRunnerError(f"committed {key} differs from report")
    result = report.get("result")
    if not isinstance(result, dict) or result.get("lrat") != artifacts[paths.proof.name]:
        raise R34LeafLratRunnerError("committed proof differs from report")
    stdout_data = paths.stdout.read_bytes()
    stderr_data = paths.stderr.read_bytes()
    if frozen_runner.proof_check_markers(stdout_data, stderr_data) != report["result"][
        "cadical_run_log_markers"
    ]:  # type: ignore[index]
        raise R34LeafLratRunnerError("committed CaDiCaL run-log markers changed")
    if frozen_runner.parse_metrics(
        stdout_data.decode("utf-8", "replace")
    ) != report["result"]["metrics"]:  # type: ignore[index]
        raise R34LeafLratRunnerError("committed solver metrics changed")


def _run_staged(
    spec: registry.LeafSpec,
    paths: RunPaths,
    directory: Path,
    solver: Path,
    observed_solver_hash: str,
    command: list[str],
    environment: dict[str, str],
    formula: dict[str, int | str],
    started_utc: str,
    owned: OwnedFiles,
) -> tuple[dict[str, object], bool]:
    budget = CombinedLogBudget(LOG_LIMIT_BYTES)
    with paths.stdout_partial.open("r+b") as stdout_stream:
        with paths.stderr_partial.open("r+b") as stderr_stream:
            monitor, launch_error, assigned = execute_supervised_process(
                command,
                directory,
                environment,
                paths,
                stdout_stream,
                stderr_stream,
                budget,
            )
    for path in (paths.proof_partial, paths.stdout_partial, paths.stderr_partial):
        _require_owned(path, owned)
    stdout_data = paths.stdout_partial.read_bytes()
    stderr_data = paths.stderr_partial.read_bytes()
    markers = frozen_runner.proof_check_markers(stdout_data, stderr_data)
    metrics = frozen_runner.parse_metrics(stdout_data.decode("utf-8", "replace"))
    stop_reason = monitor.stop_reason
    if stop_reason is None and budget.errors:
        stop_reason = "LOG_CAPTURE_ERROR"
    if stop_reason is None and budget.limit_reached.is_set():
        stop_reason = "LOG_BYTES_LIMIT"
    reported_rss = metrics["solver_reported_maximum_resident_mib"]
    if stop_reason is None and isinstance(reported_rss, float) and reported_rss >= RSS_LIMIT_MIB:
        stop_reason = "SOLVER_REPORTED_RSS_LIMIT"
    proof_bytes = _proof_size(paths.proof_partial)
    if stop_reason is None and proof_bytes >= PROOF_LIMIT_BYTES:
        stop_reason = "PROOF_SIZE_LIMIT"
    captured = len(stdout_data) + len(stderr_data)
    if stop_reason is None and captured >= LOG_LIMIT_BYTES:
        stop_reason = "LOG_BYTES_LIMIT"
    reported_lrat_bytes = metrics["solver_reported_lrat_bytes"]
    size_matches = isinstance(reported_lrat_bytes, int) and reported_lrat_bytes == proof_bytes
    base_capture = (
        stop_reason is None
        and monitor.returncode == 20
        and 0 < proof_bytes < PROOF_LIMIT_BYTES
        and size_matches
        and all(
            markers.get(name, False)
            for name in frozen_runner.REQUIRED_CHECKPROOF2_MARKERS
        )
    )
    capture_reason = "RUN_MARKERS_OR_PROOF_INCOMPLETE"
    if stop_reason is not None:
        capture_reason = stop_reason
    elif monitor.returncode != 20:
        capture_reason = f"SOLVER_EXIT_{monitor.returncode}"
    elif proof_bytes <= 0:
        capture_reason = "LRAT_MISSING_OR_EMPTY"
    elif proof_bytes >= PROOF_LIMIT_BYTES:
        capture_reason = "PROOF_SIZE_LIMIT"
    elif not size_matches:
        capture_reason = "LRAT_SIZE_DISAGREES_WITH_SOLVER_LOG"
    elif not all(
        markers.get(name, False)
        for name in frozen_runner.REQUIRED_CHECKPROOF2_MARKERS
    ):
        capture_reason = "CADICAL_RUN_MARKERS_INCOMPLETE"
    if base_capture:
        complete_metrics = (
            assigned
            and launch_error is None
            and monitor.monitor_error is None
            and 0 <= monitor.wall_seconds < WALL_LIMIT_SECONDS
            and monitor.rss_sample_count > 0
            and 0 <= monitor.sampled_peak_rss_bytes < RSS_LIMIT_BYTES
            and max(monitor.maximum_observed_proof_bytes, proof_bytes)
            < PROOF_LIMIT_BYTES
            and isinstance(metrics.get("lrat_added_clauses"), int)
            and int(metrics["lrat_added_clauses"]) > 0
            and isinstance(metrics.get("lrat_deleted_clauses"), int)
            and int(metrics["lrat_deleted_clauses"]) >= 0
            and isinstance(metrics.get("conflicts"), int)
            and 0 <= int(metrics["conflicts"]) <= CONFLICT_LIMIT
            and isinstance(reported_rss, (int, float))
            and 0 <= float(reported_rss) < RSS_LIMIT_MIB
        )
        if not complete_metrics:
            capture_reason = "CAPTURE_METRICS_OR_SUPERVISION_INCOMPLETE"
    else:
        complete_metrics = False
    success = base_capture and complete_metrics
    reason = "UNSAT_CANDIDATE_CAPTURED" if success else capture_reason
    proof_metadata: dict[str, int | str] | None = None
    discarded: dict[str, object] | None = None
    if success:
        proof_metadata = _identity_with_name(paths.proof_partial, paths.proof.name)
    else:
        discarded = {
            "name": paths.proof_partial.name,
            "bytes_before_removal": proof_bytes,
            "removed": False,
            "quarantined": True,
            "reason": "incomplete candidate remains only inside an uncommitted run directory",
        }
    stdout_meta = _identity_with_name(paths.stdout_partial, paths.stdout.name)
    stderr_meta = _identity_with_name(paths.stderr_partial, paths.stderr.name)
    report: dict[str, object] = {
        "schema_version": 1,
        "status": (
            "UNSAT_CANDIDATE_CAPTURED"
            if success else "INCONCLUSIVE_NO_LRAT_PUBLISHED"
        ),
        "started_utc": started_utc,
        "formula": formula,
        "selection": leaf.selection_payload(spec),
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
            "threshold_semantics": "each cap triggers at observed value >= limit",
            "windows_job_object": {
                "assigned": assigned,
                "process_memory_limit_bytes": RSS_LIMIT_BYTES,
                "kill_on_job_close": True,
                "launch_suspended_until_assignment": True,
            },
            "stop_reason": stop_reason,
            "wall_seconds": round(monitor.wall_seconds, 6),
            "sampled_peak_rss_bytes": monitor.sampled_peak_rss_bytes,
            "rss_sample_count": monitor.rss_sample_count,
            "maximum_observed_proof_bytes": max(
                monitor.maximum_observed_proof_bytes, proof_bytes
            ),
            "captured_combined_log_bytes": captured,
            "log_limit_reached": budget.limit_reached.is_set(),
            "monitor_error": monitor.monitor_error or launch_error,
        },
        "result": {
            "outcome_reason": reason,
            "cadical_run_log_markers": markers,
            "published_proof_bound_to_internal_checkproof": False,
            "independent_lrat_validation": "PENDING",
            "metrics": metrics,
            "proof_size_matches_solver_log": size_matches,
            "lrat_published": success,
            "lrat": proof_metadata,
            "discarded_partial_lrat": discarded,
        },
        "logs": {"stdout": stdout_meta, "stderr": stderr_meta},
        "published": {
            "artifact_directory": paths.report.parent.name,
            "proof": paths.proof.name if success else None,
            "stdout": paths.stdout.name if success else None,
            "stderr": paths.stderr.name if success else None,
            "report": paths.report.name if success else None,
            "commit": artifact_names(spec)["commit"] if success else None,
        },
        "quarantine": (
            None
            if success
            else {
                "artifact_directory": paths.report.parent.name,
                "commit_marker_present": False,
                "partials": [
                    paths.proof_partial.name,
                    paths.stdout_partial.name,
                    paths.stderr_partial.name,
                    paths.report_partial.name,
                ],
            }
        ),
        "formal_boundary": {
            "proof_level": "captured certificate candidate only",
            "published_byte_binding": (
                "the published LRAT bytes are not attested as the exact bytes "
                "processed by CaDiCaL's internal checkproof request"
            ),
            "missing": "independent full LRAT audit, Lean replay, and semantic S7 composition",
            "claim_forbidden": "no cover6-d7 theorem or Ramsey-number bound",
        },
        "threat_model": {
            "workspace": "controlled non-adversarial S: research directory",
            "concurrent_tampering": "out of scope; observed reparse or identity changes fail closed",
            "failed_run_policy": "leave the fresh run directory quarantined; never delete or overwrite it",
        },
    }
    _write_report_partial(paths.report_partial, report, owned)
    return report, success


def run(directory: Path, solver: Path, slug: str) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    preflight(slug)
    directory = require_absolute_s_path(directory, "runner directory")
    solver = require_absolute_s_path(solver, "CaDiCaL binary")
    if os.name != "nt":
        raise R34LeafLratRunnerError("the supervised S: runner requires Windows")
    try:
        safety.require_existing_directory(directory, "runner directory")
        safety.require_existing_regular_file(solver, "CaDiCaL binary")
    except safety.R34PathSafetyError as error:
        raise R34LeafLratRunnerError(str(error)) from error
    staged_paths = run_paths(directory, spec, run_id=secrets.token_hex(16))
    stage = staged_paths.report.parent
    for path, label in (
        (staged_paths.formula, "leaf formula"),
        (solver, "CaDiCaL binary"),
        (stage, "committed run directory"),
    ):
        try:
            safety.reject_absolute_s_reparse(path, label)
        except safety.R34PathSafetyError as error:
            raise R34LeafLratRunnerError(str(error)) from error
    if _lexists(staged_paths.formula_partial):
        raise FileExistsError(f"refusing residual formula partial: {staged_paths.formula_partial}")
    if _lexists(stage):
        raise FileExistsError("refusing existing committed run directory")
    try:
        safety.require_existing_regular_file(staged_paths.formula, "leaf formula")
    except safety.R34PathSafetyError as error:
        raise R34LeafLratRunnerError(str(error)) from error

    owned: OwnedFiles = {}
    committed = False
    try:
        with WindowsDirectoryGuard(directory), WindowsDirectoryGuard(
            solver.parent
        ), WindowsReadLocks([staged_paths.formula, solver]):
            # Recheck the path chain only after immutable read handles exist.
            try:
                safety.require_existing_directory(directory, "runner directory")
                safety.require_existing_directory(
                    solver.parent, "guarded CaDiCaL parent directory"
                )
                safety.require_existing_regular_file(staged_paths.formula, "leaf formula")
                safety.require_existing_regular_file(solver, "CaDiCaL binary")
            except safety.R34PathSafetyError as error:
                raise R34LeafLratRunnerError(str(error)) from error
            formula = leaf.inspect_stream(
                staged_paths.formula, leaf.target_identity(spec)
            )
            observed_solver_hash = frozen_runner.sha256_file(solver)
            if observed_solver_hash != SOLVER_SHA256:
                raise R34LeafLratRunnerError(
                    f"CaDiCaL binary SHA-256 mismatch: {observed_solver_hash}"
                )
            # A second prelaunch pass is intentional: no hash computed before
            # the read lock is accepted as the launch identity.
            if leaf.inspect_stream(
                staged_paths.formula, leaf.target_identity(spec)
            ) != formula or frozen_runner.sha256_file(solver) != observed_solver_hash:
                raise R34LeafLratRunnerError("formula or solver changed before launch")
            stage.mkdir(exist_ok=False)
            try:
                safety.require_existing_directory(stage, "new run directory")
            except safety.R34PathSafetyError as error:
                raise R34LeafLratRunnerError(str(error)) from error
            with WindowsDirectoryGuard(stage):
                try:
                    safety.require_existing_directory(stage, "guarded run directory")
                    owned = _reserve_runner_partials(staged_paths)
                    command = solver_command(solver, staged_paths)
                    environment = os.environ.copy()
                    environment["TEMP"] = str(stage)
                    environment["TMP"] = str(stage)
                    environment["PYTHONDWRITEBYTECODE"] = "1"
                    started = dt.datetime.now(dt.timezone.utc).isoformat()
                    report, success = _run_staged(
                        spec,
                        staged_paths,
                        directory,
                        solver,
                        observed_solver_hash,
                        command,
                        environment,
                        formula,
                        started,
                        owned,
                    )
                    if leaf.inspect_stream(
                        staged_paths.formula, leaf.target_identity(spec)
                    ) != formula or frozen_runner.sha256_file(solver) != observed_solver_hash:
                        raise R34LeafLratRunnerError("locked formula or solver identity changed")
                    if not success:
                        # A missing commit marker makes the fresh directory a
                        # quarantine.  Failure handling intentionally deletes nothing.
                        return report
                except BaseException:
                    # Preserve every partial/final byte in this uncommitted,
                    # unpredictable run directory for diagnosis or quarantine.
                    raise
            # The direct stage guard is intentionally closed before any child
            # rename; _commit_stage performs its own validate/close/publish/
            # reopen protocol and emits the commit marker last.
            _commit_stage(directory, spec, staged_paths, report, owned)
            return report
    finally:
        # No unlink/rmdir is permitted on failure.  The commit marker is the
        # sole distinction between an accepted capture and quarantined bytes.
        pass


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", default="preflight", choices=("preflight", "run"))
    parser.add_argument("--leaf", choices=registry.ACTIONABLE_SLUGS, default=registry.FIRST_LEAF_SLUG)
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--solver", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight(args.leaf)
    else:
        if args.directory is None or args.solver is None:
            parser.error("run requires --directory and --solver")
        result = run(args.directory, args.solver, args.leaf)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
