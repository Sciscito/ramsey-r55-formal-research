#!/usr/bin/env python3
"""Audit, reduce, verify, and optionally replay one pending R34 leaf LRAT.

The default preflight is local and reads neither ``S:`` nor a solver output.
All data commands require an explicit actionable leaf and absolute ``S:``
    paths.  The source LRAT identity is bound to the exact captured-candidate
    report, then the entire proof is independently indexed with forward hints rejected and RAT
syntax refused before backward dependency closure and dense-ID remapping.

Reduction publishes a new guarded output directory only when a final commit
marker binds its exact contents, and never overwrites an existing path.  Lean replay is an explicit later command using the
pinned direct Lean executable, a suspended launch, and a 1.5-GiB family Job
Object.  No SAT solver is invoked by this module.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import threading
import time
from array import array
from contextlib import nullcontext
from pathlib import Path, PureWindowsPath

from . import cover6_d7_r34_leaf_registry as registry
from . import cover6_d7_r34_safety as safety
from . import materialize_cover6_d7_r34_leaf as materializer
from . import reduce_cover6_d7_r34_fgravegow_lrat_core as frozen_core
from . import reduce_master8_lrat_core as corelib
from . import run_cover6_d7_r34_leaf_lrat as runner
from . import run_cover6_d7_r34_fgravegow_lrat as frozen_runner


SOURCE_VARIABLES = 66
SOURCE_CLAUSES = 4_312_440
MAX_CORE_CLAUSES = 50_000
MAX_CORE_CNF_BYTES = 32 * 1024 * 1024
MAX_CORE_LRAT_BYTES = 128 * 1024 * 1024
LEAN_WALL_LIMIT_SECONDS = 600.0
LEAN_JOB_MEMORY_LIMIT_BYTES = 1_536 * 1024 * 1024
LEAN_LOG_LIMIT_BYTES = 8 * 1024 * 1024
POLL_SECONDS = 0.05
PARTIAL_SUFFIX = ".partial"
MAPPING_NAME = "core_clause_map.tsv"
REDUCTION_NAME = "reduction.json"
REPLAY_NAME = "Replay.lean"
LEAN_LOG_NAME = "lean_replay.log"
MANIFEST_NAME = "MANIFEST.json"
CORE_COMMIT_NAME = "CORE_COMMIT.json"
REPLAY_DIRECTORY_NAME = "lean_replay.run"
REPLAY_COMMIT_NAME = "REPLAY_COMMIT.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

WindowsFamilyJob = frozen_core.WindowsFamilyJob
WindowsReadLocks = safety.WindowsReadLocks
WindowsDirectoryGuard = safety.WindowsDirectoryGuard
resume_suspended_process = frozen_core.resume_suspended_process
verify_replay_stack = frozen_core.verify_replay_stack
frozen_replay_files = frozen_core.frozen_replay_files
LEAN_EXE = frozen_core.LEAN_EXE
LEAN_EXE_SHA256 = frozen_core.LEAN_EXE_SHA256
LEAN_VERSION = frozen_core.LEAN_VERSION
LEAN_TOOLCHAIN_ROOT = frozen_core.LEAN_TOOLCHAIN_ROOT
LRAT_CATCHER = frozen_core.LRAT_CATCHER
LRAT_CATCHER_LEAN_PATH = frozen_core.LRAT_CATCHER_LEAN_PATH


class R34LeafCoreError(ValueError):
    """Raised at the first provenance, proof, cap, or replay mismatch."""


def sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb", buffering=1024 * 1024) as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
            size += len(block)
    return digest.hexdigest().upper(), size


def file_metadata(path: Path, *, lines: bool = False) -> dict[str, object]:
    digest = hashlib.sha256()
    size = 0
    line_count = 0
    with path.open("rb", buffering=1024 * 1024) as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
            size += len(block)
            line_count += block.count(b"\n")
    result: dict[str, object] = {
        "name": path.name,
        "bytes": size,
        "sha256": digest.hexdigest().upper(),
    }
    if lines:
        result["lines"] = line_count
    return result


def require_absolute_s(path: Path, label: str) -> Path:
    try:
        return safety.require_absolute_s_no_parent(path, label)
    except safety.R34PathSafetyError as error:
        raise R34LeafCoreError(str(error)) from error


def reject_reparse(path: Path, label: str) -> None:
    try:
        safety.reject_absolute_s_reparse(path, label)
    except BaseException as error:
        raise R34LeafCoreError(str(error)) from error


def paths_overlap(left: Path, right: Path) -> bool:
    """Return whether either normalized path contains the other."""

    left_text = os.path.normcase(os.path.abspath(os.fspath(left)))
    right_text = os.path.normcase(os.path.abspath(os.fspath(right)))
    try:
        common = os.path.commonpath((left_text, right_text))
    except ValueError:
        return False
    return common in (left_text, right_text)


def require_disjoint_source_output(source_dir: Path, output_dir: Path) -> None:
    if paths_overlap(source_dir, output_dir):
        raise R34LeafCoreError(
            "source and compact-core directories must be disjoint"
        )


def require_dedicated_empty_directory(
    directory: Path, protected: dict[str, Path]
) -> None:
    """Require a fresh-use directory disjoint from every protected tree.

    The caller still owns the physical-path/reparse checks.  This helper is
    deliberately path-root agnostic so the overlap and pollution policy can
    be exercised by local tests without touching ``S:``.
    """

    for label, path in protected.items():
        if paths_overlap(directory, path):
            raise R34LeafCoreError(
                f"temporary directory overlaps protected {label}: "
                f"{directory} <-> {path}"
            )
    if any(directory.iterdir()):
        raise R34LeafCoreError(
            f"temporary directory must be dedicated and empty: {directory}"
        )


def names(spec: registry.LeafSpec) -> dict[str, str]:
    run_names = runner.artifact_names(spec)
    base = spec.target_name.removesuffix(".cnf")
    return {
        "run_directory": run_names["directory"],
        "source_cnf": spec.target_name,
        "source_lrat": run_names["proof"],
        "source_stdout": run_names["stdout"],
        "source_stderr": run_names["stderr"],
        "source_report": run_names["report"],
        "source_commit": run_names["commit"],
        "core_cnf": f"{base}_core.cnf",
        "core_lrat": f"{base}_core.lrat",
        "mapping": MAPPING_NAME,
        "reduction": REDUCTION_NAME,
        "replay": REPLAY_NAME,
        "core_commit": CORE_COMMIT_NAME,
        "replay_directory": REPLAY_DIRECTORY_NAME,
        "lean_log": LEAN_LOG_NAME,
        "manifest": MANIFEST_NAME,
        "replay_commit": REPLAY_COMMIT_NAME,
    }


def _run_id_from_directory_name(name: str, spec: registry.LeafSpec) -> str:
    prefix = names(spec)["run_directory"] + "."
    if not name.startswith(prefix):
        raise R34LeafCoreError(f"runner directory lacks expected prefix: {name}")
    run_id = name[len(prefix) :]
    if len(run_id) != 32 or re.fullmatch(r"[0-9a-f]{32}", run_id) is None:
        raise R34LeafCoreError(f"runner directory lacks exact 128-bit suffix: {name}")
    return run_id


def discover_committed_run_directory(
    directory: Path, spec: registry.LeafSpec
) -> Path:
    """Select exactly one committed random run and ignore quarantined siblings."""

    commit_name = names(spec)["source_commit"]
    prefix = names(spec)["run_directory"] + "."
    committed: list[Path] = []
    for candidate in directory.iterdir():
        if not candidate.name.startswith(prefix):
            continue
        _run_id_from_directory_name(candidate.name, spec)
        try:
            safety.reject_reparse_between(candidate, directory, "candidate run directory")
        except safety.R34PathSafetyError as error:
            raise R34LeafCoreError(str(error)) from error
        if not candidate.is_dir():
            raise R34LeafCoreError(f"runner candidate is not a directory: {candidate}")
        if _lexists(candidate / commit_name):
            committed.append(candidate)
    if len(committed) != 1:
        raise R34LeafCoreError(
            "expected exactly one committed random runner directory, found "
            f"{len(committed)}"
        )
    return committed[0]


def source_paths(
    directory: Path,
    spec: registry.LeafSpec,
    *,
    run_directory: Path | None = None,
) -> dict[str, Path]:
    table = names(spec)
    run_directory = run_directory or discover_committed_run_directory(directory, spec)
    if run_directory.parent != directory:
        raise R34LeafCoreError("runner directory is not an immediate source child")
    _run_id_from_directory_name(run_directory.name, spec)
    return {
        "source_cnf": directory / table["source_cnf"],
        "source_lrat": run_directory / table["source_lrat"],
        "source_stdout": run_directory / table["source_stdout"],
        "source_stderr": run_directory / table["source_stderr"],
        "source_report": run_directory / table["source_report"],
        "source_commit": run_directory / table["source_commit"],
    }


def output_paths(directory: Path, spec: registry.LeafSpec) -> dict[str, Path]:
    table = names(spec)
    result = {
        key: directory / table[key]
        for key in ("core_cnf", "core_lrat", "mapping", "reduction", "replay", "core_commit")
    }
    replay_directory = directory / table["replay_directory"]
    result["replay_directory"] = replay_directory
    for key in ("lean_log", "manifest", "replay_commit"):
        result[key] = replay_directory / table[key]
    return result


def _json_field(value: object, *keys: str) -> object:
    current = value
    for key in keys:
        if not isinstance(current, dict):
            return None
        current = current.get(key)
    return current


def _valid_sha256(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9A-F]{64}", value) is not None


def validate_run_report_payload(
    report: dict[str, object],
    spec: registry.LeafSpec,
    source_dir: Path | None = None,
) -> dict[str, object]:
    """Validate every runner anchor before trusting its dynamic proof identity."""

    expected_selection = materializer.selection_payload(spec)
    expected_formula = {
        "name": spec.target_name,
        "bytes": spec.target_bytes,
        "sha256": spec.target_sha256,
        "lines": materializer.TARGET_LINES,
    }
    checks = (
        (report.get("schema_version"), 1, "schema"),
        (
            report.get("status"),
            "UNSAT_CANDIDATE_CAPTURED",
            "status",
        ),
        (_json_field(report, "solver", "name"), runner.SOLVER_NAME, "solver name"),
        (_json_field(report, "solver", "version"), runner.SOLVER_VERSION, "solver version"),
        (_json_field(report, "solver", "binary_sha256"), runner.SOLVER_SHA256, "solver hash"),
        (_json_field(report, "solver", "flags"), list(runner.SOLVER_FLAGS), "solver flags"),
        (_json_field(report, "solver", "conflict_limit"), runner.CONFLICT_LIMIT, "conflict cap"),
        (_json_field(report, "solver", "jobs"), 1, "jobs"),
        (_json_field(report, "solver", "returncode"), 20, "return code"),
        (_json_field(report, "supervision", "wall_limit_seconds"), runner.WALL_LIMIT_SECONDS, "wall cap"),
        (_json_field(report, "supervision", "rss_limit_bytes"), runner.RSS_LIMIT_BYTES, "RSS cap"),
        (_json_field(report, "supervision", "proof_limit_bytes"), runner.PROOF_LIMIT_BYTES, "proof cap"),
        (_json_field(report, "supervision", "combined_log_limit_bytes"), runner.LOG_LIMIT_BYTES, "log cap"),
        (_json_field(report, "supervision", "stop_reason"), None, "stop reason"),
        (_json_field(report, "supervision", "windows_job_object", "assigned"), True, "Job assignment"),
        (
            _json_field(
                report,
                "supervision",
                "windows_job_object",
                "process_memory_limit_bytes",
            ),
            runner.RSS_LIMIT_BYTES,
            "Job memory limit",
        ),
        (
            _json_field(report, "supervision", "windows_job_object", "kill_on_job_close"),
            True,
            "kill-on-close",
        ),
        (
            _json_field(report, "supervision", "windows_job_object", "launch_suspended_until_assignment"),
            True,
            "suspended launch",
        ),
        (
            _json_field(report, "result", "outcome_reason"),
            "UNSAT_CANDIDATE_CAPTURED",
            "outcome",
        ),
        (
            _json_field(
                report,
                "result",
                "published_proof_bound_to_internal_checkproof",
            ),
            False,
            "published-byte binding",
        ),
        (
            _json_field(report, "result", "independent_lrat_validation"),
            "PENDING",
            "independent LRAT validation state",
        ),
        (_json_field(report, "result", "proof_size_matches_solver_log"), True, "proof byte marker"),
        (_json_field(report, "result", "lrat_published"), True, "proof publication"),
        (_json_field(report, "result", "discarded_partial_lrat"), None, "discarded proof"),
        (report.get("quarantine"), None, "quarantine state"),
        (_json_field(report, "supervision", "log_limit_reached"), False, "log-limit flag"),
        (_json_field(report, "supervision", "monitor_error"), None, "monitor error"),
        (
            _json_field(report, "supervision", "threshold_semantics"),
            "each cap triggers at observed value >= limit",
            "threshold semantics",
        ),
    )
    for observed, expected, label in checks:
        if observed != expected:
            raise R34LeafCoreError(
                f"runner report {label} mismatch: {observed!r} != {expected!r}"
            )
    if report.get("selection") != expected_selection:
        raise R34LeafCoreError("runner report leaf selection changed")
    published = report.get("published")
    if not isinstance(published, dict):
        raise R34LeafCoreError("runner published-name table is malformed")
    artifact_directory = published.get("artifact_directory")
    if not isinstance(artifact_directory, str):
        raise R34LeafCoreError("runner artifact-directory name is malformed")
    run_id = _run_id_from_directory_name(artifact_directory, spec)
    expected_published = {
        "artifact_directory": artifact_directory,
        "proof": runner.artifact_names(spec)["proof"],
        "stdout": runner.artifact_names(spec)["stdout"],
        "stderr": runner.artifact_names(spec)["stderr"],
        "report": runner.artifact_names(spec)["report"],
        "commit": runner.artifact_names(spec)["commit"],
    }
    if published != expected_published:
        raise R34LeafCoreError("runner published-name table changed")
    expected_threat_model = {
        "workspace": "controlled non-adversarial S: research directory",
        "concurrent_tampering": "out of scope; observed reparse or identity changes fail closed",
        "failed_run_policy": "leave the fresh run directory quarantined; never delete or overwrite it",
    }
    if report.get("threat_model") != expected_threat_model:
        raise R34LeafCoreError("runner threat-model declaration changed")
    expected_formal_boundary = {
        "proof_level": "captured certificate candidate only",
        "published_byte_binding": (
            "the published LRAT bytes are not attested as the exact bytes "
            "processed by CaDiCaL's internal checkproof request"
        ),
        "missing": "independent full LRAT audit, Lean replay, and semantic S7 composition",
        "claim_forbidden": "no cover6-d7 theorem or Ramsey-number bound",
    }
    if report.get("formal_boundary") != expected_formal_boundary:
        raise R34LeafCoreError("runner formal-boundary declaration changed")

    solver_table = report.get("solver")
    if not isinstance(solver_table, dict):
        raise R34LeafCoreError("runner solver table is malformed")
    solver_path_value = solver_table.get("path")
    if not isinstance(solver_path_value, str):
        raise R34LeafCoreError("runner solver path is malformed")
    try:
        safety.require_absolute_s_no_parent(Path(solver_path_value), "reported solver")
    except safety.R34PathSafetyError as error:
        raise R34LeafCoreError(str(error)) from error
    command = solver_table.get("command")
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        raise R34LeafCoreError("runner command is malformed")
    if source_dir is not None:
        discovered = discover_committed_run_directory(source_dir, spec)
        if discovered.name != artifact_directory:
            raise R34LeafCoreError(
                "runner report artifact directory differs from committed directory"
            )
        expected_paths = runner.run_paths(source_dir, spec, run_id=run_id)
        expected_command = runner.solver_command(Path(solver_path_value), expected_paths)
    else:
        if len(command) < 2:
            raise R34LeafCoreError("runner command is too short")
        formula_arg = PureWindowsPath(command[-2])
        proof_arg = PureWindowsPath(command[-1])
        if formula_arg.name != spec.target_name:
            raise R34LeafCoreError("runner command formula name changed")
        expected_proof = runner.artifact_names(spec)["proof"] + runner.PARTIAL_SUFFIX
        if proof_arg.name != expected_proof:
            raise R34LeafCoreError("runner command proof partial name changed")
        if proof_arg.parent.name != artifact_directory:
            raise R34LeafCoreError("runner command artifact directory changed")
        expected_command = [
            solver_path_value,
            *runner.SOLVER_FLAGS,
            "-c",
            str(runner.CONFLICT_LIMIT),
            command[-2],
            command[-1],
        ]
    if command != expected_command:
        raise R34LeafCoreError("runner command/flag order differs from the frozen template")
    formula = report.get("formula")
    if not isinstance(formula, dict):
        raise R34LeafCoreError("runner report formula is malformed")
    for key, expected in expected_formula.items():
        if formula.get(key) != expected:
            raise R34LeafCoreError(f"runner report formula {key} changed")
    markers = _json_field(report, "result", "cadical_run_log_markers")
    if not isinstance(markers, dict) or not all(
        markers.get(name, False)
        for name in frozen_runner.REQUIRED_CHECKPROOF2_MARKERS
    ):
        raise R34LeafCoreError("runner report does not retain the required run-log markers")
    proof = _json_field(report, "result", "lrat")
    if not isinstance(proof, dict):
        raise R34LeafCoreError("runner report proof metadata is malformed")
    proof_bytes = proof.get("bytes")
    if proof.get("name") != names(spec)["source_lrat"]:
        raise R34LeafCoreError("runner report proof name changed")
    if not isinstance(proof_bytes, int) or not 0 < proof_bytes < runner.PROOF_LIMIT_BYTES:
        raise R34LeafCoreError("runner report proof bytes violate the strict cap")
    if not _valid_sha256(proof.get("sha256")):
        raise R34LeafCoreError("runner report proof SHA-256 is malformed")
    supervision = report["supervision"]
    assert isinstance(supervision, dict)
    wall_seconds = supervision.get("wall_seconds")
    if (
        not isinstance(wall_seconds, (int, float))
        or wall_seconds < 0
        or wall_seconds >= runner.WALL_LIMIT_SECONDS
    ):
        raise R34LeafCoreError("runner wall time violates the strict cap")
    samples = supervision.get("rss_sample_count")
    if not isinstance(samples, int) or samples <= 0:
        raise R34LeafCoreError("runner report has no positive RSS sample count")
    for key, limit in (
        ("sampled_peak_rss_bytes", runner.RSS_LIMIT_BYTES),
        ("maximum_observed_proof_bytes", runner.PROOF_LIMIT_BYTES),
        ("captured_combined_log_bytes", runner.LOG_LIMIT_BYTES),
    ):
        observed = supervision.get(key)
        if not isinstance(observed, (int, float)) or observed < 0 or observed >= limit:
            raise R34LeafCoreError(f"runner report {key} violates strict cap")
    if supervision.get("maximum_observed_proof_bytes", -1) < proof_bytes:
        raise R34LeafCoreError("runner maximum observed proof bytes is below final proof size")
    metrics = _json_field(report, "result", "metrics")
    if not isinstance(metrics, dict):
        raise R34LeafCoreError("runner metrics are malformed")
    additions = metrics.get("lrat_added_clauses")
    deletions = metrics.get("lrat_deleted_clauses")
    reported_bytes = metrics.get("solver_reported_lrat_bytes")
    if not isinstance(additions, int) or additions <= 0:
        raise R34LeafCoreError("runner report lacks positive LRAT addition count")
    if not isinstance(deletions, int) or deletions < 0:
        raise R34LeafCoreError("runner report lacks LRAT deletion count")
    if reported_bytes != proof_bytes:
        raise R34LeafCoreError("runner proof bytes differ from solver metric")
    conflicts = metrics.get("conflicts")
    if not isinstance(conflicts, int) or not 0 <= conflicts <= runner.CONFLICT_LIMIT:
        raise R34LeafCoreError("runner conflict metric violates the configured cap")
    reported_rss = metrics.get("solver_reported_maximum_resident_mib")
    if (
        not isinstance(reported_rss, (int, float))
        or reported_rss < 0
        or reported_rss >= runner.RSS_LIMIT_MIB
    ):
        raise R34LeafCoreError("solver-reported RSS violates the strict cap")
    return {"proof": proof, "metrics": metrics}


def verify_run_commit(
    directory: Path, spec: registry.LeafSpec
) -> tuple[dict[str, object], dict[str, object]]:
    paths = source_paths(directory, spec)
    run_directory = paths["source_report"].parent
    expected = {
        paths["source_lrat"],
        paths["source_stdout"],
        paths["source_stderr"],
        paths["source_report"],
        paths["source_commit"],
    }
    if set(run_directory.iterdir()) != expected:
        raise R34LeafCoreError("runner transaction inventory is not exact")
    try:
        reject_reparse(run_directory, "runner transaction directory")
        for path in expected:
            reject_reparse(path, f"runner transaction artifact {path.name}")
    except R34LeafCoreError:
        raise
    commit = json.loads(paths["source_commit"].read_text(encoding="utf-8"))
    if not isinstance(commit, dict):
        raise R34LeafCoreError("runner commit marker is not a JSON object")
    expected_header = {
        "schema_version": 1,
        "status": "COMMITTED_UNSAT_CANDIDATE_CAPTURE",
        "artifact_directory": run_directory.name,
        "selection": materializer.selection_payload(spec),
    }
    for key, value in expected_header.items():
        if commit.get(key) != value:
            raise R34LeafCoreError(f"runner commit {key} changed")
    artifacts = commit.get("artifacts")
    artifact_paths = expected - {paths["source_commit"]}
    expected_names = {path.name for path in artifact_paths}
    if not isinstance(artifacts, dict) or set(artifacts) != expected_names:
        raise R34LeafCoreError("runner commit artifact table is not exact")
    for path in artifact_paths:
        if artifacts.get(path.name) != file_metadata(path):
            raise R34LeafCoreError(f"runner commit does not bind {path.name}")
    if commit.get("report") != artifacts.get(paths["source_report"].name):
        raise R34LeafCoreError("runner commit report anchor changed")
    return file_metadata(paths["source_commit"]), commit


def verify_run_report(
    directory: Path, spec: registry.LeafSpec
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    paths = source_paths(directory, spec)
    _commit_meta, commit = verify_run_commit(directory, spec)
    report_meta = file_metadata(paths["source_report"])
    if commit.get("report") != report_meta:
        raise R34LeafCoreError("runner report differs from committed report anchor")
    report = json.loads(paths["source_report"].read_text(encoding="utf-8"))
    if not isinstance(report, dict):
        raise R34LeafCoreError("runner report is not a JSON object")
    dynamic = validate_run_report_payload(report, spec, directory)
    proof_meta = file_metadata(paths["source_lrat"])
    expected_proof = dynamic["proof"]
    assert isinstance(expected_proof, dict)
    for field in ("name", "bytes", "sha256"):
        if proof_meta.get(field) != expected_proof.get(field):
            raise R34LeafCoreError(f"published LRAT {field} differs from runner report")
    logs = report.get("logs")
    if not isinstance(logs, dict):
        raise R34LeafCoreError("runner log table is malformed")
    for key in ("stdout", "stderr"):
        actual = file_metadata(paths[f"source_{key}"])
        claimed = logs.get(key)
        if not isinstance(claimed, dict):
            raise R34LeafCoreError(f"runner {key} log claim is malformed")
        for field in ("name", "bytes", "sha256"):
            if actual.get(field) != claimed.get(field):
                raise R34LeafCoreError(f"runner {key} log {field} changed")
    stdout_data = paths["source_stdout"].read_bytes()
    stderr_data = paths["source_stderr"].read_bytes()
    captured = _json_field(report, "supervision", "captured_combined_log_bytes")
    if captured != len(stdout_data) + len(stderr_data):
        raise R34LeafCoreError("captured log byte count differs from published logs")
    observed_markers = frozen_runner.proof_check_markers(stdout_data, stderr_data)
    claimed_markers = _json_field(report, "result", "cadical_run_log_markers")
    if observed_markers != claimed_markers:
        raise R34LeafCoreError("runner markers differ from independent log reparse")
    observed_metrics = frozen_runner.parse_metrics(
        stdout_data.decode("utf-8", "replace")
    )
    claimed_metrics = _json_field(report, "result", "metrics")
    if observed_metrics != claimed_metrics:
        raise R34LeafCoreError("runner metrics differ from independent stdout reparse")
    if observed_metrics.get("conflicts") is None:
        raise R34LeafCoreError("runner stdout lacks the conflict metric")
    return report_meta, dynamic, report


def _public_analysis(analysis: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in analysis.items() if not key.startswith("_")}


def _source_identity(paths: dict[str, Path]) -> dict[str, dict[str, object]]:
    return {key: file_metadata(path) for key, path in paths.items()}


def _analyze_locked(directory: Path, spec: registry.LeafSpec) -> dict[str, object]:
    paths = source_paths(directory, spec)
    before = _source_identity(paths)
    report_meta, dynamic, _report = verify_run_report(directory, spec)
    materializer.inspect_stream(
        paths["source_cnf"], materializer.target_identity(spec)
    )
    analysis = corelib.analyze(
        paths["source_cnf"], paths["source_lrat"], master_identity=False
    )
    public = _public_analysis(analysis)
    source = public.get("input")
    proof = public.get("proof")
    if not isinstance(source, dict) or not isinstance(proof, dict):
        raise R34LeafCoreError("full proof analysis is malformed")
    if (source.get("variables"), source.get("initial_clauses")) != (
        SOURCE_VARIABLES,
        SOURCE_CLAUSES,
    ):
        raise R34LeafCoreError("source DIMACS dimensions changed")
    expected_cnf = {"bytes": spec.target_bytes, "sha256": spec.target_sha256}
    if source.get("cnf") != expected_cnf:
        raise R34LeafCoreError("source CNF identity changed during proof audit")
    expected_proof = dynamic["proof"]
    assert isinstance(expected_proof, dict)
    if source.get("lrat") != {
        "bytes": expected_proof["bytes"],
        "sha256": expected_proof["sha256"],
    }:
        raise R34LeafCoreError("source LRAT identity changed during proof audit")
    metrics = dynamic["metrics"]
    assert isinstance(metrics, dict)
    if proof.get("additions") != metrics.get("lrat_added_clauses"):
        raise R34LeafCoreError("full LRAT addition count differs from solver metric")
    if proof.get("deleted_identifiers") != metrics.get("lrat_deleted_clauses"):
        raise R34LeafCoreError("full LRAT deleted-ID count differs from solver metric")
    if proof.get("rat_additions") != 0 or proof.get("rup_additions") != proof.get("additions"):
        raise corelib.RatReductionUnsupported(
            "parameterized reduction requires every addition to use RUP hint syntax"
        )
    after = _source_identity(paths)
    if after != before:
        raise R34LeafCoreError("source artifacts changed during full proof audit")
    public.update(
        {
            "status": "PASS_EXACT_PARAMETERIZED_R34_ALL_RUP_BACKWARD_CORE_ANALYSIS",
            "selection": materializer.selection_payload(spec),
            "source_run_report": report_meta,
            "source_artifacts": before,
            "audit": {
                "all_additions_rup_syntax": True,
                "rat_additions": 0,
                "forward_hints_rejected_during_indexing": True,
                "backward_closure_from_unique_final_empty_clause": True,
                "semantic_rup_replay_still_required": True,
            },
            "caps": {
                "core_clauses_max": MAX_CORE_CLAUSES,
                "core_cnf_bytes_max": MAX_CORE_CNF_BYTES,
                "core_lrat_bytes_max": MAX_CORE_LRAT_BYTES,
            },
            "_index": analysis["_index"],
            "_core": analysis["_core"],
        }
    )
    return public


def analyze_exact(directory: Path, slug: str) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    directory = require_absolute_s(directory, "source directory")
    try:
        safety.require_existing_directory(directory, "source directory")
    except safety.R34PathSafetyError as error:
        raise R34LeafCoreError(str(error)) from error
    paths = source_paths(directory, spec)
    for key, path in paths.items():
        reject_reparse(path, key)
    run_directory = paths["source_report"].parent
    with WindowsDirectoryGuard(run_directory):
        with WindowsReadLocks(list(paths.values())):
            return _analyze_locked(directory, spec)


def validate_compact_caps(
    clauses: int, cnf_bytes: int, lrat_bytes: int
) -> dict[str, object]:
    observed = {"clauses": clauses, "cnf_bytes": cnf_bytes, "lrat_bytes": lrat_bytes}
    limits = {
        "clauses": MAX_CORE_CLAUSES,
        "cnf_bytes": MAX_CORE_CNF_BYTES,
        "lrat_bytes": MAX_CORE_LRAT_BYTES,
    }
    for key, value in observed.items():
        if not isinstance(value, int) or value < 0 or value > limits[key]:
            raise R34LeafCoreError(
                f"compact core {key} cap exceeded: {value} > {limits[key]}"
            )
    return {"status": "PASS_COMPACT_CORE_CAPS", "observed": observed, "limits": limits}


def mapping_label(spec: registry.LeafSpec) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", spec.slug).lower() + "_clause_id"


def lean_identifiers(spec: registry.LeafSpec) -> tuple[str, str, str]:
    safe = re.sub(r"[^A-Za-z0-9]", "", spec.slug)
    lower = re.sub(r"[^a-z0-9_]", "_", spec.slug.lower())
    namespace = f"LRATCatcher.Tests.Cover6D7R34{safe}CoreReplay"
    theorem = f"cover6_d7_r34_{lower}_core_unsat"
    return namespace, theorem, f"{namespace}.{theorem}"


def lean_source(spec: registry.LeafSpec, cnf: Path, lrat: Path) -> bytes:
    namespace, theorem, _qualified = lean_identifiers(spec)
    cnf_text = cnf.as_posix().replace('"', '\\"')
    lrat_text = lrat.as_posix().replace('"', '\\"')
    return (
        "import LRATCatcher.Reflect\n\n"
        f"namespace {namespace}\n\n"
        "-- Exact frozen-DIMACS leaf core; semantic S7 composition is separate.\n"
        f"lrat_reflect {theorem}\n"
        f"  \"{cnf_text}\"\n"
        f"  \"{lrat_text}\"\n\n"
        f"#print axioms {theorem}\n\n"
        f"end {namespace}\n"
    ).encode("utf-8")


def _core_linkage(
    analysis: dict[str, object],
    reduced: dict[str, object],
    mapping: dict[str, object],
    caps: dict[str, object],
) -> None:
    source_core = analysis.get("core")
    reduced_input = reduced.get("input")
    reduced_proof = reduced.get("proof")
    reduced_core = reduced.get("core")
    cap_observed = caps.get("observed")
    if not all(
        isinstance(value, dict)
        for value in (source_core, reduced_input, reduced_proof, reduced_core, cap_observed)
    ):
        raise R34LeafCoreError("malformed dependency-core linkage metadata")
    checks = (
        (reduced_input.get("variables"), SOURCE_VARIABLES, "compact variables"),
        (reduced_input.get("initial_clauses"), source_core.get("initial_clauses"), "compact clauses"),
        (mapping.get("rows"), source_core.get("initial_clauses"), "mapping rows"),
        (mapping.get("master_variables"), SOURCE_VARIABLES, "mapping source variables"),
        (mapping.get("master_clauses"), SOURCE_CLAUSES, "mapping source clauses"),
        (mapping.get("core_variables"), SOURCE_VARIABLES, "mapping core variables"),
        (reduced_proof.get("additions"), source_core.get("derived_additions"), "compact additions"),
        (reduced_core.get("dependency_edges"), source_core.get("dependency_edges"), "dependency edges"),
        (reduced_proof.get("deletion_actions"), source_core.get("retained_deletion_actions"), "deletion actions"),
        (reduced_proof.get("deleted_identifiers"), source_core.get("retained_deleted_identifiers"), "deleted ids"),
        (cap_observed.get("clauses"), source_core.get("initial_clauses"), "cap clause count"),
    )
    for observed, expected, label in checks:
        if observed != expected:
            raise R34LeafCoreError(f"{label} mismatch: {observed!r} != {expected!r}")


OwnedFiles = dict[Path, safety.FileObjectIdentity]


def _claim_owned(
    path: Path,
    owned: OwnedFiles,
    identity: safety.FileObjectIdentity | None = None,
) -> None:
    if path in owned:
        raise R34LeafCoreError(f"duplicate ownership claim: {path}")
    try:
        owned[path] = identity or safety.regular_file_object_identity(path)
    except (OSError, safety.R34PathSafetyError) as error:
        raise R34LeafCoreError(f"cannot claim new regular file {path}: {error}") from error


def _require_owned(path: Path, owned: OwnedFiles) -> None:
    expected = owned.get(path)
    if expected is None:
        raise R34LeafCoreError(f"refusing operation on unowned file: {path}")
    try:
        observed = safety.regular_file_object_identity(path)
    except (OSError, safety.R34PathSafetyError) as error:
        raise R34LeafCoreError(f"owned file is unavailable or unsafe {path}: {error}") from error
    if observed != expected:
        raise R34LeafCoreError(
            f"owned file object was replaced: {path}: {observed} != {expected}"
        )


def _rename_owned(partial: Path, final: Path, owned: OwnedFiles) -> None:
    _require_owned(partial, owned)
    if _lexists(final):
        raise FileExistsError(f"refusing to overwrite output artifact: {final}")
    identity = owned[partial]
    os.rename(partial, final)
    if safety.regular_file_object_identity(final) != identity:
        raise R34LeafCoreError(f"file object changed across rename: {partial}")
    del owned[partial]
    owned[final] = identity


def _write_new(
    path: Path, payload: bytes, owned: OwnedFiles | None = None
) -> dict[str, object]:
    with safety.create_new_exclusive_binary(path) as (stream, identity):
        if owned is not None:
            _claim_owned(path, owned, identity)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    return {
        "name": path.name,
        "bytes": len(payload),
        "lines": payload.count(b"\n"),
        "sha256": hashlib.sha256(payload).hexdigest().upper(),
    }


def _lexists(path: Path) -> bool:
    try:
        os.lstat(path)
    except FileNotFoundError:
        return False
    return True


CORE_ARTIFACT_KEYS = ("core_cnf", "core_lrat", "mapping", "reduction", "replay")


def _core_artifacts(paths: dict[str, Path]) -> dict[str, dict[str, object]]:
    return {
        paths[key].name: file_metadata(paths[key], lines=True)
        for key in CORE_ARTIFACT_KEYS
    }


def _core_commit_payload(
    output_dir: Path, spec: registry.LeafSpec, paths: dict[str, Path]
) -> dict[str, object]:
    return {
        "schema_version": 1,
        "status": "COMMITTED_PARAMETERIZED_R34_COMPACT_CORE_CANDIDATE",
        "artifact_directory": output_dir.name,
        "selection": materializer.selection_payload(spec),
        "artifacts": _core_artifacts(paths),
    }


def verify_core_commit(
    output_dir: Path,
    spec: registry.LeafSpec,
    *,
    allow_replay_directory: bool,
) -> dict[str, object]:
    paths = output_paths(output_dir, spec)
    expected = {paths[key] for key in CORE_ARTIFACT_KEYS} | {paths["core_commit"]}
    observed = set(output_dir.iterdir())
    if allow_replay_directory and paths["replay_directory"] in observed:
        expected.add(paths["replay_directory"])
    if observed != expected:
        raise R34LeafCoreError("compact-core transaction inventory is not exact")
    for path in expected:
        reject_reparse(path, f"compact-core artifact {path.name}")
    commit = json.loads(paths["core_commit"].read_text(encoding="utf-8"))
    if not isinstance(commit, dict):
        raise R34LeafCoreError("compact-core commit marker is not a JSON object")
    expected_header = {
        "schema_version": 1,
        "status": "COMMITTED_PARAMETERIZED_R34_COMPACT_CORE_CANDIDATE",
        "artifact_directory": output_dir.name,
        "selection": materializer.selection_payload(spec),
    }
    for key, value in expected_header.items():
        if commit.get(key) != value:
            raise R34LeafCoreError(f"compact-core commit {key} changed")
    artifacts = commit.get("artifacts")
    actual = _core_artifacts(paths)
    if artifacts != actual:
        raise R34LeafCoreError("compact-core commit artifact table changed")
    if paths["replay_directory"] in observed:
        verify_replay_commit(output_dir, spec)
    return commit


def verify_replay_commit(
    output_dir: Path, spec: registry.LeafSpec
) -> dict[str, object]:
    paths = output_paths(output_dir, spec)
    replay_directory = paths["replay_directory"]
    expected = {paths[key] for key in ("lean_log", "manifest", "replay_commit")}
    if set(replay_directory.iterdir()) != expected:
        raise R34LeafCoreError("Lean replay transaction inventory is not exact")
    reject_reparse(replay_directory, "Lean replay transaction directory")
    for path in expected:
        reject_reparse(path, f"Lean replay artifact {path.name}")
    commit = json.loads(paths["replay_commit"].read_text(encoding="utf-8"))
    if not isinstance(commit, dict):
        raise R34LeafCoreError("Lean replay commit marker is not a JSON object")
    expected_header = {
        "schema_version": 1,
        "status": "COMMITTED_LEAN_REPLAY_PASS",
        "artifact_directory": replay_directory.name,
        "selection": materializer.selection_payload(spec),
    }
    for key, value in expected_header.items():
        if commit.get(key) != value:
            raise R34LeafCoreError(f"Lean replay commit {key} changed")
    actual = {
        paths[key].name: file_metadata(paths[key], lines=True)
        for key in ("lean_log", "manifest")
    }
    if commit.get("artifacts") != actual:
        raise R34LeafCoreError("Lean replay commit artifact table changed")
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    if not isinstance(manifest, dict) or manifest.get("status") != "LEAN_REPLAY_PASS":
        raise R34LeafCoreError("committed Lean manifest is not an exact replay PASS")
    if _json_field(manifest, "validation", "lean", "status") != "LEAN_LRAT_REPLAY_PASS":
        raise R34LeafCoreError("committed Lean manifest lacks the LRAT replay PASS anchor")
    post_identity = _json_field(manifest, "validation", "post_replay_identity")
    required_identity_flags = (
        "compact_artifacts_unchanged",
        "source_artifacts_unchanged",
        "lean_lratcatcher_stack_unchanged",
        "lean_log_matches_exclusive_capture",
        "temporary_directory_empty_after_replay",
    )
    if not isinstance(post_identity, dict) or any(
        post_identity.get(field) is not True for field in required_identity_flags
    ):
        raise R34LeafCoreError(
            "committed Lean manifest lacks exact post-replay identity anchors"
        )
    if _json_field(manifest, "validation", "lean", "axioms_allowed") is not True:
        raise R34LeafCoreError("committed Lean manifest lacks the axiom allowlist PASS")
    return commit


class _CappedHashingWriter(corelib.HashingWriter):
    def __init__(self, stream: object, limit: int, label: str) -> None:
        super().__init__(stream)  # type: ignore[arg-type]
        self.limit = limit
        self.label = label

    def write(self, payload: bytes) -> None:
        if self.bytes + len(payload) > self.limit:
            raise R34LeafCoreError(
                f"{self.label} streaming cap exceeded: {self.bytes + len(payload)} > {self.limit}"
            )
        super().write(payload)


def _write_core_cnf_owned(
    source: Path,
    target: Path,
    mapping_target: Path,
    dependency: corelib.DependencyCore,
    spec: registry.LeafSpec,
    owned: OwnedFiles,
) -> tuple[array, dict[str, object], dict[str, object]]:
    mapping = array("I", [0]) * (SOURCE_CLAUSES + 1)
    clause_number = kept = 0
    with source.open("rb", buffering=8 * 1024 * 1024) as inp:
        with safety.create_new_exclusive_binary(target) as (
            raw_out,
            target_identity,
        ):
            _claim_owned(target, owned, target_identity)
            with safety.create_new_exclusive_binary(mapping_target) as (
                raw_mapping,
                mapping_identity,
            ):
                _claim_owned(mapping_target, owned, mapping_identity)
                out = _CappedHashingWriter(raw_out, MAX_CORE_CNF_BYTES, "compact CNF")
                mapping_out = _CappedHashingWriter(
                    raw_mapping, MAX_CORE_CNF_BYTES, "compact mapping"
                )
                out.write(f"p cnf {SOURCE_VARIABLES} {dependency.initial_count}\n".encode("ascii"))
                mapping_out.write(corelib._mapping_header(mapping_label(spec)) + b"\n")
                header_seen = False
                for raw in inp:
                    stripped = raw.strip()
                    if not stripped or stripped.startswith(b"c"):
                        continue
                    if not header_seen:
                        expected = [
                            b"p",
                            b"cnf",
                            str(SOURCE_VARIABLES).encode(),
                            str(SOURCE_CLAUSES).encode(),
                        ]
                        if stripped.split() != expected:
                            raise R34LeafCoreError("DIMACS header changed during reduction")
                        header_seen = True
                        continue
                    clause_number += 1
                    canonical = corelib._canonical_clause(
                        raw, SOURCE_VARIABLES, clause_number
                    )
                    if dependency.initial_used[clause_number]:
                        kept += 1
                        mapping[clause_number] = kept
                        out.write(canonical)
                        clause_hash = hashlib.sha256(canonical).hexdigest().upper()
                        mapping_out.write(
                            f"{kept}\t{clause_number}\t{clause_hash}\n".encode("ascii")
                        )
                if not header_seen or clause_number != SOURCE_CLAUSES:
                    raise R34LeafCoreError("DIMACS clause count changed during reduction")
                if kept != dependency.initial_count:
                    raise R34LeafCoreError("not every selected initial clause was emitted")
                raw_out.flush()
                os.fsync(raw_out.fileno())
                raw_mapping.flush()
                os.fsync(raw_mapping.fileno())
                cnf_meta = out.metadata()
                mapping_meta = mapping_out.metadata()
    return (
        mapping,
        {"variables": SOURCE_VARIABLES, "clauses": kept, **cnf_meta},
        {"rows": kept, **mapping_meta},
    )


def _write_core_lrat_owned(
    source: Path,
    target: Path,
    index: corelib.ProofIndex,
    dependency: corelib.DependencyCore,
    initial_map: array,
    owned: OwnedFiles,
) -> dict[str, object]:
    if index.rat_additions:
        raise corelib.RatReductionUnsupported(
            "RAT additions are forbidden in the parameterized compact-core reducer"
        )
    derived_map = array("I", [0]) * index.additions
    additions = deletion_actions = deleted_ids = kept_additions = 0
    with source.open("rb", buffering=8 * 1024 * 1024) as inp:
        with safety.create_new_exclusive_binary(target) as (
            raw_out,
            target_identity,
        ):
            _claim_owned(target, owned, target_identity)
            out = _CappedHashingWriter(raw_out, MAX_CORE_LRAT_BYTES, "compact LRAT")
            for line_number, raw in enumerate(inp, 1):
                action = corelib.parse_lrat_line(raw, line_number)
                if action is None:
                    continue
                if isinstance(action, corelib.Addition):
                    position = action.clause_id - index.initial_id
                    if not 0 <= position < index.additions:
                        raise R34LeafCoreError("addition id changed during output pass")
                    additions += 1
                    if not dependency.derived_used[position]:
                        continue
                    kept_additions += 1
                    new_id = dependency.initial_count + kept_additions
                    mapped_hints = tuple(
                        corelib._map_id(
                            hint,
                            SOURCE_CLAUSES,
                            index,
                            initial_map,
                            derived_map,
                        )
                        for hint in action.rup_hints
                    )
                    derived_map[position] = new_id
                    out.write(corelib._addition_line(action, new_id, mapped_hints))
                else:
                    mapped: list[int] = []
                    for old_id in action.clause_ids:
                        selected = (
                            bool(dependency.initial_used[old_id])
                            if old_id <= SOURCE_CLAUSES
                            else (
                                index.initial_id <= old_id <= index.final_id
                                and bool(dependency.derived_used[old_id - index.initial_id])
                            )
                        )
                        if selected:
                            mapped.append(
                                corelib._map_id(
                                    old_id,
                                    SOURCE_CLAUSES,
                                    index,
                                    initial_map,
                                    derived_map,
                                )
                            )
                    if mapped:
                        deletion_actions += 1
                        deleted_ids += len(mapped)
                        out.write(
                            ("1 d " + " ".join(map(str, mapped)) + " 0\n").encode(
                                "ascii"
                            )
                        )
            if additions != index.additions or kept_additions != dependency.derived_count:
                raise R34LeafCoreError("not every selected proof addition was emitted")
            raw_out.flush()
            os.fsync(raw_out.fileno())
            metadata = out.metadata()
    return {
        "additions": kept_additions,
        "deletion_actions": deletion_actions,
        "deleted_identifiers": deleted_ids,
        **metadata,
    }


def reduce_exact(source_dir: Path, output_dir: Path, slug: str) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    source_dir = require_absolute_s(source_dir, "source directory")
    output_dir = require_absolute_s(output_dir, "output directory")
    require_disjoint_source_output(source_dir, output_dir)
    reject_reparse(output_dir, "output directory")
    if _lexists(output_dir):
        raise FileExistsError(f"refusing existing output directory: {output_dir}")
    try:
        safety.require_existing_directory(output_dir.parent, "output parent")
    except safety.R34PathSafetyError as error:
        raise R34LeafCoreError(str(error)) from error
    sources = source_paths(source_dir, spec)
    for key, path in sources.items():
        reject_reparse(path, key)
    paths = output_paths(output_dir, spec)
    commit_partial = paths["core_commit"].with_name(
        paths["core_commit"].name + PARTIAL_SUFFIX
    )
    owned: OwnedFiles = {}
    source_run_directory = sources["source_report"].parent
    with WindowsDirectoryGuard(source_run_directory), WindowsDirectoryGuard(
        output_dir.parent
    ):
        with WindowsReadLocks(list(sources.values())):
            try:
                safety.require_existing_directory(
                    source_run_directory, "guarded source run directory"
                )
                safety.require_existing_directory(
                    output_dir.parent, "guarded compact-core parent"
                )
            except safety.R34PathSafetyError as error:
                raise R34LeafCoreError(str(error)) from error
            analysis = _analyze_locked(source_dir, spec)
            index = analysis["_index"]
            dependency = analysis["_core"]
            if not isinstance(index, corelib.ProofIndex) or not isinstance(
                dependency, corelib.DependencyCore
            ):
                raise R34LeafCoreError("internal dependency analysis objects are malformed")
            if dependency.initial_count > MAX_CORE_CLAUSES:
                raise R34LeafCoreError("dependency core exceeds the 50k-clause cap")
            output_dir.mkdir(exist_ok=False)
            try:
                try:
                    safety.require_existing_directory(output_dir, "new compact-core directory")
                except safety.R34PathSafetyError as error:
                    raise R34LeafCoreError(str(error)) from error
                with WindowsDirectoryGuard(output_dir) as output_guard:
                    try:
                        initial_map, cnf_meta, mapping_meta = _write_core_cnf_owned(
                            sources["source_cnf"],
                            paths["core_cnf"],
                            paths["mapping"],
                            dependency,
                            spec,
                            owned,
                        )
                        lrat_meta = _write_core_lrat_owned(
                            sources["source_lrat"],
                            paths["core_lrat"],
                            index,
                            dependency,
                            initial_map,
                            owned,
                        )
                        caps = validate_compact_caps(
                            dependency.initial_count,
                            int(cnf_meta["bytes"]),
                            int(lrat_meta["bytes"]),
                        )
                        generated_keys = ("core_cnf", "core_lrat", "mapping")
                        for key in generated_keys:
                            _require_owned(paths[key], owned)
                        with WindowsReadLocks([paths[key] for key in generated_keys]):
                            reduced = corelib.verify_reduced_pair(
                                paths["core_cnf"], paths["core_lrat"]
                            )
                            mapping = corelib.verify_clause_mapping(
                                sources["source_cnf"],
                                paths["core_cnf"],
                                paths["mapping"],
                                source_clause_label=mapping_label(spec),
                            )
                            if mapping.get("status") != "PASS_EXACT_ORDERED_SUBSEQUENCE":
                                raise R34LeafCoreError("exact source-clause mapping failed")
                            _core_linkage(analysis, reduced, mapping, caps)
                            replay_meta = _write_new(
                                paths["replay"],
                                lean_source(
                                    spec, paths["core_cnf"], paths["core_lrat"]
                                ),
                                owned,
                            )
                            reduction: dict[str, object] = {
                                **_public_analysis(analysis),
                                "schema_version": 1,
                                "status": "CORE_CANDIDATE_REDUCED_PENDING_LEAN_REPLAY",
                                "generated_utc": dt.datetime.now(
                                    dt.timezone.utc
                                ).isoformat(),
                                "caps": caps,
                                "output": {
                                    "cnf": {"name": paths["core_cnf"].name, **cnf_meta},
                                    "lrat": {"name": paths["core_lrat"].name, **lrat_meta},
                                    "initial_clause_mapping": {
                                        "name": MAPPING_NAME,
                                        **mapping_meta,
                                    },
                                    "replay_module": replay_meta,
                                },
                                "validation": {
                                    "reduced_pair": _public_analysis(reduced),
                                    "initial_clause_mapping": mapping,
                                    "lean_replay": "PENDING",
                                },
                                "formal_boundary": (
                                    "exact selected DIMACS leaf only; Lean replay pending; "
                                    "no S7 transport, cover6-d7 theorem, global gluing, "
                                    "or Ramsey bound"
                                ),
                            }
                            _write_new(
                                paths["reduction"],
                                (
                                    json.dumps(reduction, indent=2, sort_keys=True)
                                    + "\n"
                                ).encode("utf-8"),
                                owned,
                            )
                            locked_output_keys = CORE_ARTIFACT_KEYS
                            for key in locked_output_keys:
                                _require_owned(paths[key], owned)
                            with WindowsReadLocks(
                                [paths[key] for key in locked_output_keys]
                            ):
                                expected_before_commit = {
                                    paths[key] for key in CORE_ARTIFACT_KEYS
                                }
                                if set(output_dir.iterdir()) != expected_before_commit:
                                    raise R34LeafCoreError(
                                        "compact-core precommit inventory changed"
                                    )
                                for path in expected_before_commit:
                                    reject_reparse(path, f"locked compact output {path.name}")
                                # Reparse every generated byte under immutable handles.
                                locked_reduced = corelib.verify_reduced_pair(
                                    paths["core_cnf"], paths["core_lrat"]
                                )
                                locked_mapping = corelib.verify_clause_mapping(
                                    sources["source_cnf"],
                                    paths["core_cnf"],
                                    paths["mapping"],
                                    source_clause_label=mapping_label(spec),
                                )
                                if locked_reduced != reduced or locked_mapping != mapping:
                                    raise R34LeafCoreError(
                                        "compact outputs changed before locked reparse"
                                    )
                                _core_linkage(
                                    analysis, locked_reduced, locked_mapping, caps
                                )
                                if paths["replay"].read_bytes() != lean_source(
                                    spec, paths["core_cnf"], paths["core_lrat"]
                                ):
                                    raise R34LeafCoreError("Replay.lean changed before commit")
                                decoded_reduction = json.loads(
                                    paths["reduction"].read_text(encoding="utf-8")
                                )
                                if decoded_reduction != reduction:
                                    raise R34LeafCoreError(
                                        "reduction report changed before commit"
                                    )
                                if _source_identity(sources) != analysis["source_artifacts"]:
                                    raise R34LeafCoreError(
                                        "source artifacts changed during reduction"
                                    )
                                commit_payload = _core_commit_payload(
                                    output_dir, spec, paths
                                )
                                _write_new(
                                    commit_partial,
                                    (
                                        json.dumps(
                                            commit_payload, indent=2, sort_keys=True
                                        )
                                        + "\n"
                                    ).encode("utf-8"),
                                    owned,
                                )
                                _require_owned(commit_partial, owned)
                                with WindowsReadLocks([commit_partial]):
                                    reject_reparse(
                                        commit_partial, "compact-core commit partial"
                                    )
                                    if json.loads(
                                        commit_partial.read_text(encoding="utf-8")
                                    ) != commit_payload:
                                        raise R34LeafCoreError(
                                            "compact-core commit partial changed"
                                        )
                                    if set(output_dir.iterdir()) != (
                                        expected_before_commit | {commit_partial}
                                    ):
                                        raise R34LeafCoreError(
                                            "compact-core final precommit inventory changed"
                                        )
                                    if _core_artifacts(paths) != commit_payload["artifacts"]:
                                        raise R34LeafCoreError(
                                            "compact outputs changed before commit publication"
                                        )
                                    if _source_identity(sources) != analysis["source_artifacts"]:
                                        raise R34LeafCoreError(
                                            "source artifacts changed before commit publication"
                                        )
                                if _lexists(paths["core_commit"]):
                                    raise FileExistsError(
                                        f"core commit marker appeared: {paths['core_commit']}"
                                    )
                                # The direct parent guard omits
                                # FILE_SHARE_DELETE and must close before its
                                # child marker can be renamed on Windows.
                                output_guard.close()
                                # Linearization point and last fallible filesystem
                                # operation.  Later verification replays every hash.
                                os.rename(commit_partial, paths["core_commit"])
                                return reduction
                    except BaseException:
                        # The fresh output directory remains an uncommitted
                        # quarantine.  Failure handling never deletes bytes.
                        raise
            except BaseException:
                raise


def _verify_core_locked(
    source_dir: Path,
    output_dir: Path,
    spec: registry.LeafSpec,
    *,
    replay_expected: bool,
) -> dict[str, object]:
    analysis = _analyze_locked(source_dir, spec)
    sources = source_paths(source_dir, spec)
    paths = output_paths(output_dir, spec)
    replay_present = paths["replay_directory"] in set(output_dir.iterdir())
    if replay_present != replay_expected:
        raise R34LeafCoreError("Lean replay directory presence changed under verification")
    verify_core_commit(
        output_dir, spec, allow_replay_directory=replay_expected
    )
    for key in (*CORE_ARTIFACT_KEYS, "core_commit"):
        path = paths[key]
        if path.name.endswith(PARTIAL_SUFFIX):
            raise R34LeafCoreError("unexpected partial output path")
    reduced = corelib.verify_reduced_pair(paths["core_cnf"], paths["core_lrat"])
    mapping = corelib.verify_clause_mapping(
        sources["source_cnf"],
        paths["core_cnf"],
        paths["mapping"],
        source_clause_label=mapping_label(spec),
    )
    _, clauses = corelib.read_cnf_header(paths["core_cnf"])
    caps = validate_compact_caps(
        clauses, paths["core_cnf"].stat().st_size, paths["core_lrat"].stat().st_size
    )
    expected_replay = lean_source(spec, paths["core_cnf"], paths["core_lrat"])
    if paths["replay"].read_bytes() != expected_replay:
        raise R34LeafCoreError("Replay.lean path or theorem payload changed")
    reduction = json.loads(paths["reduction"].read_text(encoding="utf-8"))
    if not isinstance(reduction, dict):
        raise R34LeafCoreError("reduction report is malformed")
    if reduction.get("status") != "CORE_CANDIDATE_REDUCED_PENDING_LEAN_REPLAY":
        raise R34LeafCoreError("reduction report status changed")
    expected_public = _public_analysis(analysis)
    for key in ("input", "proof", "core", "selection", "source_run_report", "source_artifacts", "audit"):
        if reduction.get(key) != expected_public.get(key):
            raise R34LeafCoreError(f"reduction report {key} differs from re-analysis")
    if reduction.get("caps") != caps:
        raise R34LeafCoreError("reduction report cap table changed")
    validation = reduction.get("validation")
    if not isinstance(validation, dict):
        raise R34LeafCoreError("reduction validation table is malformed")
    if validation.get("reduced_pair") != _public_analysis(reduced):
        raise R34LeafCoreError("reduction reduced-pair claim changed")
    if validation.get("initial_clause_mapping") != mapping:
        raise R34LeafCoreError("reduction mapping claim changed")
    if validation.get("lean_replay") != "PENDING":
        raise R34LeafCoreError("reduction must leave Lean replay pending")
    artifacts = {
        key: file_metadata(paths[key], lines=True) for key in CORE_ARTIFACT_KEYS
    }
    claims = reduction.get("output")
    if not isinstance(claims, dict):
        raise R34LeafCoreError("reduction output claims are malformed")
    for claim_key, artifact_key in (
        ("cnf", "core_cnf"),
        ("lrat", "core_lrat"),
        ("initial_clause_mapping", "mapping"),
        ("replay_module", "replay"),
    ):
        claim = claims.get(claim_key)
        if not isinstance(claim, dict):
            raise R34LeafCoreError(f"missing output claim {claim_key}")
        for field in ("name", "bytes", "lines", "sha256"):
            if claim.get(field) != artifacts[artifact_key].get(field):
                raise R34LeafCoreError(f"output claim {claim_key}.{field} changed")
    _core_linkage(analysis, reduced, mapping, caps)
    return {
        "status": (
            "LEAN_REPLAY_PASS"
            if replay_expected
            else "CORE_CANDIDATE_VERIFIED_PENDING_LEAN_REPLAY"
        ),
        "selection": materializer.selection_payload(spec),
        "source_analysis": expected_public,
        "reduced_pair": _public_analysis(reduced),
        "mapping": mapping,
        "caps": caps,
        "artifacts": artifacts,
    }


def verify_core(source_dir: Path, output_dir: Path, slug: str) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    source_dir = require_absolute_s(source_dir, "source directory")
    output_dir = require_absolute_s(output_dir, "output directory")
    require_disjoint_source_output(source_dir, output_dir)
    try:
        safety.require_existing_directory(source_dir, "source directory")
        safety.require_existing_directory(output_dir, "output directory")
    except safety.R34PathSafetyError as error:
        raise R34LeafCoreError(str(error)) from error
    sources = source_paths(source_dir, spec)
    outputs = output_paths(output_dir, spec)
    for key, path in sources.items():
        reject_reparse(path, key)
    for key in (*CORE_ARTIFACT_KEYS, "core_commit"):
        reject_reparse(outputs[key], key)
    base_locked = list(sources.values()) + [
        outputs[key] for key in (*CORE_ARTIFACT_KEYS, "core_commit")
    ]
    source_run_directory = sources["source_report"].parent
    with WindowsDirectoryGuard(source_run_directory):
        with WindowsDirectoryGuard(output_dir):
            try:
                safety.require_existing_directory(
                    source_run_directory, "guarded source run directory"
                )
                safety.require_existing_directory(
                    output_dir, "guarded compact-core directory"
                )
            except safety.R34PathSafetyError as error:
                raise R34LeafCoreError(str(error)) from error
            if _lexists(outputs["replay_directory"]):
                try:
                    safety.require_existing_directory(
                        outputs["replay_directory"], "Lean replay transaction directory"
                    )
                except safety.R34PathSafetyError as error:
                    raise R34LeafCoreError(str(error)) from error
                replay_locked = [
                    outputs[key] for key in ("lean_log", "manifest", "replay_commit")
                ]
                with WindowsDirectoryGuard(outputs["replay_directory"]):
                    with WindowsReadLocks(base_locked + replay_locked):
                        return _verify_core_locked(
                            source_dir,
                            output_dir,
                            spec,
                            replay_expected=True,
                        )
            with WindowsReadLocks(base_locked):
                return _verify_core_locked(
                    source_dir,
                    output_dir,
                    spec,
                    replay_expected=False,
                )


def parse_axioms(log_text: str, qualified_theorem: str) -> list[str]:
    match = re.search(
        rf"'{re.escape(qualified_theorem)}' depends on axioms: \[(.*?)\]",
        log_text,
        re.DOTALL,
    )
    if not match:
        return []
    return [item.strip() for item in match.group(1).split(",") if item.strip()]


def axioms_allowed(axioms: list[str], theorem: str) -> bool:
    native = re.compile(
        rf"{re.escape(theorem)}\._native\.native_decide\.ax_[0-9]+_[0-9]+"
    )
    return bool(axioms) and all(
        axiom in ALLOWED_AXIOMS or native.fullmatch(axiom) is not None
        for axiom in axioms
    )


def _lean_supervised_owned(
    replay_path: Path,
    log_partial: Path,
    *,
    temporary_directory: Path | None = None,
    owned: OwnedFiles | None = None,
) -> dict[str, object]:
    command = [str(LEAN_EXE), str(replay_path)]
    temporary_directory = temporary_directory or replay_path.parent
    windows_root = r"C:\Windows"
    system32 = str(Path(windows_root) / "System32")
    environment = {
        "SystemRoot": windows_root,
        "WINDIR": windows_root,
        "COMSPEC": str(Path(system32) / "cmd.exe"),
        "PATHEXT": ".COM;.EXE;.BAT;.CMD",
        "PATH": str(LEAN_TOOLCHAIN_ROOT / "bin") + os.pathsep + system32,
        "TEMP": str(temporary_directory),
        "TMP": str(temporary_directory),
        "LEAN_PATH": str(LRAT_CATCHER_LEAN_PATH),
        "LEAN_ABORT_ON_PANIC": "1",
    }
    budget = frozen_runner.CombinedLogBudget(LEAN_LOG_LIMIT_BYTES)
    started = time.perf_counter()
    stop_reason: str | None = None
    launch_error: str | None = None
    peak_memory = 0
    process: subprocess.Popen[bytes] | None = None
    job: WindowsFamilyJob | None = None
    thread: threading.Thread | None = None
    captured_log: dict[str, object]
    with safety.create_new_exclusive_binary(log_partial) as (
        log_stream,
        log_identity,
    ):
        if owned is not None:
            _claim_owned(log_partial, owned, log_identity)
        try:
            job = WindowsFamilyJob(LEAN_JOB_MEMORY_LIMIT_BYTES)
            process = subprocess.Popen(
                command,
                cwd=LRAT_CATCHER,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                creationflags=(
                    getattr(subprocess, "CREATE_NO_WINDOW", 0)
                    | getattr(subprocess, "CREATE_SUSPENDED", 0x00000004)
                ),
            )
            job.assign(process)
            resume_suspended_process(process)
            if process.stdout is None:
                raise R34LeafCoreError("Lean stdout pipe was not created")
            thread = threading.Thread(
                target=budget.copy,
                args=(process.stdout, log_stream),
                name="r34-leaf-core-lean-log",
                daemon=True,
            )
            thread.start()
            while process.poll() is None:
                elapsed = time.perf_counter() - started
                peak_memory = max(peak_memory, job.peak_memory_bytes())
                if elapsed >= LEAN_WALL_LIMIT_SECONDS:
                    stop_reason = "WALL_LIMIT"
                elif peak_memory >= LEAN_JOB_MEMORY_LIMIT_BYTES:
                    stop_reason = "JOB_MEMORY_LIMIT"
                elif budget.limit_reached.is_set():
                    stop_reason = "LOG_BYTES_LIMIT"
                elif budget.errors:
                    stop_reason = "LOG_CAPTURE_ERROR"
                if stop_reason:
                    errors = frozen_core._terminate_and_wait(process, job)
                    if errors:
                        launch_error = "; ".join(errors)
                    break
                time.sleep(POLL_SECONDS)
            if process.poll() is None:
                errors = frozen_core._terminate_and_wait(process, job)
                if errors:
                    launch_error = "; ".join(errors)
                    stop_reason = stop_reason or "TERMINATION_ERROR"
            else:
                process.wait(timeout=10)
            peak_memory = max(peak_memory, job.peak_memory_bytes())
        except BaseException as error:
            launch_error = f"{type(error).__name__}: {error}"
            stop_reason = stop_reason or "LAUNCH_OR_MONITOR_ERROR"
            if process is not None:
                errors = frozen_core._terminate_and_wait(process, job)
                if errors:
                    launch_error += "; " + "; ".join(errors)
        finally:
            try:
                if thread is not None:
                    thread.join(timeout=10)
                if thread is not None and thread.is_alive():
                    stop_reason = "LOG_CAPTURE_THREAD_TIMEOUT"
                    if process is not None:
                        frozen_core._terminate_and_wait(process, job)
                        if process.stdout is not None:
                            process.stdout.close()
                    thread.join(timeout=5)
                    if thread.is_alive():
                        launch_error = "; ".join(
                            filter(None, (launch_error, "log thread remained alive"))
                        )
                if launch_error:
                    message = budget.accepted_prefix(
                        ("Lean supervision error: " + launch_error + "\n").encode(
                            "utf-8", "replace"
                        )
                    )
                    log_stream.write(message)
                log_stream.flush()
                os.fsync(log_stream.fileno())
            finally:
                if job is not None:
                    job.close()
        log_stream.seek(0)
        captured_bytes = log_stream.read()
        captured_log = {
            "bytes": len(captured_bytes),
            "lines": captured_bytes.count(b"\n"),
            "sha256": hashlib.sha256(captured_bytes).hexdigest().upper(),
        }
    elapsed = time.perf_counter() - started
    if stop_reason is None and elapsed >= LEAN_WALL_LIMIT_SECONDS:
        stop_reason = "WALL_LIMIT"
    if stop_reason is None and peak_memory >= LEAN_JOB_MEMORY_LIMIT_BYTES:
        stop_reason = "JOB_MEMORY_LIMIT"
    if stop_reason is None and budget.limit_reached.is_set():
        stop_reason = "LOG_BYTES_LIMIT"
    return {
        "command": command,
        "returncode": process.returncode if process is not None else None,
        "stop_reason": stop_reason,
        "wall_seconds": round(elapsed, 6),
        "peak_job_memory_bytes": peak_memory,
        "job_memory_limit_bytes": LEAN_JOB_MEMORY_LIMIT_BYTES,
        "wall_limit_seconds": LEAN_WALL_LIMIT_SECONDS,
        "log_limit_bytes": LEAN_LOG_LIMIT_BYTES,
        "job_object_assigned": bool(job is not None and job.assigned),
        "launch_suspended_until_job_assignment": True,
        "job_memory_scope": "Lean plus every descendant process",
        "kill_on_job_close": True,
        "environment_inherited": False,
        "launch_error": launch_error,
        "captured_log_under_exclusive_creator_handle": captured_log,
    }


def _lean_supervised(
    replay_path: Path, log_partial: Path, *, temporary_directory: Path | None = None
) -> dict[str, object]:
    """Supervise Lean and leave a failed fresh partial quarantined."""

    if _lexists(log_partial):
        raise FileExistsError(f"refusing residual Lean log partial: {log_partial}")
    owned: OwnedFiles = {}
    return _lean_supervised_owned(
        replay_path,
        log_partial,
        temporary_directory=temporary_directory,
        owned=owned,
    )


def _replay_lean_owned(
    source_dir: Path, output_dir: Path, slug: str, temporary_directory: Path
) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    source_dir = require_absolute_s(source_dir, "source directory")
    output_dir = require_absolute_s(output_dir, "output directory")
    temporary_directory = require_absolute_s(temporary_directory, "temporary directory")
    try:
        safety.require_existing_directory(temporary_directory, "temporary directory")
        safety.require_existing_directory(
            temporary_directory.parent, "temporary-directory parent"
        )
        safety.require_existing_directory(source_dir, "source directory")
        safety.require_existing_directory(output_dir, "output directory")
    except safety.R34PathSafetyError as error:
        raise R34LeafCoreError(str(error)) from error
    sources = source_paths(source_dir, spec)
    paths = output_paths(output_dir, spec)
    replay_directory = paths["replay_directory"]
    reject_reparse(replay_directory, "Lean replay transaction directory")
    if _lexists(replay_directory):
        raise FileExistsError(f"refusing existing replay transaction: {replay_directory}")
    log_partial = paths["lean_log"].with_name(
        paths["lean_log"].name + PARTIAL_SUFFIX
    )
    manifest_partial = paths["manifest"].with_name(
        paths["manifest"].name + PARTIAL_SUFFIX
    )
    commit_partial = paths["replay_commit"].with_name(
        paths["replay_commit"].name + PARTIAL_SUFFIX
    )
    core_lock_keys = (*CORE_ARTIFACT_KEYS, "core_commit")
    locked = (
        list(sources.values())
        + [paths[key] for key in core_lock_keys]
        + frozen_replay_files()
    )
    owned: OwnedFiles = {}
    source_run_directory = sources["source_report"].parent
    require_disjoint_source_output(source_dir, output_dir)
    protected_from_temp = {
        "source directory": source_dir,
        "source run directory": source_run_directory,
        "compact-core directory": output_dir,
        "Lean replay transaction": replay_directory,
        "Lean toolchain": LEAN_TOOLCHAIN_ROOT,
        "LRATCatcher worktree": LRAT_CATCHER,
        "LRATCatcher Lean path": LRAT_CATCHER_LEAN_PATH,
    }
    require_dedicated_empty_directory(temporary_directory, protected_from_temp)
    with (
        WindowsDirectoryGuard(source_dir),
        WindowsDirectoryGuard(source_run_directory),
        WindowsDirectoryGuard(output_dir),
        # Guard the parent, not TEMP itself: Lean/native_decide must be able to
        # rename and delete its own children on Windows.  The parent guard
        # still prevents replacing the dedicated TEMP directory object.
        WindowsDirectoryGuard(temporary_directory.parent),
    ):
                try:
                    safety.require_existing_directory(
                        source_dir, "guarded source directory"
                    )
                    safety.require_existing_directory(
                        source_run_directory, "guarded source run directory"
                    )
                    safety.require_existing_directory(
                        output_dir, "guarded compact-core directory"
                    )
                    safety.require_existing_directory(
                        temporary_directory, "guarded Lean temporary directory"
                    )
                except safety.R34PathSafetyError as error:
                    raise R34LeafCoreError(str(error)) from error
                require_dedicated_empty_directory(
                    temporary_directory, protected_from_temp
                )
                source_directory_inventory = set(source_dir.iterdir())
                source_run_inventory = set(source_run_directory.iterdir())
                with WindowsReadLocks(locked):
                    for key, path in {
                        **sources,
                        **{name: paths[name] for name in core_lock_keys},
                    }.items():
                        reject_reparse(path, f"locked replay input {key}")
                    verification = _verify_core_locked(
                        source_dir,
                        output_dir,
                        spec,
                        replay_expected=False,
                    )
                    stack_before = verify_replay_stack()
                    locked_sources = _source_identity(sources)
                    if (
                        locked_sources
                        != verification["source_analysis"]["source_artifacts"]
                    ):
                        raise R34LeafCoreError("source artifacts changed before replay")
                    artifacts_before = {
                        key: file_metadata(paths[key], lines=True)
                        for key in CORE_ARTIFACT_KEYS
                    }
                    if artifacts_before != verification["artifacts"]:
                        raise R34LeafCoreError("core artifacts changed before replay")
                    replay_directory.mkdir(exist_ok=False)
                    try:
                        try:
                            safety.require_existing_directory(
                                replay_directory, "new Lean replay directory"
                            )
                        except safety.R34PathSafetyError as error:
                            raise R34LeafCoreError(str(error)) from error
                        # The guarded output parent already prevents replacing
                        # the replay directory itself.  A direct guard on this
                        # directory would block every child publication rename
                        # on Windows because it omits FILE_SHARE_DELETE.
                        with nullcontext():
                            try:
                                supervision = _lean_supervised_owned(
                                    paths["replay"],
                                    log_partial,
                                    temporary_directory=temporary_directory,
                                    owned=owned,
                                )
                                captured_log = supervision.get(
                                    "captured_log_under_exclusive_creator_handle"
                                )
                                _require_owned(log_partial, owned)
                                with WindowsReadLocks([log_partial]):
                                    partial_log_meta = file_metadata(
                                        log_partial, lines=True
                                    )
                                    if captured_log != {
                                        key: partial_log_meta[key]
                                        for key in ("bytes", "lines", "sha256")
                                    }:
                                        raise R34LeafCoreError(
                                            "Lean log partial changed after exclusive capture"
                                        )
                                    if set(replay_directory.iterdir()) != {
                                        log_partial
                                    }:
                                        raise R34LeafCoreError(
                                            "Lean log partial inventory changed"
                                        )
                                _rename_owned(
                                    log_partial, paths["lean_log"], owned
                                )
                                with WindowsReadLocks([paths["lean_log"]]):
                                    log_meta = file_metadata(
                                        paths["lean_log"], lines=True
                                    )
                                    if log_meta != {
                                        **partial_log_meta,
                                        "name": paths["lean_log"].name,
                                    }:
                                        raise R34LeafCoreError(
                                            "Lean log changed across Windows publication rename"
                                        )
                                    if set(replay_directory.iterdir()) != {
                                        paths["lean_log"]
                                    }:
                                        raise R34LeafCoreError(
                                            "published Lean log inventory changed"
                                        )
                                    log_text = paths["lean_log"].read_text(
                                        encoding="utf-8", errors="replace"
                                    )
                                    namespace, theorem, qualified = lean_identifiers(
                                        spec
                                    )
                                    axioms = parse_axioms(log_text, qualified)
                                    artifacts_after = {
                                        key: file_metadata(paths[key], lines=True)
                                        for key in CORE_ARTIFACT_KEYS
                                    }
                                    locked_sources_after = _source_identity(sources)
                                    stack_after = verify_replay_stack()
                                    captured_log_unchanged = captured_log == {
                                        key: log_meta[key]
                                        for key in ("bytes", "lines", "sha256")
                                    }
                                    temporary_directory_empty_after_replay = not any(
                                        temporary_directory.iterdir()
                                    )
                                    strict_supervision = (
                                        supervision["stop_reason"] is None
                                        and supervision["returncode"] == 0
                                        and supervision["launch_error"] is None
                                        and supervision["job_object_assigned"] is True
                                        and supervision[
                                            "launch_suspended_until_job_assignment"
                                        ]
                                        is True
                                        and supervision["kill_on_job_close"] is True
                                        and supervision["environment_inherited"] is False
                                        and supervision["job_memory_limit_bytes"]
                                        == LEAN_JOB_MEMORY_LIMIT_BYTES
                                        and supervision["wall_limit_seconds"]
                                        == LEAN_WALL_LIMIT_SECONDS
                                        and supervision["log_limit_bytes"]
                                        == LEAN_LOG_LIMIT_BYTES
                                        and isinstance(
                                            supervision["wall_seconds"], (int, float)
                                        )
                                        and 0
                                        <= float(supervision["wall_seconds"])
                                        < LEAN_WALL_LIMIT_SECONDS
                                        and isinstance(
                                            supervision["peak_job_memory_bytes"], int
                                        )
                                        and 0
                                        <= int(supervision["peak_job_memory_bytes"])
                                        < LEAN_JOB_MEMORY_LIMIT_BYTES
                                        and int(log_meta["bytes"])
                                        < LEAN_LOG_LIMIT_BYTES
                                        and captured_log_unchanged
                                        and temporary_directory_empty_after_replay
                                    )
                                    success = (
                                        strict_supervision
                                        and qualified in log_text
                                        and "sorryAx" not in log_text
                                        and "declaration uses 'sorry'" not in log_text
                                        and axioms_allowed(axioms, theorem)
                                        and artifacts_after == artifacts_before
                                        and locked_sources_after == locked_sources
                                        and stack_after == stack_before
                                    )
                                    manifest: dict[str, object] = {
                                        "schema_version": 1,
                                        "status": (
                                            "LEAN_REPLAY_PASS"
                                            if success
                                            else "LEAN_REPLAY_FAILED"
                                        ),
                                        "selection": materializer.selection_payload(
                                            spec
                                        ),
                                        "source_analysis": verification[
                                            "source_analysis"
                                        ],
                                        "dependency_core": verification[
                                            "source_analysis"
                                        ]["core"],
                                        "caps": verification["caps"],
                                        "artifacts": artifacts_after
                                        | {"lean_log": log_meta},
                                        "validation": {
                                            "rup_syntax": "ALL_SOURCE_ADDITIONS_RUP_NO_RAT",
                                            "forward_hint_policy": "REJECTED_DURING_FULL_INDEX",
                                            "mapping": verification["mapping"],
                                            "reduced_pair": verification[
                                                "reduced_pair"
                                            ],
                                            "post_replay_identity": {
                                                "compact_artifacts_unchanged": artifacts_after
                                                == artifacts_before,
                                                "source_artifacts_unchanged": locked_sources_after
                                                == locked_sources,
                                                "lean_lratcatcher_stack_unchanged": stack_after
                                                == stack_before,
                                                "lean_log_matches_exclusive_capture": captured_log_unchanged,
                                                "temporary_directory_empty_after_replay": temporary_directory_empty_after_replay,
                                            },
                                            "lean": {
                                                "status": (
                                                    "LEAN_LRAT_REPLAY_PASS"
                                                    if success
                                                    else "LEAN_LRAT_REPLAY_FAILED"
                                                ),
                                                "namespace": namespace,
                                                "theorem": qualified,
                                                "axioms": axioms,
                                                "axioms_allowed": axioms_allowed(
                                                    axioms, theorem
                                                ),
                                                "observed_stack": stack_before,
                                                "supervision": supervision,
                                            },
                                        },
                                        "trust_boundary": (
                                            "Replay in the observed pinned Lean/LRATCatcher "
                                            "worktree; this is not an adversarially frozen "
                                            "closure of every transitive imported .olean or "
                                            "junction target."
                                        ),
                                        "formal_boundary": (
                                            "Lean proves UNSAT only for the exact selected "
                                            "compact DIMACS leaf; S7 transport and the "
                                            "cover6-d7/global theorem remain separate"
                                        ),
                                    }
                                    _write_new(
                                        manifest_partial,
                                        (
                                            json.dumps(
                                                manifest, indent=2, sort_keys=True
                                            )
                                            + "\n"
                                        ).encode("utf-8"),
                                        owned,
                                    )
                                    _require_owned(manifest_partial, owned)
                                    with WindowsReadLocks([manifest_partial]):
                                        if json.loads(
                                            manifest_partial.read_text(
                                                encoding="utf-8"
                                            )
                                        ) != manifest:
                                            raise R34LeafCoreError(
                                                "Lean replay manifest partial changed"
                                            )
                                        if set(replay_directory.iterdir()) != {
                                            paths["lean_log"],
                                            manifest_partial,
                                        }:
                                            raise R34LeafCoreError(
                                                "Lean manifest partial inventory changed"
                                            )
                                    if not success:
                                        # A failed replay is never committed or
                                        # promoted; its fresh directory is quarantine.
                                        return manifest
                                    _rename_owned(
                                        manifest_partial, paths["manifest"], owned
                                    )
                                    with WindowsReadLocks([paths["manifest"]]):
                                        if json.loads(
                                            paths["manifest"].read_text(
                                                encoding="utf-8"
                                            )
                                        ) != manifest:
                                            raise R34LeafCoreError(
                                                "Lean replay manifest changed"
                                            )
                                        if set(replay_directory.iterdir()) != {
                                            paths["lean_log"],
                                            paths["manifest"],
                                        }:
                                            raise R34LeafCoreError(
                                                "published Lean manifest inventory changed"
                                            )
                                        commit_payload = {
                                            "schema_version": 1,
                                            "status": "COMMITTED_LEAN_REPLAY_PASS",
                                            "artifact_directory": replay_directory.name,
                                            "selection": materializer.selection_payload(
                                                spec
                                            ),
                                            "artifacts": {
                                                paths[key].name: file_metadata(
                                                    paths[key], lines=True
                                                )
                                                for key in ("lean_log", "manifest")
                                            },
                                        }
                                        _write_new(
                                            commit_partial,
                                            (
                                                json.dumps(
                                                    commit_payload,
                                                    indent=2,
                                                    sort_keys=True,
                                                )
                                                + "\n"
                                            ).encode("utf-8"),
                                            owned,
                                        )
                                        _require_owned(commit_partial, owned)
                                        with WindowsReadLocks([commit_partial]):
                                            reject_reparse(
                                                commit_partial,
                                                "Lean replay commit partial",
                                            )
                                            if json.loads(
                                                commit_partial.read_text(
                                                    encoding="utf-8"
                                                )
                                            ) != commit_payload:
                                                raise R34LeafCoreError(
                                                    "Lean replay commit partial changed"
                                                )
                                            if set(replay_directory.iterdir()) != {
                                                paths["lean_log"],
                                                paths["manifest"],
                                                commit_partial,
                                            }:
                                                raise R34LeafCoreError(
                                                    "Lean replay final precommit inventory changed"
                                                )
                                            if set(output_dir.iterdir()) != {
                                                paths[key] for key in core_lock_keys
                                            } | {replay_directory}:
                                                raise R34LeafCoreError(
                                                    "compact-core inventory changed before replay commit"
                                                )
                                            if (
                                                set(source_dir.iterdir())
                                                != source_directory_inventory
                                                or set(source_run_directory.iterdir())
                                                != source_run_inventory
                                            ):
                                                raise R34LeafCoreError(
                                                    "source directory inventory changed during replay"
                                                )
                                            require_dedicated_empty_directory(
                                                temporary_directory,
                                                protected_from_temp,
                                            )
                                            if (
                                                _source_identity(sources)
                                                != locked_sources
                                                or {
                                                    key: file_metadata(
                                                        paths[key], lines=True
                                                    )
                                                    for key in CORE_ARTIFACT_KEYS
                                                }
                                                != artifacts_before
                                                or verify_replay_stack()
                                                != stack_before
                                                or json.loads(
                                                    paths["manifest"].read_text(
                                                        encoding="utf-8"
                                                    )
                                                )
                                                != manifest
                                            ):
                                                raise R34LeafCoreError(
                                                    "locked replay inputs changed before commit publication"
                                                )
                                        if _lexists(paths["replay_commit"]):
                                            raise FileExistsError(
                                                "Lean replay commit marker appeared: "
                                                f"{paths['replay_commit']}"
                                            )
                                        # Linearization point and final fallible
                                        # filesystem operation.  A later verifier
                                        # replays the manifest, hashes, and proof.
                                        os.rename(
                                            commit_partial,
                                            paths["replay_commit"],
                                        )
                                        return manifest
                            except BaseException:
                                # The replay directory remains uncommitted and
                                # quarantined; no failure path deletes anything.
                                raise
                    except BaseException:
                        raise


def replay_lean(
    source_dir: Path, output_dir: Path, slug: str, temporary_directory: Path
) -> dict[str, object]:
    """Replay into a new guarded directory committed by one final marker."""

    return _replay_lean_owned(source_dir, output_dir, slug, temporary_directory)


def preflight(slug: str = registry.FIRST_LEAF_SLUG) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    runner_preflight = runner.preflight(slug)
    table = names(spec)
    namespace, theorem, qualified = lean_identifiers(spec)
    return {
        "status": "PREFLIGHT_ONLY_NO_S_NO_SOLVER_NO_LEAN",
        "selection": materializer.selection_payload(spec),
        "source": {
            "cnf": runner_preflight["formula"],
            "lrat": {
                "name": table["source_lrat"],
                "identity_source": "exact captured-candidate report plus independent file rehash",
            },
            "run_report": table["source_report"],
        },
        "proof_audit": {
            "coverage": "100% LRAT lines indexed before reduction",
            "forward_hints": "rejected",
            "rat": "refused; every addition must use RUP syntax",
            "closure": "backward from unique final empty clause",
            "id_remap": "dense with exact initial-clause ordered-subsequence mapping",
        },
        "caps": {
            "core_clauses_max": MAX_CORE_CLAUSES,
            "core_cnf_bytes_max": MAX_CORE_CNF_BYTES,
            "core_lrat_bytes_max": MAX_CORE_LRAT_BYTES,
            "lean_wall_seconds": LEAN_WALL_LIMIT_SECONDS,
            "lean_family_memory_bytes": LEAN_JOB_MEMORY_LIMIT_BYTES,
            "lean_log_bytes": LEAN_LOG_LIMIT_BYTES,
        },
        "replay": {
            "lean_executable": str(LEAN_EXE),
            "lean_version": LEAN_VERSION,
            "lean_sha256": LEAN_EXE_SHA256,
            "namespace": namespace,
            "theorem": theorem,
            "qualified_theorem": qualified,
            "launch_suspended_until_job_assignment": True,
            "aggregate_family_job_memory_limit": True,
        },
        "outputs": {
            "core_cnf": table["core_cnf"],
            "core_lrat": table["core_lrat"],
            "mapping": MAPPING_NAME,
            "reduction": REDUCTION_NAME,
            "replay": REPLAY_NAME,
            "core_commit": CORE_COMMIT_NAME,
            "replay_directory": REPLAY_DIRECTORY_NAME,
            "lean_log": LEAN_LOG_NAME,
            "manifest": MANIFEST_NAME,
            "replay_commit": REPLAY_COMMIT_NAME,
        },
        "publication": (
            "new guarded directories remain invalid until exact hashes, reparse "
            "checks, Windows-compatible close/rename/relock/revalidation, and a "
            "final atomic commit-marker rename all pass; any failed directory is "
            "left quarantined without unlink/rmdir or overwrite; the marker rename "
            "is the last fallible filesystem operation, so a lost acknowledgement "
            "is recovered only by full verifier revalidation"
        ),
        "path_policy": (
            "all data/temp paths are absolute S:, contain no '..', and cross no "
            "existing symlink/junction/reparse component; source and compact-core "
            "output trees are disjoint; Lean TEMP is a dedicated empty directory "
            "disjoint from all source, output, replay, and tool trees; only TEMP's "
            "parent is directory-guarded so Lean can rename/delete TEMP children"
        ),
        "solver_policy": "this reducer never invokes CaDiCaL or any SAT solver",
        "threat_model": (
            "controlled non-adversarial S: research workspace; observed reparse or "
            "identity mutation fails closed, but hostile concurrent writers are out of scope"
        ),
        "formal_boundary": (
            "leaf-level exact-CNF proof pipeline only; no S7 catalogue composition, "
            "cover6-d7 theorem, global gluing, or Ramsey-number bound"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        default="preflight",
        choices=("preflight", "analyze", "reduce", "verify", "replay"),
    )
    parser.add_argument("--leaf", choices=registry.ACTIONABLE_SLUGS, default=registry.FIRST_LEAF_SLUG)
    parser.add_argument("--source-dir", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--temporary-directory", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight(args.leaf)
    else:
        if args.source_dir is None:
            parser.error(f"{args.command} requires --source-dir")
        if args.command == "analyze":
            result = _public_analysis(analyze_exact(args.source_dir, args.leaf))
        else:
            if args.output_dir is None:
                parser.error(f"{args.command} requires --output-dir")
            if args.command == "reduce":
                result = reduce_exact(args.source_dir, args.output_dir, args.leaf)
            elif args.command == "verify":
                result = verify_core(args.source_dir, args.output_dir, args.leaf)
            else:
                if args.temporary_directory is None:
                    parser.error("replay requires --temporary-directory")
                result = replay_lean(
                    args.source_dir, args.output_dir, args.leaf, args.temporary_directory
                )
                if result["status"].endswith("FAILED"):
                    print(json.dumps(result, indent=2, sort_keys=True))
                    raise SystemExit(2)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
