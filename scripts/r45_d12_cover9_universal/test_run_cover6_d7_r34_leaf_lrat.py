from __future__ import annotations

import io
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from . import cover6_d7_r34_leaf_registry as registry
from . import run_cover6_d7_r34_leaf_lrat as subject


class FakeProcess:
    def __init__(self, events: list[object]) -> None:
        self.events = events
        self.pid = 1234
        self.stdout = io.BytesIO(b"")
        self.stderr = io.BytesIO(b"")
        self.returncode = 20

    def poll(self) -> int:
        return self.returncode

    def wait(self, timeout: float | None = None) -> int:
        self.events.append(("wait", timeout))
        return self.returncode

    def kill(self) -> None:
        self.events.append("kill")
        self.returncode = -9


class FakeJob:
    def __init__(self, events: list[object], cap: int) -> None:
        self.events = events
        self.events.append(("job-created", cap))
        self.assigned = False

    def assign(self, process: FakeProcess) -> None:
        self.events.append("job-assigned")
        self.assigned = True

    def close(self) -> None:
        self.events.append("job-closed")


class RunnerTests(unittest.TestCase):
    def test_preflight_freezes_caps_and_fodpo_names(self) -> None:
        result = subject.preflight("FoDPO")
        self.assertEqual(result["status"], "PREFLIGHT_ONLY_NO_S_NO_SOLVER_INVOKED")
        self.assertEqual(result["formula"]["sha256"], registry.LEAF_BY_SLUG["FoDPO"].target_sha256)
        self.assertEqual(result["solver"]["conflict_limit"], 25_000)
        self.assertEqual(result["supervision"]["wall_limit_seconds"], 300.0)
        self.assertEqual(result["supervision"]["rss_limit_mib"], 1_536)
        self.assertEqual(result["supervision"]["proof_limit_mib"], 512)
        self.assertEqual(result["supervision"]["combined_log_limit_mib"], 8)
        self.assertTrue(
            result["supervision"]["windows_job_object"]["launch_suspended_until_assignment"]
        )
        self.assertEqual(
            result["outputs"]["proof"],
            "cover6_closed_f7_r34_i7_FoDPO_c25k.lrat",
        )
        self.assertEqual(
            result["outputs"]["directory_pattern"],
            subject.artifact_names(registry.select_actionable("FoDPO"))["directory"]
            + ".<32-hex-run-id>",
        )

    def test_run_id_is_exact_lowercase_128_bit_hex(self) -> None:
        spec = registry.select_actionable("FoDPO")
        path = subject.run_paths(Path("root"), spec, run_id="a" * 32)
        self.assertTrue(path.report.parent.name.endswith("." + "a" * 32))
        for mutant in ("a" * 31, "A" * 32, "g" * 32, "a" * 33):
            with self.subTest(mutant=mutant):
                with self.assertRaises(subject.R34LeafLratRunnerError):
                    subject.run_paths(Path("root"), spec, run_id=mutant)

    def test_every_actionable_leaf_has_disjoint_names(self) -> None:
        all_names = [subject.artifact_names(spec) for spec in registry.ACTIONABLE_LEAVES]
        flattened = [name for table in all_names for name in table.values()]
        self.assertEqual(len(flattened), len(set(flattened)))

    def test_suspended_launch_is_assigned_before_resume_and_monitor(self) -> None:
        events: list[object] = []
        spec = registry.select_actionable("FoDPO")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec, run_id="1" * 32)
            stdout_path = directory / "stdout.partial"
            stderr_path = directory / "stderr.partial"
            stdout_path.touch()
            stderr_path.touch()

            def popen(*_args: object, **kwargs: object) -> FakeProcess:
                events.append(("popen", kwargs["creationflags"]))
                return FakeProcess(events)

            def job_factory(cap: int) -> FakeJob:
                return FakeJob(events, cap)

            def resume(_process: FakeProcess) -> None:
                self.assertIn("job-assigned", events)
                events.append("resumed")

            def monitor(
                _process: FakeProcess,
                _proof: Path,
                _budget: subject.CombinedLogBudget,
            ) -> subject.MonitorResult:
                self.assertEqual(events[-1], "resumed")
                events.append("monitored")
                return subject.MonitorResult(20, None, 0.01, 1024, 0, 1, None)

            with stdout_path.open("r+b") as stdout_stream:
                with stderr_path.open("r+b") as stderr_stream:
                    result, error, assigned = subject.execute_supervised_process(
                        ["fake-cadical"],
                        directory,
                        {},
                        paths,
                        stdout_stream,
                        stderr_stream,
                        subject.CombinedLogBudget(1024),
                        popen_factory=popen,
                        job_factory=job_factory,
                        resume_factory=resume,
                        monitor_factory=monitor,
                    )
        self.assertIsNone(error)
        self.assertTrue(assigned)
        self.assertEqual(result.returncode, 20)
        self.assertEqual(events[0], ("job-created", subject.RSS_LIMIT_BYTES))
        self.assertEqual(events[1][0], "popen")
        self.assertTrue(events[1][1] & 0x00000004)
        self.assertLess(events.index("job-assigned"), events.index("resumed"))
        self.assertLess(events.index("resumed"), events.index("monitored"))
        self.assertEqual(events[-1], "job-closed")

    def test_job_creation_failure_prevents_popen(self) -> None:
        events: list[object] = []
        spec = registry.select_actionable("FoDPO")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec)
            stdout_path = directory / "stdout.partial"
            stderr_path = directory / "stderr.partial"
            stdout_path.touch()
            stderr_path.touch()

            def bad_job(_cap: int) -> object:
                events.append("job-failed")
                raise OSError("simulated Job failure")

            def forbidden_popen(*_args: object, **_kwargs: object) -> FakeProcess:
                events.append("popen")
                return FakeProcess(events)

            with stdout_path.open("r+b") as stdout_stream:
                with stderr_path.open("r+b") as stderr_stream:
                    result, error, assigned = subject.execute_supervised_process(
                        ["fake-cadical"],
                        directory,
                        {},
                        paths,
                        stdout_stream,
                        stderr_stream,
                        subject.CombinedLogBudget(1024),
                        popen_factory=forbidden_popen,
                        job_factory=bad_job,
                    )
        self.assertEqual(events, ["job-failed"])
        self.assertFalse(assigned)
        self.assertEqual(result.stop_reason, "LAUNCH_OR_MONITOR_ERROR")
        self.assertIn("simulated Job failure", error or "")

    def test_job_closes_even_when_log_fsync_raises(self) -> None:
        events: list[object] = []
        spec = registry.select_actionable("FoDPO")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec)
            stdout_path = directory / "stdout.partial"
            stderr_path = directory / "stderr.partial"
            stdout_path.touch()
            stderr_path.touch()

            def popen(*_args: object, **_kwargs: object) -> FakeProcess:
                return FakeProcess(events)

            with (
                stdout_path.open("r+b") as stdout_stream,
                stderr_path.open("r+b") as stderr_stream,
                mock.patch.object(subject.os, "fsync", side_effect=OSError("fsync mutant")),
            ):
                with self.assertRaisesRegex(OSError, "fsync mutant"):
                    subject.execute_supervised_process(
                        ["fake-cadical"],
                        directory,
                        {},
                        paths,
                        stdout_stream,
                        stderr_stream,
                        subject.CombinedLogBudget(1024),
                        popen_factory=popen,
                        job_factory=lambda cap: FakeJob(events, cap),
                        resume_factory=lambda _process: None,
                        monitor_factory=lambda *_args: subject.MonitorResult(
                            20, None, 0.01, 1024, 0, 1, None
                        ),
                    )
        self.assertEqual(events[-1], "job-closed")

    def test_collision_and_path_mutants_fail_closed(self) -> None:
        spec = registry.select_actionable("FoDPO")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec)
            paths.proof_partial.parent.mkdir()
            paths.proof_partial.write_bytes(b"foreign")
            with self.assertRaises(FileExistsError):
                subject.frozen_runner.refuse_artifact_collisions(paths)
            self.assertEqual(paths.proof_partial.read_bytes(), b"foreign")
        for path in (
            Path("relative"),
            Path(r"C:\wrong"),
            Path(r"\\host\share"),
            Path(r"S:\safe\..\escape"),
        ):
            with self.assertRaises(subject.R34LeafLratRunnerError):
                subject.require_absolute_s_path(path, "test")

    def test_run_publishes_one_commit_bound_directory(self) -> None:
        spec = registry.select_actionable("FoDPO")
        proof = b"proof-candidate\n"
        stdout = (
            b"c command line option '--checkproof=2'\n"
            b"s UNSATISFIABLE\n"
            b"c LRAT proof file candidate closed\n"
            b"c LRAT 5 added clauses\n"
            b"c LRAT 3 deleted clauses\n"
            + f"c LRAT {len(proof)} bytes\n".encode("ascii")
            + b"c conflicts: 7\n"
            + b"c maximum resident set size of process: 10.0 MB\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec, run_id="1" * 32)
            stage = paths.report.parent
            stage.mkdir()
            owned = subject._reserve_runner_partials(paths)

            def fake_execute(
                _command: list[str],
                _directory: Path,
                _environment: dict[str, str],
                received_paths: subject.RunPaths,
                stdout_stream: object,
                _stderr_stream: object,
                _budget: subject.CombinedLogBudget,
            ) -> tuple[subject.MonitorResult, None, bool]:
                stdout_stream.write(stdout)  # type: ignore[attr-defined]
                received_paths.proof_partial.write_bytes(proof)
                return subject.MonitorResult(20, None, 0.1, 1024, len(proof), 2, None), None, True

            with mock.patch.object(subject, "execute_supervised_process", fake_execute):
                report, success = subject._run_staged(
                    spec,
                    paths,
                    directory,
                    Path(r"S:\tools\cadical.exe"),
                    subject.SOLVER_SHA256,
                    ["simulated"],
                    {},
                    {"name": spec.target_name, "bytes": spec.target_bytes,
                     "sha256": spec.target_sha256, "lines": 4_312_441},
                    "2026-08-08T00:00:00+00:00",
                    owned,
                )
            self.assertTrue(success)
            self.assertEqual(report["status"], "UNSAT_CANDIDATE_CAPTURED")
            self.assertEqual(
                report["result"]["outcome_reason"], "UNSAT_CANDIDATE_CAPTURED"
            )
            self.assertIs(
                report["result"]["published_proof_bound_to_internal_checkproof"],
                False,
            )
            self.assertNotIn("CHECKED", str(report).upper())
            self.assertTrue(paths.report_partial.exists())
            with mock.patch.object(
                subject.safety, "reject_absolute_s_reparse", side_effect=lambda path, _label: path
            ):
                subject._commit_stage(directory, spec, paths, report, owned)
            final_paths = paths
            self.assertTrue(final_paths.report.parent.is_dir())
            self.assertTrue(final_paths.proof.is_file())
            self.assertTrue(final_paths.stdout.is_file())
            self.assertTrue(final_paths.stderr.is_file())
            self.assertTrue(final_paths.report.is_file())
            self.assertTrue(
                (final_paths.report.parent / subject.artifact_names(spec)["commit"]).is_file()
            )
            self.assertFalse(any(final_paths.report.parent.glob("*.partial")))

    def test_real_inconclusive_report_names_only_quarantine_partials(self) -> None:
        spec = registry.select_actionable("FoDPO")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec, run_id="9" * 32)
            paths.report.parent.mkdir()
            owned = subject._reserve_runner_partials(paths)

            def fake_execute(*_args: object, **_kwargs: object) -> tuple[
                subject.MonitorResult, None, bool
            ]:
                return subject.MonitorResult(0, None, 0.1, 1024, 0, 2, None), None, True

            with mock.patch.object(subject, "execute_supervised_process", fake_execute):
                report, success = subject._run_staged(
                    spec,
                    paths,
                    directory,
                    Path(r"S:\tools\cadical.exe"),
                    subject.SOLVER_SHA256,
                    ["simulated"],
                    {},
                    {
                        "name": spec.target_name,
                        "bytes": spec.target_bytes,
                        "sha256": spec.target_sha256,
                        "lines": 4_312_441,
                    },
                    "2026-08-08T00:00:00+00:00",
                    owned,
                )
            self.assertFalse(success)
            self.assertEqual(report["status"], "INCONCLUSIVE_NO_LRAT_PUBLISHED")
            self.assertEqual(
                {key: report["published"][key] for key in ("proof", "stdout", "stderr", "report", "commit")},
                {key: None for key in ("proof", "stdout", "stderr", "report", "commit")},
            )
            self.assertFalse(report["quarantine"]["commit_marker_present"])
            self.assertEqual(
                set(report["quarantine"]["partials"]),
                {
                    paths.proof_partial.name,
                    paths.stdout_partial.name,
                    paths.stderr_partial.name,
                    paths.report_partial.name,
                },
            )
            self.assertTrue(paths.report_partial.exists())
            self.assertFalse(
                (paths.report.parent / subject.artifact_names(spec)["commit"]).exists()
            )

    @unittest.skipUnless(subject.os.name == "nt", "Windows object guards are required")
    def test_directory_guard_blocks_directory_rename_but_allows_child_creation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / "transaction"
            renamed = root / "substituted"
            directory.mkdir()
            with subject.WindowsDirectoryGuard(directory):
                (directory / "child.bin").write_bytes(b"owned")
                with self.assertRaises(PermissionError):
                    directory.rename(renamed)
            directory.rename(renamed)
            self.assertEqual((renamed / "child.bin").read_bytes(), b"owned")

    @unittest.skipUnless(subject.os.name == "nt", "Windows file locks are required")
    def test_commit_output_lock_rejects_real_mutation_attempt(self) -> None:
        spec = registry.select_actionable("FoDPO")
        proof = b"proof-candidate\n"
        stdout = (
            b"c command line option '--checkproof=2'\n"
            b"s UNSATISFIABLE\n"
            b"c LRAT proof file candidate closed\n"
            b"c LRAT 5 added clauses\n"
            b"c LRAT 3 deleted clauses\n"
            + f"c LRAT {len(proof)} bytes\n".encode("ascii")
            + b"c conflicts: 7\n"
            + b"c maximum resident set size of process: 10.0 MB\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            paths = subject.run_paths(directory, spec, run_id="2" * 32)
            paths.report.parent.mkdir()
            owned = subject._reserve_runner_partials(paths)

            def fake_execute(
                _command: list[str],
                _directory: Path,
                _environment: dict[str, str],
                received_paths: subject.RunPaths,
                stdout_stream: object,
                _stderr_stream: object,
                _budget: subject.CombinedLogBudget,
            ) -> tuple[subject.MonitorResult, None, bool]:
                stdout_stream.write(stdout)  # type: ignore[attr-defined]
                received_paths.proof_partial.write_bytes(proof)
                return subject.MonitorResult(20, None, 0.1, 1024, len(proof), 2, None), None, True

            with mock.patch.object(subject, "execute_supervised_process", fake_execute):
                report, success = subject._run_staged(
                    spec,
                    paths,
                    directory,
                    Path(r"S:\tools\cadical.exe"),
                    subject.SOLVER_SHA256,
                    ["simulated"],
                    {},
                    {
                        "name": spec.target_name,
                        "bytes": spec.target_bytes,
                        "sha256": spec.target_sha256,
                        "lines": 4_312_441,
                    },
                    "2026-08-08T00:00:00+00:00",
                    owned,
                )
            original_identity = subject._identity_with_name
            staged_mutation_attempted = False
            staged_mutation_denied = False
            final_mutation_attempted = False
            final_mutation_denied = False

            def probe_locked_identity(path: Path, name: str) -> dict[str, int | str]:
                nonlocal staged_mutation_attempted, staged_mutation_denied
                nonlocal final_mutation_attempted, final_mutation_denied
                if path == paths.stdout_partial and not staged_mutation_attempted:
                    staged_mutation_attempted = True
                    try:
                        path.write_bytes(b"mutant")
                    except PermissionError:
                        staged_mutation_denied = True
                if path == paths.stdout and not final_mutation_attempted:
                    final_mutation_attempted = True
                    try:
                        path.write_bytes(b"mutant")
                    except PermissionError:
                        final_mutation_denied = True
                return original_identity(path, name)

            with (
                mock.patch.object(
                    subject.safety,
                    "reject_absolute_s_reparse",
                    side_effect=lambda path, _label: path,
                ),
                mock.patch.object(
                    subject, "_identity_with_name", side_effect=probe_locked_identity
                ),
            ):
                subject._commit_stage(directory, spec, paths, report, owned)
                final_paths = {
                    paths.proof,
                    paths.stdout,
                    paths.stderr,
                    paths.report,
                }
                commit = paths.report.parent / subject.artifact_names(spec)["commit"]
                verified_owned = {
                    path: subject.safety.regular_file_object_identity(path)
                    for path in final_paths | {commit}
                }
                with subject.WindowsReadLocks(
                    sorted(final_paths | {commit}, key=str)
                ):
                    subject._verify_committed_stage_locked(
                        spec, paths, report, verified_owned
                    )
            self.assertTrue(staged_mutation_attempted)
            self.assertTrue(staged_mutation_denied)
            self.assertTrue(final_mutation_attempted)
            self.assertTrue(final_mutation_denied)
            self.assertEqual(paths.stdout.read_bytes(), stdout)
            self.assertEqual(
                set(paths.report.parent.iterdir()), final_paths | {commit}
            )
            self.assertFalse(any(paths.report.parent.glob("*.partial")))

    def test_run_holds_read_locks_across_all_hashes_run_and_commit(self) -> None:
        spec = registry.select_actionable("FoDPO")
        events: list[str] = []
        lock_active = False

        class FakeLocks:
            def __init__(self, paths: list[Path]) -> None:
                self.paths = paths

            def __enter__(self) -> "FakeLocks":
                nonlocal lock_active
                self.assert_paths = self.paths
                lock_active = True
                events.append("lock-enter")
                return self

            def __exit__(self, *_unused: object) -> None:
                nonlocal lock_active
                events.append("lock-exit")
                lock_active = False

        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solver = directory / "cadical.exe"
            formula = directory / spec.target_name
            solver.write_bytes(b"solver")
            formula.write_bytes(b"formula")

            def inspect(_path: Path, _identity: object) -> dict[str, int | str]:
                self.assertTrue(lock_active)
                events.append("formula-hash")
                return {"name": spec.target_name, "bytes": spec.target_bytes,
                        "sha256": spec.target_sha256, "lines": 4_312_441}

            def solver_hash(_path: Path) -> str:
                self.assertTrue(lock_active)
                events.append("solver-hash")
                return subject.SOLVER_SHA256

            def staged(*_args: object, **_kwargs: object) -> tuple[dict[str, object], bool]:
                self.assertTrue(lock_active)
                events.append("run")
                return {"status": "UNSAT_CANDIDATE_CAPTURED"}, True

            def commit(*_args: object, **_kwargs: object) -> None:
                self.assertTrue(lock_active)
                events.append("commit")

            def verify_commit(*_args: object, **_kwargs: object) -> None:
                self.assertTrue(lock_active)
                events.append("verify-commit")

            with (
                mock.patch.object(subject, "preflight", return_value={}),
                mock.patch.object(subject, "require_absolute_s_path", side_effect=lambda path, _label: path),
                mock.patch.object(subject.os, "name", "nt"),
                mock.patch.object(subject.safety, "require_existing_directory", side_effect=lambda path, _label: path),
                mock.patch.object(subject.safety, "require_existing_regular_file", side_effect=lambda path, _label: path),
                mock.patch.object(subject.safety, "reject_absolute_s_reparse", side_effect=lambda path, _label: path),
                mock.patch.object(subject, "WindowsReadLocks", FakeLocks),
                mock.patch.object(subject.leaf, "inspect_stream", side_effect=inspect),
                mock.patch.object(subject.frozen_runner, "sha256_file", side_effect=solver_hash),
                mock.patch.object(subject, "_run_staged", side_effect=staged),
                mock.patch.object(subject, "_commit_stage", side_effect=commit),
                mock.patch.object(
                    subject,
                    "_verify_committed_stage_locked",
                    side_effect=verify_commit,
                ) as post_commit_verify,
            ):
                result = subject.run(directory, solver, spec.slug)
        self.assertEqual(result, {"status": "UNSAT_CANDIDATE_CAPTURED"})
        self.assertEqual(events.count("formula-hash"), 3)
        self.assertEqual(events.count("solver-hash"), 3)
        self.assertLess(events.index("lock-enter"), events.index("run"))
        self.assertLess(events.index("commit"), events.index("lock-exit"))
        post_commit_verify.assert_not_called()

    def test_inconclusive_run_leaves_random_directory_quarantined_without_commit(self) -> None:
        spec = registry.select_actionable("FoDPO")

        class NoopGuard:
            def __init__(self, *_args: object) -> None:
                pass

            def __enter__(self) -> "NoopGuard":
                return self

            def __exit__(self, *_args: object) -> None:
                pass

        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solver = directory / "cadical.exe"
            formula = directory / spec.target_name
            solver.write_bytes(b"solver")
            formula.write_bytes(b"formula")
            expected_formula = {
                "name": spec.target_name,
                "bytes": spec.target_bytes,
                "sha256": spec.target_sha256,
                "lines": 4_312_441,
            }
            with (
                mock.patch.object(subject, "preflight", return_value={}),
                mock.patch.object(subject, "require_absolute_s_path", side_effect=lambda path, _label: path),
                mock.patch.object(subject.os, "name", "nt"),
                mock.patch.object(subject.secrets, "token_hex", return_value="e" * 32),
                mock.patch.object(subject.safety, "require_existing_directory", side_effect=lambda path, _label: path),
                mock.patch.object(subject.safety, "require_existing_regular_file", side_effect=lambda path, _label: path),
                mock.patch.object(subject.safety, "reject_absolute_s_reparse", side_effect=lambda path, _label: path),
                mock.patch.object(subject, "WindowsDirectoryGuard", NoopGuard),
                mock.patch.object(subject, "WindowsReadLocks", NoopGuard),
                mock.patch.object(subject.leaf, "inspect_stream", return_value=expected_formula),
                mock.patch.object(subject.frozen_runner, "sha256_file", return_value=subject.SOLVER_SHA256),
                mock.patch.object(
                    subject,
                    "_run_staged",
                    return_value=({"status": "INCONCLUSIVE_NO_LRAT_PUBLISHED"}, False),
                ),
                mock.patch.object(subject, "_commit_stage") as commit,
            ):
                result = subject.run(directory, solver, spec.slug)
            self.assertEqual(result["status"], "INCONCLUSIVE_NO_LRAT_PUBLISHED")
            commit.assert_not_called()
            run_directory = directory / (
                subject.artifact_names(spec)["directory"] + "." + "e" * 32
            )
            self.assertTrue(run_directory.is_dir())
            self.assertEqual(
                {path.name for path in run_directory.iterdir()},
                {
                    subject.run_paths(directory, spec, run_id="e" * 32).proof_partial.name,
                    subject.run_paths(directory, spec, run_id="e" * 32).stdout_partial.name,
                    subject.run_paths(directory, spec, run_id="e" * 32).stderr_partial.name,
                },
            )
            self.assertFalse(
                (run_directory / subject.artifact_names(spec)["commit"]).exists()
            )


if __name__ == "__main__":
    unittest.main()
