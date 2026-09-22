from __future__ import annotations

import hashlib
import io
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from . import run_cover6_d7_r34_fgravegow_lrat as runner


REPOSITORY = Path(__file__).resolve().parents[2]
GEN4416_REAL_LOG = (
    REPOSITORY
    / "scripts"
    / "r45_d8_pilot"
    / "gen4416_rooted_classification"
    / "solver.log"
)
GEN4416_REAL_LOG_SHA256 = (
    "38A702497DA1BB0FBA2288FAC3B668BEE4B30BDE6F16E1AD3C517B8D442B4976"
)


CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS = b"""c   --checkproof=2                 (different from default '3')
c LRAT proof file 'leaf.lrat.partial' closed
c LRAT 123 added clauses 60.00%
c LRAT 45 deleted clauses 40.00%
c LRAT 9876 bytes (0.01 MB)
s UNSATISFIABLE
c conflicts:                    3944
c decisions:                    4100
c fixed:                          21
c learned:                      3900
c total process time since initialization:         5.70    seconds
c total real time since initialization:            5.78    seconds
c maximum resident set size of process:          1083.19    MB
"""


class FgraveGowLratPreflightTests(unittest.TestCase):
    def test_preflight_has_fixed_formula_binary_command_and_caps(self) -> None:
        result = runner.preflight()
        self.assertEqual(result["status"], "PREFLIGHT_ONLY_NO_SOLVER_INVOKED")
        self.assertEqual(result["formula"]["variables"], 66)
        self.assertEqual(result["formula"]["clauses"], 4_312_440)
        self.assertEqual(result["formula"]["bytes"], 246_507_635)
        self.assertEqual(
            result["formula"]["sha256"],
            "78D066E03B1F55FACBF8839BCC409E0D45BABF93FA6D266628BB526D2F5E5971",
        )
        self.assertEqual(result["selection"]["record"], "F`GOW")
        self.assertEqual(result["selection"]["incremental_position_one_based"], 6)
        self.assertEqual(result["solver"]["conflict_limit"], 25_000)
        self.assertEqual(result["solver"]["jobs"], 1)
        self.assertEqual(result["supervision"]["wall_limit_seconds"], 300.0)
        self.assertEqual(result["supervision"]["rss_limit_mib"], 1_536)
        self.assertEqual(result["supervision"]["proof_limit_mib"], 512)
        self.assertEqual(result["supervision"]["combined_log_limit_mib"], 8)
        self.assertIn(">= limit", result["supervision"]["threshold_semantics"])
        self.assertTrue(
            result["supervision"]["windows_job_object"]["kill_on_job_close"]
        )
        self.assertEqual(
            result["supervision"]["windows_job_object"][
                "process_memory_limit_mib"
            ],
            1_536,
        )
        self.assertTrue(
            result["supervision"]["rss_sampling"]["stop_at_or_above_limit"]
        )
        self.assertEqual(
            result["solver"]["required_binary_sha256"], runner.SOLVER_SHA256
        )
        self.assertEqual(result["command_template"][1:6], list(runner.SOLVER_FLAGS))
        self.assertEqual(result["command_template"][6:8], ["-c", "25000"])
        self.assertIn("no recognized CaDiCaL error", result["success_policy"])
        self.assertIn("not required by CaDiCaL 2.1.2", result["success_policy"])

    def test_solver_command_has_no_hidden_or_configurable_work(self) -> None:
        command = runner.solver_command(
            Path(r"S:\tools\cadical.exe"),
            Path(r"S:\run\leaf.cnf"),
            Path(r"S:\run\leaf.lrat.partial"),
        )
        self.assertEqual(
            command,
            [
                r"S:\tools\cadical.exe",
                "--lrat",
                "--no-binary",
                "--checkproof=2",
                "--unsat",
                "--walk=false",
                "-c",
                "25000",
                r"S:\run\leaf.cnf",
                r"S:\run\leaf.lrat.partial",
            ],
        )

    def test_absolute_s_policy_rejects_relative_and_other_drives(self) -> None:
        accepted = runner.require_absolute_s_path(Path(r"S:\proof\leaf"), "test")
        self.assertEqual(str(accepted), r"S:\proof\leaf")
        for rejected in (
            Path("relative"),
            Path(r"S:relative"),
            Path(r"C:\forbidden"),
        ):
            with self.assertRaisesRegex(
                runner.FgraveGowLratRunnerError, "absolute S: path"
            ):
                runner.require_absolute_s_path(rejected, "test")

    def test_public_run_rejects_non_s_before_launch(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(
                runner.FgraveGowLratRunnerError, "absolute S: path"
            ):
                runner.run(Path(directory), Path(directory) / "cadical.exe")


class FgraveGowLratStaticHelpersTests(unittest.TestCase):
    @unittest.skipUnless(os.name == "nt", "RSS sampler is intentionally Windows-only")
    def test_windows_rss_sampler_reads_the_current_process(self) -> None:
        with runner.WindowsProcessMemory(os.getpid()) as memory:
            current, peak = memory.sample()
        self.assertGreater(current, 0)
        self.assertGreaterEqual(peak, current)

    @unittest.skipUnless(os.name == "nt", "Job Object is intentionally Windows-only")
    def test_windows_job_object_configures_hard_limit_without_a_process(self) -> None:
        with runner.WindowsJobObject(16 * 1024 * 1024) as job:
            self.assertEqual(job.process_memory_limit_bytes, 16 * 1024 * 1024)
            self.assertFalse(job.assigned)

    def test_real_gen4416_log_without_checker_statistics_is_accepted(self) -> None:
        log_data = GEN4416_REAL_LOG.read_bytes()
        self.assertEqual(
            hashlib.sha256(log_data).hexdigest().upper(), GEN4416_REAL_LOG_SHA256
        )
        markers = runner.proof_check_markers(log_data)
        self.assertFalse(markers["optional_lrat_checker_statistics_present"])
        self.assertTrue(markers["no_cadical_error_diagnostic"])
        self.assertTrue(runner.markers_establish_cadical_checked_lrat(markers))
        metrics = runner.parse_metrics(log_data.decode("ascii"))
        self.assertEqual(metrics["conflicts"], 32342)
        self.assertEqual(metrics["lrat_added_clauses"], 32732)
        self.assertEqual(metrics["lrat_deleted_clauses"], 26982)
        self.assertEqual(metrics["solver_reported_lrat_bytes"], 3_658_365)
        self.assertEqual(metrics["total_real_seconds"], 0.55)
        self.assertEqual(metrics["solver_reported_maximum_resident_mib"], 10.43)
        self.assertEqual(
            runner.classify_outcome(None, 20, 3_658_365, True, markers),
            "CADICAL_CHECKED_LRAT_CANDIDATE",
        )

    def test_required_success_markers_reject_realistic_mutants(self) -> None:
        for mutation in (
            CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS.replace(
                b"s UNSATISFIABLE", b"s UNKNOWN"
            ),
            CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS.replace(
                b"--checkproof=2", b"--checkproof=0"
            ),
            CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS.replace(b" closed", b" open"),
            CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS
            + b"*** cadical error: proof check failed\n",
        ):
            self.assertFalse(
                runner.markers_establish_cadical_checked_lrat(
                    runner.proof_check_markers(mutation)
                )
            )
        stderr_error = runner.proof_check_markers(
            CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS,
            b"cadical: error: failed to check proof\n",
        )
        self.assertFalse(
            runner.markers_establish_cadical_checked_lrat(stderr_error)
        )

    def test_outcome_classifier_rejects_each_incomplete_evidence_mutant(self) -> None:
        markers = runner.proof_check_markers(CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS)
        self.assertEqual(
            runner.classify_outcome(None, 20, 9876, True, markers),
            "CADICAL_CHECKED_LRAT_CANDIDATE",
        )
        self.assertEqual(
            runner.classify_outcome("RSS_LIMIT", -9, 0, False, markers),
            "RSS_LIMIT",
        )
        self.assertEqual(
            runner.classify_outcome(None, 0, 9876, True, markers),
            "SOLVER_DID_NOT_RETURN_UNSAT",
        )
        self.assertEqual(
            runner.classify_outcome(None, 20, 0, False, markers),
            "LRAT_MISSING_OR_EMPTY",
        )
        self.assertEqual(
            runner.classify_outcome(None, 20, 9876, False, markers),
            "LRAT_SIZE_DISAGREES_WITH_SOLVER_LOG",
        )
        missing = dict(markers)
        missing["checkproof_option_echoed"] = False
        self.assertEqual(
            runner.classify_outcome(None, 20, 9876, True, missing),
            "CADICAL_SELF_CHECK_MARKERS_INCOMPLETE",
        )
        with mock.patch.object(runner, "PROOF_LIMIT_BYTES", 9876):
            self.assertEqual(
                runner.classify_outcome(None, 20, 9876, True, markers),
                "PROOF_SIZE_LIMIT",
            )

    def test_combined_log_capture_never_writes_past_exact_budget(self) -> None:
        budget = runner.CombinedLogBudget(7)
        first_target = io.BytesIO()
        second_target = io.BytesIO()
        budget.copy(io.BytesIO(b"abcd"), first_target)
        budget.copy(io.BytesIO(b"efghi"), second_target)
        self.assertEqual(first_target.getvalue(), b"abcd")
        self.assertEqual(second_target.getvalue(), b"efg")
        self.assertEqual(budget.total_bytes, 7)
        self.assertTrue(budget.limit_reached.is_set())
        self.assertEqual(budget.errors, ())

    def test_collision_guard_preserves_every_existing_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            directory = Path(directory_text)
            paths = runner.run_paths(directory)
            paths.proof.write_bytes(b"keep final")
            with self.assertRaisesRegex(FileExistsError, "refusing to overwrite"):
                runner.refuse_artifact_collisions(paths)
            self.assertEqual(paths.proof.read_bytes(), b"keep final")
            paths.proof.unlink()
            paths.stderr_partial.write_bytes(b"keep partial")
            with self.assertRaisesRegex(FileExistsError, "refusing residual"):
                runner.refuse_artifact_collisions(paths)
            self.assertEqual(paths.stderr_partial.read_bytes(), b"keep partial")

    def test_formula_partial_is_a_hard_stop(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            paths = runner.run_paths(Path(directory_text))
            paths.formula_partial.write_bytes(b"incomplete formula")
            with self.assertRaisesRegex(FileExistsError, "formula partial"):
                runner.refuse_artifact_collisions(paths)

    def test_reservation_failure_cleans_only_partials_created_by_this_run(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            paths = runner.run_paths(Path(directory_text))
            paths.stderr_partial.write_bytes(b"foreign partial")
            with self.assertRaises(FileExistsError):
                runner.reserve_runner_partials(paths)
            self.assertFalse(paths.proof_partial.exists())
            self.assertFalse(paths.stdout_partial.exists())
            self.assertEqual(paths.stderr_partial.read_bytes(), b"foreign partial")

    def test_owned_cleanup_never_deletes_unowned_partial(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            paths = runner.run_paths(Path(directory_text))
            owned = runner.reserve_runner_partials(paths)
            foreign = Path(directory_text) / "foreign.partial"
            foreign.write_bytes(b"preserve")
            runner.cleanup_owned_partials(owned)
            self.assertEqual(owned, set())
            self.assertEqual(foreign.read_bytes(), b"preserve")
            self.assertFalse(paths.proof_partial.exists())
            self.assertFalse(paths.stdout_partial.exists())
            self.assertFalse(paths.stderr_partial.exists())

    def test_simulated_log_publish_race_cleans_remaining_owned_partials(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            paths = runner.run_paths(Path(directory_text))
            owned = runner.reserve_runner_partials(paths)
            paths.stdout.write_bytes(b"foreign final")
            try:
                with self.assertRaisesRegex(FileExistsError, "publish race"):
                    runner.publish_owned(paths.stdout_partial, paths.stdout, owned)
            finally:
                runner.cleanup_owned_partials(owned)
            self.assertEqual(paths.stdout.read_bytes(), b"foreign final")
            self.assertFalse(paths.proof_partial.exists())
            self.assertFalse(paths.stdout_partial.exists())
            self.assertFalse(paths.stderr_partial.exists())

    def test_atomic_report_refuses_final_and_residual_partial(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            directory = Path(directory_text)
            final = directory / "report.json"
            partial = directory / "report.json.partial"
            runner.atomic_write_new_json(final, partial, {"status": "PASS"})
            self.assertEqual(json.loads(final.read_text(encoding="utf-8"))["status"], "PASS")
            self.assertFalse(partial.exists())
            with self.assertRaisesRegex(FileExistsError, "overwrite"):
                runner.atomic_write_new_json(final, partial, {"status": "MUTANT"})
            self.assertEqual(json.loads(final.read_text(encoding="utf-8"))["status"], "PASS")

    def test_atomic_report_cleans_its_partial_when_publication_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory_text:
            directory = Path(directory_text)
            final = directory / "report.json"
            partial = directory / "report.json.partial"
            with mock.patch.object(
                runner, "publish_new", side_effect=OSError("simulated publish failure")
            ):
                with self.assertRaisesRegex(OSError, "simulated publish failure"):
                    runner.atomic_write_new_json(final, partial, {"status": "PASS"})
            self.assertFalse(final.exists())
            self.assertFalse(partial.exists())

    def test_popen_job_assignment_and_capture_are_fully_simulated(self) -> None:
        events: list[object] = []

        class FakeProcess:
            pid = 4242
            returncode = 20
            stdout = io.BytesIO(CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS)
            stderr = io.BytesIO(b"")
            _handle = 123

            def poll(self) -> int:
                return self.returncode

            def kill(self) -> None:
                events.append("kill")
                self.returncode = -9

            def wait(self, timeout: float | None = None) -> int:
                del timeout
                return self.returncode

        class FakeJob:
            def __init__(self, limit: int) -> None:
                events.append(("job_create", limit))

            def assign(self, process: FakeProcess) -> None:
                events.append(("job_assign", process.pid))

            def close(self) -> None:
                events.append("job_close")

        def fake_popen(command: list[str], **kwargs: object) -> FakeProcess:
            events.append(("popen", command, kwargs))
            return FakeProcess()

        def fake_monitor(
            process: FakeProcess, proof: Path, logs: runner.CombinedLogBudget
        ) -> runner.MonitorResult:
            del proof, logs
            events.append(("monitor", process.pid))
            return runner.MonitorResult(20, None, 1.0, 1024, 10, 2, None)

        with tempfile.TemporaryDirectory() as directory_text:
            directory = Path(directory_text)
            paths = runner.run_paths(directory)
            owned = runner.reserve_runner_partials(paths)
            try:
                budget = runner.CombinedLogBudget(1024 * 1024)
                with paths.stdout_partial.open("r+b") as stdout_stream:
                    with paths.stderr_partial.open("r+b") as stderr_stream:
                        monitor, error, assigned = runner.execute_supervised_process(
                            ["fake-cadical", "formula", "proof"],
                            directory,
                            {},
                            paths,
                            stdout_stream,
                            stderr_stream,
                            budget,
                            popen_factory=fake_popen,
                            job_factory=FakeJob,
                            monitor_factory=fake_monitor,
                        )
                self.assertEqual(monitor.returncode, 20)
                self.assertIsNone(error)
                self.assertTrue(assigned)
                self.assertEqual(
                    paths.stdout_partial.read_bytes(),
                    CHECKED_LOG_WITHOUT_OPTIONAL_STATISTICS,
                )
                self.assertEqual(paths.stderr_partial.read_bytes(), b"")
                self.assertEqual(events[0][0], "popen")
                self.assertEqual(events[1], ("job_create", runner.RSS_LIMIT_BYTES))
                self.assertEqual(events[2], ("job_assign", 4242))
                self.assertEqual(events[3], ("monitor", 4242))
                self.assertEqual(events[4], "job_close")
                self.assertNotIn("kill", events)
            finally:
                runner.cleanup_owned_partials(owned)

    def test_simulated_popen_failure_leaves_no_owned_partial(self) -> None:
        def failing_popen(*_args: object, **_kwargs: object) -> object:
            raise OSError("simulated Popen failure")

        with tempfile.TemporaryDirectory() as directory_text:
            directory = Path(directory_text)
            paths = runner.run_paths(directory)
            owned = runner.reserve_runner_partials(paths)
            with paths.stdout_partial.open("r+b") as stdout_stream:
                with paths.stderr_partial.open("r+b") as stderr_stream:
                    monitor, error, assigned = runner.execute_supervised_process(
                        ["fake-cadical"],
                        directory,
                        {},
                        paths,
                        stdout_stream,
                        stderr_stream,
                        runner.CombinedLogBudget(1024),
                        popen_factory=failing_popen,
                    )
            self.assertEqual(monitor.stop_reason, "LAUNCH_OR_MONITOR_ERROR")
            self.assertIn("simulated Popen failure", error or "")
            self.assertFalse(assigned)
            self.assertIn(
                b"simulated Popen failure", paths.stderr_partial.read_bytes()
            )
            runner.cleanup_owned_partials(owned)
            self.assertFalse(paths.proof_partial.exists())
            self.assertFalse(paths.stdout_partial.exists())
            self.assertFalse(paths.stderr_partial.exists())

    def test_monitor_stops_at_equal_proof_rss_log_and_wall_caps(self) -> None:
        class FakeProcess:
            pid = 77

            def __init__(self) -> None:
                self.returncode: int | None = None
                self.killed = False

            def poll(self) -> int | None:
                return self.returncode

            def kill(self) -> None:
                self.killed = True
                self.returncode = -9

            def wait(self, timeout: float | None = None) -> int:
                del timeout
                if self.returncode is None:
                    self.returncode = 0
                return self.returncode

        class FakeMemory:
            def __init__(self, peak: int) -> None:
                self.peak = peak

            def __enter__(self) -> "FakeMemory":
                return self

            def __exit__(self, *_unused: object) -> None:
                return None

            def sample(self) -> tuple[int, int]:
                return self.peak, self.peak

        with tempfile.TemporaryDirectory() as directory_text:
            proof = Path(directory_text) / "proof.partial"

            proof.write_bytes(b"1234")
            proof_process = FakeProcess()
            with mock.patch.object(runner, "PROOF_LIMIT_BYTES", 4):
                with mock.patch.object(
                    runner, "WindowsProcessMemory", return_value=FakeMemory(1)
                ):
                    proof_result = runner.monitor_process(
                        proof_process, proof, runner.CombinedLogBudget(100)
                    )
            self.assertEqual(proof_result.stop_reason, "PROOF_SIZE_LIMIT")
            self.assertTrue(proof_process.killed)

            proof.write_bytes(b"")
            rss_process = FakeProcess()
            with mock.patch.object(runner, "RSS_LIMIT_BYTES", 10):
                with mock.patch.object(
                    runner, "WindowsProcessMemory", return_value=FakeMemory(10)
                ):
                    rss_result = runner.monitor_process(
                        rss_process, proof, runner.CombinedLogBudget(100)
                    )
            self.assertEqual(rss_result.stop_reason, "RSS_LIMIT")
            self.assertTrue(rss_process.killed)

            log_process = FakeProcess()
            log_budget = runner.CombinedLogBudget(4)
            self.assertEqual(log_budget.accepted_prefix(b"1234"), b"1234")
            with mock.patch.object(
                runner, "WindowsProcessMemory", return_value=FakeMemory(1)
            ):
                log_result = runner.monitor_process(log_process, proof, log_budget)
            self.assertEqual(log_result.stop_reason, "LOG_BYTES_LIMIT")
            self.assertTrue(log_process.killed)

            wall_process = FakeProcess()
            with mock.patch.object(runner, "WALL_LIMIT_SECONDS", 300.0):
                with mock.patch.object(
                    runner, "WindowsProcessMemory", return_value=FakeMemory(1)
                ):
                    with mock.patch.object(
                        runner.time,
                        "perf_counter",
                        side_effect=(0.0, 300.0, 300.0),
                    ):
                        wall_result = runner.monitor_process(
                            wall_process, proof, runner.CombinedLogBudget(100)
                        )
            self.assertEqual(wall_result.stop_reason, "WALL_LIMIT")
            self.assertTrue(wall_process.killed)


if __name__ == "__main__":
    unittest.main()
