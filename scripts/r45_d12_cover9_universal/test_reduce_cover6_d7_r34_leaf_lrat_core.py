from __future__ import annotations

import copy
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from . import cover6_d7_r34_leaf_registry as registry
from . import materialize_cover6_d7_r34_leaf as materializer
from . import reduce_cover6_d7_r34_leaf_lrat_core as subject
from . import run_cover6_d7_r34_leaf_lrat as runner


RUN_ID = "a" * 32


def valid_report() -> dict[str, object]:
    spec = registry.select_actionable("FoDPO")
    proof_bytes = 12_345
    solver_path = Path(r"S:\TOOLS\cadical.exe")
    run_paths = runner.run_paths(Path(r"S:\RUNROOT"), spec, run_id=RUN_ID)
    artifact_names = runner.artifact_names(spec)
    return {
        "schema_version": 1,
        "status": "UNSAT_CANDIDATE_CAPTURED",
        "formula": {
            "name": spec.target_name,
            "bytes": spec.target_bytes,
            "sha256": spec.target_sha256,
            "lines": materializer.TARGET_LINES,
            "variables": 66,
            "clauses": materializer.TARGET_CLAUSES,
        },
        "selection": materializer.selection_payload(spec),
        "solver": {
            "name": runner.SOLVER_NAME,
            "version": runner.SOLVER_VERSION,
            "binary_sha256": runner.SOLVER_SHA256,
            "flags": list(runner.SOLVER_FLAGS),
            "conflict_limit": runner.CONFLICT_LIMIT,
            "jobs": 1,
            "returncode": 20,
            "path": str(solver_path),
            "command": runner.solver_command(solver_path, run_paths),
        },
        "supervision": {
            "wall_limit_seconds": runner.WALL_LIMIT_SECONDS,
            "rss_limit_bytes": runner.RSS_LIMIT_BYTES,
            "proof_limit_bytes": runner.PROOF_LIMIT_BYTES,
            "combined_log_limit_bytes": runner.LOG_LIMIT_BYTES,
            "threshold_semantics": "each cap triggers at observed value >= limit",
            "stop_reason": None,
            "wall_seconds": 12.5,
            "sampled_peak_rss_bytes": 100,
            "rss_sample_count": 3,
            "maximum_observed_proof_bytes": proof_bytes,
            "captured_combined_log_bytes": 200,
            "log_limit_reached": False,
            "monitor_error": None,
            "windows_job_object": {
                "assigned": True,
                "process_memory_limit_bytes": runner.RSS_LIMIT_BYTES,
                "kill_on_job_close": True,
                "launch_suspended_until_assignment": True,
            },
        },
        "result": {
            "outcome_reason": "UNSAT_CANDIDATE_CAPTURED",
            "published_proof_bound_to_internal_checkproof": False,
            "independent_lrat_validation": "PENDING",
            "proof_size_matches_solver_log": True,
            "lrat_published": True,
            "discarded_partial_lrat": None,
            "cadical_run_log_markers": {
                "unsatisfiable_status": True,
                "checkproof_option_echoed": True,
                "proof_closed": True,
                "no_cadical_error_diagnostic": True,
                "optional_lrat_checker_statistics_present": False,
            },
            "lrat": {
                "name": runner.artifact_names(spec)["proof"],
                "bytes": proof_bytes,
                "sha256": "A" * 64,
            },
            "metrics": {
                "lrat_added_clauses": 77,
                "lrat_deleted_clauses": 88,
                "solver_reported_lrat_bytes": proof_bytes,
                "conflicts": 3_474,
                "solver_reported_maximum_resident_mib": 1_000.0,
            },
        },
        "published": {
            "artifact_directory": run_paths.report.parent.name,
            "proof": artifact_names["proof"],
            "stdout": artifact_names["stdout"],
            "stderr": artifact_names["stderr"],
            "report": artifact_names["report"],
            "commit": artifact_names["commit"],
        },
        "quarantine": None,
        "threat_model": {
            "workspace": "controlled non-adversarial S: research directory",
            "concurrent_tampering": "out of scope; observed reparse or identity changes fail closed",
            "failed_run_policy": "leave the fresh run directory quarantined; never delete or overwrite it",
        },
        "formal_boundary": {
            "proof_level": "captured certificate candidate only",
            "published_byte_binding": (
                "the published LRAT bytes are not attested as the exact bytes "
                "processed by CaDiCaL's internal checkproof request"
            ),
            "missing": "independent full LRAT audit, Lean replay, and semantic S7 composition",
            "claim_forbidden": "no cover6-d7 theorem or Ramsey-number bound",
        },
    }


def write_run_commit(directory: Path, spec: registry.LeafSpec) -> None:
    run_directory = directory / (
        runner.artifact_names(spec)["directory"] + "." + RUN_ID
    )
    paths = subject.source_paths(directory, spec, run_directory=run_directory)
    artifact_paths = [
        paths["source_lrat"],
        paths["source_stdout"],
        paths["source_stderr"],
        paths["source_report"],
    ]
    artifacts = {path.name: subject.file_metadata(path) for path in artifact_paths}
    payload = {
        "schema_version": 1,
        "status": "COMMITTED_UNSAT_CANDIDATE_CAPTURE",
        "artifact_directory": paths["source_report"].parent.name,
        "selection": materializer.selection_payload(spec),
        "artifacts": artifacts,
        "report": artifacts[paths["source_report"].name],
    }
    paths["source_commit"].write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


class ReducerPreflightTests(unittest.TestCase):
    def test_preflight_is_leaf_specific_and_solver_free(self) -> None:
        result = subject.preflight("FoDPO")
        self.assertEqual(result["status"], "PREFLIGHT_ONLY_NO_S_NO_SOLVER_NO_LEAN")
        self.assertEqual(result["caps"]["core_clauses_max"], 50_000)
        self.assertEqual(result["caps"]["core_cnf_bytes_max"], 32 * 1024 * 1024)
        self.assertEqual(result["caps"]["core_lrat_bytes_max"], 128 * 1024 * 1024)
        self.assertEqual(result["caps"]["lean_wall_seconds"], 600.0)
        self.assertEqual(result["caps"]["lean_family_memory_bytes"], 1_536 * 1024 * 1024)
        self.assertTrue(result["replay"]["launch_suspended_until_job_assignment"])
        self.assertEqual(
            result["outputs"]["core_cnf"],
            "cover6_closed_f7_r34_i7_FoDPO_core.cnf",
        )

    def test_dynamic_names_are_disjoint(self) -> None:
        tables = [subject.names(spec) for spec in registry.ACTIONABLE_LEAVES]
        self.assertEqual(
            len({table["core_cnf"] for table in tables}), len(registry.ACTIONABLE_LEAVES)
        )
        self.assertEqual(
            len({table["source_lrat"] for table in tables}), len(registry.ACTIONABLE_LEAVES)
        )

    def test_lean_temp_must_be_empty_and_disjoint(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            output = root / "output"
            temp = root / "lean-temp"
            for path in (source, output, temp):
                path.mkdir()
            protected = {"source": source, "output": output}
            subject.require_disjoint_source_output(source, output)
            with self.assertRaisesRegex(subject.R34LeafCoreError, "disjoint"):
                subject.require_disjoint_source_output(source, source / "core")
            with self.assertRaisesRegex(subject.R34LeafCoreError, "disjoint"):
                subject.require_disjoint_source_output(source / "run", source)
            subject.require_dedicated_empty_directory(temp, protected)
            self.assertFalse(subject.paths_overlap(temp, source))
            with self.assertRaisesRegex(subject.R34LeafCoreError, "overlaps"):
                subject.require_dedicated_empty_directory(source, protected)
            nested = source / "nested-temp"
            nested.mkdir()
            with self.assertRaisesRegex(subject.R34LeafCoreError, "overlaps"):
                subject.require_dedicated_empty_directory(nested, protected)
            parent = root / "parent-temp"
            protected_child = parent / "protected-child"
            protected_child.mkdir(parents=True)
            with self.assertRaisesRegex(subject.R34LeafCoreError, "overlaps"):
                subject.require_dedicated_empty_directory(
                    parent, {"protected child": protected_child}
                )
            (temp / "pollution.bin").write_bytes(b"mutant")
            with self.assertRaisesRegex(subject.R34LeafCoreError, "empty"):
                subject.require_dedicated_empty_directory(temp, protected)

    def test_caps_accept_boundary_and_reject_plus_one(self) -> None:
        accepted = subject.validate_compact_caps(
            subject.MAX_CORE_CLAUSES,
            subject.MAX_CORE_CNF_BYTES,
            subject.MAX_CORE_LRAT_BYTES,
        )
        self.assertEqual(accepted["status"], "PASS_COMPACT_CORE_CAPS")
        mutants = (
            (subject.MAX_CORE_CLAUSES + 1, 1, 1),
            (1, subject.MAX_CORE_CNF_BYTES + 1, 1),
            (1, 1, subject.MAX_CORE_LRAT_BYTES + 1),
            (-1, 1, 1),
        )
        for values in mutants:
            with self.subTest(values=values):
                with self.assertRaises(subject.R34LeafCoreError):
                    subject.validate_compact_caps(*values)


class RunReportMutantTests(unittest.TestCase):
    def setUp(self) -> None:
        self.spec = registry.select_actionable("FoDPO")

    def test_valid_dynamic_report(self) -> None:
        report = valid_report()
        self.assertNotIn("CHECKED", str(report).upper())
        result = subject.validate_run_report_payload(report, self.spec)
        self.assertEqual(result["proof"]["sha256"], "A" * 64)
        self.assertEqual(result["metrics"]["lrat_added_clauses"], 77)

    def test_semantic_mutants_fail_closed(self) -> None:
        mutations = (
            (("formula", "sha256"), "0" * 64),
            (("selection", "record"), "wrong"),
            (("solver", "returncode"), 0),
            (("solver", "flags"), ["--lrat"]),
            (("supervision", "windows_job_object", "assigned"), False),
            (("supervision", "windows_job_object", "kill_on_job_close"), False),
            (("supervision", "windows_job_object", "process_memory_limit_bytes"), 1),
            (("supervision", "windows_job_object", "launch_suspended_until_assignment"), False),
            (("supervision", "log_limit_reached"), True),
            (("supervision", "monitor_error"), "mutant"),
            (("supervision", "wall_seconds"), runner.WALL_LIMIT_SECONDS),
            (("supervision", "rss_sample_count"), 0),
            (("supervision", "threshold_semantics"), "soft caps"),
            (("result", "cadical_run_log_markers", "proof_closed"), False),
            (("result", "published_proof_bound_to_internal_checkproof"), True),
            (("result", "independent_lrat_validation"), "PASS"),
            (("result", "proof_size_matches_solver_log"), False),
            (("result", "lrat", "sha256"), "a" * 64),
            (("result", "metrics", "lrat_added_clauses"), 0),
            (("result", "metrics", "conflicts"), None),
            (("result", "metrics", "solver_reported_maximum_resident_mib"), None),
            (("published", "artifact_directory"), "mutant.run"),
            (("solver", "command"), ["arbitrary"]),
        )
        for path, value in mutations:
            with self.subTest(path=path):
                report = copy.deepcopy(valid_report())
                target = report
                for key in path[:-1]:
                    target = target[key]  # type: ignore[index,assignment]
                target[path[-1]] = value  # type: ignore[index]
                with self.assertRaises(subject.R34LeafCoreError):
                    subject.validate_run_report_payload(report, self.spec)

    def test_maximum_observed_proof_must_cover_final_proof(self) -> None:
        report = valid_report()
        report["supervision"]["maximum_observed_proof_bytes"] = 12_344  # type: ignore[index]
        with self.assertRaisesRegex(subject.R34LeafCoreError, "below final proof"):
            subject.validate_run_report_payload(report, self.spec)

    def test_at_or_above_runner_caps_is_rejected(self) -> None:
        for key, cap in (
            ("sampled_peak_rss_bytes", runner.RSS_LIMIT_BYTES),
            ("maximum_observed_proof_bytes", runner.PROOF_LIMIT_BYTES),
            ("captured_combined_log_bytes", runner.LOG_LIMIT_BYTES),
        ):
            report = valid_report()
            report["supervision"][key] = cap  # type: ignore[index]
            with self.subTest(key=key):
                with self.assertRaises(subject.R34LeafCoreError):
                    subject.validate_run_report_payload(report, self.spec)

    def test_stdout_is_independently_reparsed_even_if_hash_claim_is_updated(self) -> None:
        proof_payload = b"p" * 12_345
        stdout_payload = (
            b"c option --checkproof=2\n"
            b"s UNSATISFIABLE\n"
            b"c LRAT proof file candidate closed\n"
            b"c LRAT 77 added clauses\n"
            b"c LRAT 88 deleted clauses\n"
            b"c LRAT 12345 bytes\n"
            b"c conflicts: 3474\n"
            b"c maximum resident set size of process: 1000.0 MB\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            run_directory = directory / (
                runner.artifact_names(self.spec)["directory"] + "." + RUN_ID
            )
            run_directory.mkdir()
            paths = subject.source_paths(
                directory, self.spec, run_directory=run_directory
            )
            paths["source_lrat"].write_bytes(proof_payload)
            paths["source_stdout"].write_bytes(stdout_payload)
            paths["source_stderr"].write_bytes(b"")
            report = valid_report()
            solver_path = Path(report["solver"]["path"])  # type: ignore[index]
            report["solver"]["command"] = runner.solver_command(  # type: ignore[index]
                solver_path, runner.run_paths(directory, self.spec, run_id=RUN_ID)
            )
            report["result"]["lrat"] = subject.file_metadata(paths["source_lrat"])  # type: ignore[index]
            report["result"]["metrics"] = subject.frozen_runner.parse_metrics(  # type: ignore[index]
                stdout_payload.decode("ascii")
            )
            report["logs"] = {
                "stdout": subject.file_metadata(paths["source_stdout"]),
                "stderr": subject.file_metadata(paths["source_stderr"]),
            }
            report["supervision"]["captured_combined_log_bytes"] = len(stdout_payload)  # type: ignore[index]
            paths["source_report"].write_text(
                json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            write_run_commit(directory, self.spec)
            with mock.patch.object(subject, "reject_reparse", return_value=None):
                _meta, _dynamic, parsed = subject.verify_run_report(directory, self.spec)
            self.assertEqual(parsed["result"]["metrics"]["conflicts"], 3_474)  # type: ignore[index]

            mutant = stdout_payload.replace(b"candidate closed", b"candidate opened")
            paths["source_stdout"].write_bytes(mutant)
            report["logs"]["stdout"] = subject.file_metadata(paths["source_stdout"])  # type: ignore[index]
            report["supervision"]["captured_combined_log_bytes"] = len(mutant)  # type: ignore[index]
            paths["source_report"].write_text(
                json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            paths["source_commit"].unlink()
            write_run_commit(directory, self.spec)
            with mock.patch.object(subject, "reject_reparse", return_value=None):
                with self.assertRaisesRegex(subject.R34LeafCoreError, "markers"):
                    subject.verify_run_report(directory, self.spec)


class ReplayAndCleanupTests(unittest.TestCase):
    def test_streaming_writer_refuses_first_byte_over_cap(self) -> None:
        stream = io.BytesIO()
        writer = subject._CappedHashingWriter(stream, 3, "mutant")
        writer.write(b"abc")
        with self.assertRaises(subject.R34LeafCoreError):
            writer.write(b"d")
        self.assertEqual(stream.getvalue(), b"abc")

    def test_replay_identifiers_and_axioms_are_exact(self) -> None:
        spec = registry.select_actionable("FoDPO")
        namespace, theorem, qualified = subject.lean_identifiers(spec)
        payload = subject.lean_source(
            spec, Path(r"S:\core\pair.cnf"), Path(r"S:\core\pair.lrat")
        ).decode("utf-8")
        self.assertIn(f"namespace {namespace}", payload)
        self.assertIn(f"lrat_reflect {theorem}", payload)
        good_log = (
            f"'{qualified}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        )
        axioms = subject.parse_axioms(good_log, qualified)
        self.assertTrue(subject.axioms_allowed(axioms, theorem))
        self.assertFalse(subject.axioms_allowed(["sorryAx"], theorem))
        self.assertEqual(subject.parse_axioms(good_log, qualified + "Mutant"), [])

    def test_lean_job_closes_even_when_log_fsync_raises(self) -> None:
        events: list[str] = []

        class FakeProcess:
            pid = 1234
            returncode = 0
            stdout = io.BytesIO(b"")

            def poll(self) -> int:
                return 0

            def wait(self, timeout: float | None = None) -> int:
                return 0

        class FakeJob:
            assigned = False

            def __init__(self, cap: int) -> None:
                self.asserted_cap = cap

            def assign(self, _process: FakeProcess) -> None:
                self.assigned = True

            def peak_memory_bytes(self) -> int:
                return 0

            def close(self) -> None:
                events.append("job-closed")

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            replay = root / "Replay.lean"
            replay.write_text("-- fixture\n", encoding="utf-8")
            log = root / "lean.log.partial"
            with (
                mock.patch.object(subject, "WindowsFamilyJob", FakeJob),
                mock.patch.object(subject.subprocess, "Popen", return_value=FakeProcess()),
                mock.patch.object(subject, "resume_suspended_process", return_value=None),
                mock.patch.object(subject.os, "fsync", side_effect=OSError("fsync mutant")),
            ):
                with self.assertRaisesRegex(OSError, "fsync mutant"):
                    subject._lean_supervised_owned(replay, log, owned={})
            self.assertTrue(log.exists())
        self.assertEqual(events, ["job-closed"])

    def test_production_failure_paths_have_no_unlink_or_rmdir(self) -> None:
        modules = (
            subject,
            runner,
            materializer,
            subject.safety,
        )
        for module in modules:
            with self.subTest(module=module.__name__):
                source = Path(module.__file__).read_text(encoding="utf-8")
                self.assertNotIn(".unlink(", source)
                self.assertNotIn(".rmdir(", source)

    def test_failed_new_write_is_left_quarantined(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "reduction.json.partial"
            ownership: subject.OwnedFiles = {}
            with mock.patch.object(subject.os, "fsync", side_effect=OSError("fsync mutant")):
                with self.assertRaisesRegex(OSError, "fsync mutant"):
                    subject._write_new(path, b"owned bytes", ownership)
            self.assertEqual(path.read_bytes(), b"owned bytes")
            self.assertIn(path, ownership)

    def test_replaced_owned_file_is_rejected_and_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            stage = Path(temporary) / "transaction"
            stage.mkdir()
            path = stage / "reduction.json"
            path.write_bytes(b"ours")
            ownership = {path: subject.safety.regular_file_object_identity(path)}
            path.unlink()
            path.write_bytes(b"foreign replacement")
            with self.assertRaisesRegex(subject.R34LeafCoreError, "replaced"):
                subject._require_owned(path, ownership)
            self.assertEqual(path.read_bytes(), b"foreign replacement")

    def test_discovery_ignores_quarantine_and_requires_one_commit(self) -> None:
        spec = registry.select_actionable("FoDPO")
        prefix = runner.artifact_names(spec)["directory"] + "."
        commit_name = runner.artifact_names(spec)["commit"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            quarantine = root / (prefix + "b" * 32)
            quarantine.mkdir()
            (quarantine / "proof.partial").write_bytes(b"incomplete")
            committed = root / (prefix + "c" * 32)
            committed.mkdir()
            (committed / commit_name).write_bytes(b"{}")
            self.assertEqual(
                subject.discover_committed_run_directory(root, spec), committed
            )
            second = root / (prefix + "d" * 32)
            second.mkdir()
            (second / commit_name).write_bytes(b"{}")
            with self.assertRaisesRegex(subject.R34LeafCoreError, "exactly one"):
                subject.discover_committed_run_directory(root, spec)


class CommitMarkerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.spec = registry.select_actionable("FoDPO")

    def _write_core_commit(self, directory: Path) -> dict[str, Path]:
        paths = subject.output_paths(directory, self.spec)
        for key in subject.CORE_ARTIFACT_KEYS:
            paths[key].write_bytes((key + "\n").encode("ascii"))
        payload = subject._core_commit_payload(directory, self.spec, paths)
        paths["core_commit"].write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        return paths

    @unittest.skipUnless(subject.os.name == "nt", "Windows directory guards are required")
    def test_core_direct_guard_closes_before_marker_rename(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "core"
            output.mkdir()
            partial = output / "CORE_COMMIT.json.partial"
            final = output / "CORE_COMMIT.json"
            partial.write_bytes(b"exact marker")
            guard = subject.WindowsDirectoryGuard(output)
            with guard:
                with self.assertRaises(PermissionError):
                    subject.os.rename(partial, final)
                guard.close()
                subject.os.rename(partial, final)
            self.assertEqual(final.read_bytes(), b"exact marker")
            reducer_source = Path(subject.__file__).read_text(encoding="utf-8")
            self.assertIn("output_guard.close()", reducer_source)

    @unittest.skipUnless(subject.os.name == "nt", "Windows directory guards are required")
    def test_replay_uses_only_rename_compatible_grandparent_guard(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "core"
            replay = output / subject.REPLAY_DIRECTORY_NAME
            replay.mkdir(parents=True)
            partial = replay / "lean.log.partial"
            final = replay / "lean.log"
            partial.write_bytes(b"exact log")
            with subject.WindowsDirectoryGuard(output):
                subject.os.rename(partial, final)
            self.assertEqual(final.read_bytes(), b"exact log")
            reducer_source = Path(subject.__file__).read_text(encoding="utf-8")
            self.assertNotIn(
                "with WindowsDirectoryGuard(replay_directory)", reducer_source
            )

    @unittest.skipUnless(subject.os.name == "nt", "Windows directory guards are required")
    def test_lean_temp_parent_guard_allows_child_rename(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            lean_temp = parent / "lean-temp"
            lean_temp.mkdir()
            partial = lean_temp / "native.partial"
            final = lean_temp / "native.final"
            partial.write_bytes(b"native payload")
            with subject.WindowsDirectoryGuard(lean_temp):
                with self.assertRaises(PermissionError):
                    subject.os.rename(partial, final)
            with subject.WindowsDirectoryGuard(parent):
                subject.os.rename(partial, final)
            self.assertEqual(final.read_bytes(), b"native payload")
            reducer_source = Path(subject.__file__).read_text(encoding="utf-8")
            self.assertNotIn(
                "WindowsDirectoryGuard(temporary_directory),", reducer_source
            )
            self.assertIn(
                "WindowsDirectoryGuard(temporary_directory.parent),", reducer_source
            )

    def test_core_commit_binds_every_byte_and_exact_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "core"
            directory.mkdir()
            paths = self._write_core_commit(directory)
            with mock.patch.object(subject, "reject_reparse", return_value=None):
                subject.verify_core_commit(
                    directory, self.spec, allow_replay_directory=False
                )
                paths["mapping"].write_bytes(b"mutant\n")
                with self.assertRaisesRegex(subject.R34LeafCoreError, "artifact table"):
                    subject.verify_core_commit(
                        directory, self.spec, allow_replay_directory=False
                    )

    def test_foreign_core_entry_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "core"
            directory.mkdir()
            self._write_core_commit(directory)
            (directory / "foreign.bin").write_bytes(b"foreign")
            with mock.patch.object(subject, "reject_reparse", return_value=None):
                with self.assertRaisesRegex(subject.R34LeafCoreError, "inventory"):
                    subject.verify_core_commit(
                        directory, self.spec, allow_replay_directory=False
                    )

    def test_replay_commit_binds_log_manifest_and_exact_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "core"
            output.mkdir()
            paths = subject.output_paths(output, self.spec)
            paths["replay_directory"].mkdir()
            paths["lean_log"].write_bytes(b"log\n")
            paths["manifest"].write_text(
                json.dumps(
                    {
                        "status": "LEAN_REPLAY_PASS",
                        "validation": {
                            "lean": {
                                "status": "LEAN_LRAT_REPLAY_PASS",
                                "axioms_allowed": True,
                            },
                            "post_replay_identity": {
                                "compact_artifacts_unchanged": True,
                                "source_artifacts_unchanged": True,
                                "lean_lratcatcher_stack_unchanged": True,
                                "lean_log_matches_exclusive_capture": True,
                                "temporary_directory_empty_after_replay": True,
                            },
                        },
                    },
                    sort_keys=True,
                )
                + "\n",
                encoding="utf-8",
            )
            payload = {
                "schema_version": 1,
                "status": "COMMITTED_LEAN_REPLAY_PASS",
                "artifact_directory": paths["replay_directory"].name,
                "selection": materializer.selection_payload(self.spec),
                "artifacts": {
                    paths[key].name: subject.file_metadata(paths[key], lines=True)
                    for key in ("lean_log", "manifest")
                },
            }
            paths["replay_commit"].write_text(
                json.dumps(payload, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with mock.patch.object(subject, "reject_reparse", return_value=None):
                subject.verify_replay_commit(output, self.spec)
                manifest = json.loads(
                    paths["manifest"].read_text(encoding="utf-8")
                )
                manifest["validation"]["post_replay_identity"][
                    "temporary_directory_empty_after_replay"
                ] = False
                paths["manifest"].write_text(
                    json.dumps(manifest, sort_keys=True) + "\n", encoding="utf-8"
                )
                payload["artifacts"] = {
                    paths[key].name: subject.file_metadata(paths[key], lines=True)
                    for key in ("lean_log", "manifest")
                }
                paths["replay_commit"].write_text(
                    json.dumps(payload, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    subject.R34LeafCoreError, "identity anchors"
                ):
                    subject.verify_replay_commit(output, self.spec)
                paths["manifest"].write_bytes(b"mutant\n")
                with self.assertRaisesRegex(subject.R34LeafCoreError, "artifact table"):
                    subject.verify_replay_commit(output, self.spec)

    def test_replay_commit_cannot_promote_a_failed_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "core"
            output.mkdir()
            paths = subject.output_paths(output, self.spec)
            paths["replay_directory"].mkdir()
            paths["lean_log"].write_bytes(b"failed log\n")
            paths["manifest"].write_text(
                json.dumps(
                    {
                        "status": "LEAN_REPLAY_FAILED",
                        "validation": {"lean": {"status": "LEAN_LRAT_REPLAY_FAILED"}},
                    },
                    sort_keys=True,
                )
                + "\n",
                encoding="utf-8",
            )
            payload = {
                "schema_version": 1,
                "status": "COMMITTED_LEAN_REPLAY_PASS",
                "artifact_directory": paths["replay_directory"].name,
                "selection": materializer.selection_payload(self.spec),
                "artifacts": {
                    paths[key].name: subject.file_metadata(paths[key], lines=True)
                    for key in ("lean_log", "manifest")
                },
            }
            paths["replay_commit"].write_text(
                json.dumps(payload, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with mock.patch.object(subject, "reject_reparse", return_value=None):
                with self.assertRaisesRegex(subject.R34LeafCoreError, "not an exact replay PASS"):
                    subject.verify_replay_commit(output, self.spec)


if __name__ == "__main__":
    unittest.main()
