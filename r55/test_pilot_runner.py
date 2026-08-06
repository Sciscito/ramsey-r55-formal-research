import json
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

from pilot_runner import (
    Journal,
    classify_solver_result,
    completed_run_ids,
    decode_solver_bytes,
    deterministic_sample,
    effective_job_count,
    parse_solver_output,
    repair_truncated_journal_tail,
)


HERE = Path(__file__).resolve().parent


class PilotRunnerTests(unittest.TestCase):
    def test_status_classification_is_conservative(self):
        self.assertEqual(classify_solver_result(20, "UNSAT"), ("UNSAT", "cadical_exit_code"))
        self.assertEqual(classify_solver_result(0, None), ("UNKNOWN", "cadical_exit_code"))
        self.assertEqual(classify_solver_result(0, "UNKNOWN"), ("UNKNOWN", "cadical_exit_code"))
        status, reason = classify_solver_result(0, "UNSAT")
        self.assertEqual(status, "ERROR")
        self.assertIn("mismatch", reason)

    def test_output_parser_uses_last_statistics(self):
        parsed = parse_solver_output(
            "s UNKNOWN\n"
            "c conflicts: 100 1 per second\n"
            "c conflicts: 123 2 per second\n"
            "c total real time since initialization: 1.25 seconds\n"
            "c maximum resident set size of process: 12.50 MB\n"
        )
        self.assertEqual(parsed["reported_status"], "UNKNOWN")
        self.assertEqual(parsed["conflicts"], 123)
        self.assertEqual(parsed["solver_real_seconds"], 1.25)
        self.assertEqual(parsed["reported_max_rss_mb"], 12.5)

    def test_utf16_solver_log_is_decoded(self):
        text = "c conflicts: 456 3 per second\r\nc maximum resident set size of process: 21.25 MB\r\n"
        parsed = parse_solver_output(decode_solver_bytes(text.encode("utf-16")))
        self.assertEqual(parsed["conflicts"], 456)
        self.assertEqual(parsed["reported_max_rss_mb"], 21.25)

    def test_deterministic_stratified_sample_ignores_input_order(self):
        branches = [
            {"id": f"d{degree}_c{codegree}_t{index}", "degree": degree, "codegree": codegree}
            for degree, codegree in ((18, 0), (18, 1), (20, 2))
            for index in range(4)
        ]
        first = deterministic_sample(branches, 6, "seed")
        second = deterministic_sample(list(reversed(branches)), 6, "seed")
        self.assertEqual([item["id"] for item in first], [item["id"] for item in second])
        self.assertEqual({(item["degree"], item["codegree"]) for item in first}, {(18, 0), (18, 1), (20, 2)})
        tiny = deterministic_sample(branches, 2, "seed")
        self.assertEqual({item["degree"] for item in tiny}, {18, 20})

    def test_memory_budget_caps_workers(self):
        self.assertEqual(effective_job_count(28, 18_000, 600), 28)
        self.assertEqual(effective_job_count(28, 8_400, 600), 14)
        with self.assertRaises(ValueError):
            effective_job_count(28, 500, 600)

    def test_truncated_last_journal_record_is_recoverable(self):
        with tempfile.TemporaryDirectory() as temporary:
            journal_path = Path(temporary) / "results.jsonl"
            complete = {"event": "result", "run_id": "done", "status": "UNKNOWN"}
            journal_path.write_text(json.dumps(complete) + "\n{\"event\":", encoding="utf-8")
            self.assertEqual(completed_run_ids(journal_path), {"done"})
            sidecar = repair_truncated_journal_tail(journal_path)
            self.assertIsNotNone(sidecar)
            Journal(journal_path).append({"event": "start", "run_id": "next"})
            records = [json.loads(line) for line in journal_path.read_text(encoding="utf-8").splitlines()]
            self.assertEqual([record["run_id"] for record in records], ["done", "next"])

    def test_end_to_end_unknown_is_journaled_and_resumed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            catalogue = root / "r35_0.g6"
            catalogue.write_text("?\n", encoding="ascii")
            import hashlib

            catalogue_hash = hashlib.sha256(catalogue.read_bytes()).hexdigest()
            manifest = root / "manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "host_order": 6,
                        "forbidden_clique": 3,
                        "branch_count": 1,
                        "catalogue_directory": ".",
                        "branches": [
                            {
                                "id": "d2_c0_t0",
                                "degree": 2,
                                "codegree": 0,
                                "type_index": 0,
                                "catalogue": catalogue.name,
                                "catalogue_sha256": catalogue_hash,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            fake_solver = root / "fake_cadical.py"
            fake_solver.write_text(
                textwrap.dedent(
                    """\
                    import sys
                    print("s UNKNOWN")
                    print("c conflicts: 123 2 per second")
                    print("c total real time since initialization: 0.01 seconds")
                    print("c maximum resident set size of process: 12.50 MB")
                    raise SystemExit(0)
                    """
                ),
                encoding="utf-8",
            )
            journal = root / "results.jsonl"
            command = [
                sys.executable,
                str(HERE / "pilot_runner.py"),
                "--manifest",
                str(manifest),
                "--ramsey-script",
                str(HERE / "ramsey.py"),
                "--cadical",
                sys.executable,
                f"--cadical-option={fake_solver}",
                "--branch",
                "d2_c0_t0",
                "--conflicts",
                "123",
                "--jobs",
                "1",
                "--output",
                str(journal),
                "--work-dir",
                str(root / "work"),
            ]
            first = subprocess.run(command, text=True, capture_output=True, check=False)
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            second = subprocess.run(command, text=True, capture_output=True, check=False)
            self.assertEqual(second.returncode, 0, second.stdout + second.stderr)

            records = [json.loads(line) for line in journal.read_text(encoding="utf-8").splitlines()]
            results = [record for record in records if record["event"] == "result"]
            self.assertEqual(len(results), 1)
            result = results[0]
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertEqual(result["conflicts"], 123)
            self.assertEqual(result["reported_max_rss_mb"], 12.5)
            self.assertRegex(result["cnf_sha256"], r"^[0-9a-f]{64}$")
            self.assertIn('"skipped_completed": 1', second.stdout)


if __name__ == "__main__":
    unittest.main()
