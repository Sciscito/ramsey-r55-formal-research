#!/usr/bin/env python3
"""Solver-free tests for the resumable guarded-cover LRAT runner."""

from __future__ import annotations

import importlib.util
import io
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "run_guarded_cover_lrat.py"
SPEC = importlib.util.spec_from_file_location("tested_guarded_cover_runner", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
runner = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = runner
SPEC.loader.exec_module(runner)


class GuardedCoverRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.bundle = runner.load_sources()

    def assert_leaf_layout(self, index: int, expected_cube_length: int) -> None:
        data = runner.leaf_cnf_bytes(self.bundle, index)
        lines = data.splitlines(keepends=True)
        self.assertEqual(
            lines[0],
            (
                f"p cnf 282 {runner.EXPECTED_MASTER_CLAUSES + expected_cube_length}\n"
            ).encode("ascii"),
        )
        cube = self.bundle.cubes[index - 1]
        self.assertEqual(len(cube), expected_cube_length)
        self.assertEqual(
            lines[1 : 1 + expected_cube_length],
            [f"{literal} 0\n".encode("ascii") for literal in cube],
        )
        self.assertEqual(
            b"".join(lines[1 + expected_cube_length :]),
            self.bundle.master_body,
        )

    def test_valid_leaf_is_cube_units_then_master(self) -> None:
        self.assert_leaf_layout(1, 6)
        self.assertEqual(
            self.bundle.cover_rows[0]["cube_type"], "valid_leaf"
        )

    def test_invalid_leaf_is_five_units_then_master(self) -> None:
        self.assert_leaf_layout(55, 5)
        row = self.bundle.cover_rows[54]
        self.assertEqual(row["cube_type"], "invalid_gen358_code")
        self.assertEqual(row["gen358_invalid_code"], 27)
        self.assertEqual(
            tuple(row["blocking_clause"]),
            tuple(-literal for literal in self.bundle.cubes[54]),
        )

    def test_cover_order_and_prefix_names_are_exact(self) -> None:
        jobs = runner.build_jobs(self.bundle, list(range(1, 60)), include_cover=True)
        self.assertEqual([job.stem for job in jobs[:3]], ["leaf_1", "leaf_2", "leaf_3"])
        self.assertEqual(jobs[53].stem, "leaf_54")
        self.assertEqual(jobs[54].stem, "leaf_55")
        self.assertEqual(jobs[58].stem, "leaf_59")
        self.assertEqual(jobs[59].stem, "cover")
        self.assertEqual(
            [row["cover_index_one_based"] for row in self.bundle.cover_rows],
            list(range(1, 60)),
        )

    def test_solver_command_has_required_lrat_flags_and_order(self) -> None:
        command = runner.solver_command(
            Path("cadical"), Path("leaf_1.cnf"), Path("leaf_1.lrat"), 12345
        )
        self.assertEqual(
            command,
            [
                "cadical",
                "--lrat",
                "--no-binary",
                "--unsat",
                "--walk=false",
                "-c",
                "12345",
                "leaf_1.cnf",
                "leaf_1.lrat",
            ],
        )

    def test_dry_run_plan_never_invokes_subprocess(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            with mock.patch.object(
                runner.subprocess,
                "run",
                side_effect=AssertionError("dry-run planning invoked subprocess"),
            ):
                plan = runner.build_dry_run_plan(
                    self.bundle,
                    Path("cadical"),
                    output,
                    [1, 55],
                    include_cover=True,
                    conflicts=None,
                )
        self.assertEqual(plan["status"], "DRY_RUN_NO_SOLVER_INVOKED")
        self.assertEqual([job["stem"] for job in plan["jobs"]], [
            "leaf_1", "leaf_55", "cover"
        ])
        self.assertEqual(plan["jobs"][0]["input_clause_count"], 55_932)
        self.assertEqual(plan["jobs"][1]["input_clause_count"], 55_931)
        self.assertEqual(plan["jobs"][2]["input_clause_count"], 59)

    def test_dry_run_cli_writes_only_atomic_plan(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            solver = root / "cadical-mock"
            solver.write_bytes(b"not executed")
            output = root / "external-output"
            args = SimpleNamespace(
                artifacts=runner.DEFAULT_ARTIFACTS,
                output=output,
                solver=solver,
                jobs=1,
                conflicts=None,
                timeout=None,
                cover_only=False,
                skip_cover=False,
                only=["1,55"],
                dry_run=True,
                verify_bundle=False,
                keep_cnfs=False,
            )
            with mock.patch.object(
                runner.subprocess,
                "run",
                side_effect=AssertionError("dry-run CLI invoked subprocess"),
            ), redirect_stdout(io.StringIO()):
                self.assertEqual(runner.run(args), 0)
            plan_path = output / "dry_run_plan.json"
            self.assertTrue(plan_path.is_file())
            self.assertFalse(any(output.glob("*.cnf")))
            self.assertFalse(any(output.glob("*.lrat")))
    def test_filters_and_external_output_guard(self) -> None:
        self.assertEqual(runner.parse_indices(["1,3-5", "59"]), [1, 3, 4, 5, 59])
        with self.assertRaises(runner.RunnerError):
            runner.ensure_external_output(HERE / "guarded_master" / "runner-output")
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(
                runner.ensure_external_output(Path(directory)),
                Path(directory).resolve(),
            )

    def test_tracked_proof_bundle_manifest_is_exact(self) -> None:
        manifest = runner.load_proof_bundle_manifest(self.bundle)
        self.assertEqual(manifest["bundle"]["lrat_files"], 60)
        self.assertEqual(manifest["bundle"]["leaf_lrat_files"], 59)
        self.assertEqual(manifest["bundle"]["cover_lrat_files"], 1)
        self.assertEqual(manifest["bundle"]["total_lrat_bytes"], 2_405_113_598)
        self.assertEqual(manifest["files"][0]["name"], "leaf_1.lrat")
        self.assertEqual(manifest["files"][-2]["name"], "leaf_59.lrat")
        self.assertEqual(manifest["files"][-1]["name"], "cover.lrat")

    def test_bundle_verification_rejects_missing_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(runner.RunnerError):
                runner.verify_proof_bundle(self.bundle, Path(directory))


if __name__ == "__main__":
    unittest.main()
