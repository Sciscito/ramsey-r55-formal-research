#!/usr/bin/env python3
"""Solver-free checks for the degree-twelve guarded-cover LRAT adapter."""

from __future__ import annotations

import importlib.util
import os
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "run_guarded_cover_lrat.py"
SPEC = importlib.util.spec_from_file_location("tested_r45_d12_runner", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
runner = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = runner
SPEC.loader.exec_module(runner)

FORMULA_ENV = os.environ.get("R45_D12_FORMULA_DIR")
FORMULA = Path(FORMULA_ENV) if FORMULA_ENV else Path("__missing_d12_formula__")


class DegreeTwelveGuardedCoverRunnerTests(unittest.TestCase):
    def test_ssd_guard_requires_absolute_s_path(self) -> None:
        accepted = runner.require_explicit_ssd_path(
            Path(r"S:\CodexResearchCache\ramsey-formal\runner-test")
        )
        self.assertEqual(accepted.drive.upper(), "S:")
        for rejected in (
            Path(r"C:\forbidden"),
            Path(r"S:relative-output"),
            Path("relative-output"),
        ):
            with self.assertRaises(runner.RunnerError):
                runner.require_explicit_ssd_path(rejected)

    def test_index_parser_is_exactly_thirteen_leaves(self) -> None:
        self.assertEqual(runner.parse_indices(None), list(range(1, 14)))
        self.assertEqual(runner.parse_indices(["1,3-5", "13"]), [1, 3, 4, 5, 13])
        for rejected in (["0"], ["14"], ["5-3"]):
            with self.assertRaises(runner.RunnerError):
                runner.parse_indices(rejected)

    @unittest.skipUnless(FORMULA.is_dir(), "generated formula is intentionally SSD-only")
    def test_generated_ssd_bundle_has_frozen_dimensions_and_order(self) -> None:
        bundle = runner.load_sources(FORMULA)
        self.assertEqual(bundle.master_variables, 280)
        self.assertEqual(bundle.master_clauses, 54_638)
        self.assertEqual(len(bundle.cubes), 13)
        self.assertEqual(
            [row["cover_index_one_based"] for row in bundle.cover_rows],
            list(range(1, 14)),
        )
        self.assertEqual(len(bundle.cubes[-1]), 2)
        self.assertEqual(
            bundle.master_sha256,
            "0F5049E4D2A7B465E33BA852170477711CA63220ED6F2DAD1542C558D4D8BFA8",
        )

    @unittest.skipUnless(FORMULA.is_dir(), "generated formula is intentionally SSD-only")
    def test_leaf_layout_is_cube_units_then_exact_master(self) -> None:
        bundle = runner.load_sources(FORMULA)
        data = runner.base.leaf_cnf_bytes(bundle, 1)
        lines = data.splitlines(keepends=True)
        self.assertEqual(lines[0], b"p cnf 280 54642\n")
        self.assertEqual(
            lines[1:5],
            [f"{literal} 0\n".encode("ascii") for literal in bundle.cubes[0]],
        )
        self.assertEqual(b"".join(lines[5:]), bundle.master_body)

    def test_reused_solver_command_keeps_lrat_flags(self) -> None:
        command = runner.base.solver_command(
            Path("cadical"), Path("leaf_1.cnf"), Path("leaf_1.lrat"), 123
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
                "123",
                "leaf_1.cnf",
                "leaf_1.lrat",
            ],
        )


if __name__ == "__main__":
    unittest.main()
