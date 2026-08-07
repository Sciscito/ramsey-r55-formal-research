#!/usr/bin/env python3
"""Small deterministic tests for the conditioned d12 cover probe."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "conditioned_cover_probe.py"
SPEC = importlib.util.spec_from_file_location("tested_d12_conditioned_cover", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
probe = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = probe
SPEC.loader.exec_module(probe)


class ConditionedCoverProbeTests(unittest.TestCase):
    def test_ssd_guard_rejects_relative_and_other_drives(self) -> None:
        for path in (Path("relative"), Path(r"S:relative"), Path(r"C:\probe")):
            with self.assertRaises(ValueError):
                probe.require_absolute_ssd(path)
        self.assertEqual(
            str(probe.require_absolute_ssd(Path(r"S:\probe"))), r"S:\probe"
        )

    def test_parent_specification(self) -> None:
        self.assertEqual(probe.parse_parent_specification("3,1-2,2"), (1, 2, 3))
        with self.assertRaises(ValueError):
            probe.parse_parent_specification("0")

    def test_parent_unit_mapping_and_polarity(self) -> None:
        colours = [0] * 66
        colours[0] = 1
        colours[-1] = 2
        self.assertEqual(
            probe.parent_units(colours, "complemented"), (211, -276)
        )
        self.assertEqual(probe.parent_units(colours, "raw"), (-211, 276))
        with self.assertRaises(probe.ProbeError):
            probe.parent_units([3] + [0] * 65, "complemented")

    def test_core_requirements_are_orientation_explicit(self) -> None:
        complemented = probe.core_requirements((211, -276), "complemented")
        raw = probe.core_requirements((211, -276), "raw")
        self.assertEqual((complemented[0], complemented[-1]), (1, 2))
        self.assertEqual((raw[0], raw[-1]), (2, 1))

    def test_solver_output_parser(self) -> None:
        output = (
            "c conflicts:                 1234\n"
            "s UNSATISFIABLE\n"
            "c total process time since initialization: 1.25 seconds\n"
        )
        self.assertEqual(
            probe.parse_solver_output(output, 20), ("UNSAT", 1234, 1.25)
        )

    def test_conditioned_header_and_units(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "leaf.cnf"
            clauses = b"".join(b"1 0\n" for _ in range(probe.EXPECTED_BASE_CLAUSES))
            path.write_bytes(
                f"p cnf {probe.BASE_VARIABLES} {probe.EXPECTED_BASE_CLAUSES}\n".encode("ascii")
                + clauses
            )
            rendered = probe.conditioned_cnf_bytes(path, (211, -276))
            self.assertTrue(
                rendered.startswith(
                    f"p cnf 276 {probe.EXPECTED_BASE_CLAUSES + 2}\n".encode("ascii")
                )
            )
            self.assertTrue(rendered.endswith(b"211 0\n-276 0\n"))

    def test_lrat_dependency_core_is_backward_and_sign_conservative(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / "synthetic.lrat"
            proof.write_bytes(
                b"14 5 0 11 2 0\n"
                b"15 -5 0 12 3 0\n"
                b"16 7 0 13 4 0\n"
                b"17 d 16 0\n"
                b"18 0 14 -15 0\n"
            )
            core, stats = probe.extract_initial_unit_core(
                proof, base_clause_count=10, units=(211, -212, 213)
            )
            self.assertEqual(core, (211, -212))
            self.assertEqual(stats["reachable_derived_clauses"], 3)
            self.assertEqual(stats["referenced_appended_units"], 2)

    def test_exact_permutation_checker(self) -> None:
        pairs = probe.cover.edge_pairs(probe.B_ORDER)
        requirements = [0] * len(pairs)
        for edge in ((0, 1), (0, 2), (1, 2)):
            requirements[pairs.index(edge)] = 1
        all_colour2 = [2] * len(pairs)
        self.assertFalse(probe.has_permuted_extension(all_colour2, requirements))
        target = list(all_colour2)
        for edge in ((3, 4), (3, 5), (4, 5)):
            target[pairs.index(edge)] = 1
        self.assertTrue(probe.has_permuted_extension(target, requirements))

    def test_stored_orientation_uses_normal_to_original_permutation(self) -> None:
        pairs = probe.cover.edge_pairs(probe.B_ORDER)
        requirements = [0] * len(pairs)
        requirements[pairs.index((0, 2))] = 1
        child = [2] * len(pairs)
        child[pairs.index((1, 2))] = 1
        permutation = [1, 0, *range(2, probe.B_ORDER)]
        self.assertTrue(
            probe.child_orientation_extends_requirements(
                child, permutation, requirements
            )
        )
        child[pairs.index((1, 2))] = 2
        self.assertFalse(
            probe.child_orientation_extends_requirements(
                child, permutation, requirements
            )
        )

    def test_wilson_interval_contains_observed_proportion(self) -> None:
        lower, upper = probe.wilson_interval(17, 995)
        self.assertLess(lower, 17 / 995)
        self.assertGreater(upper, 17 / 995)
        self.assertGreaterEqual(lower, 0.0)
        self.assertLessEqual(upper, 1.0)

if __name__ == "__main__":
    unittest.main()
