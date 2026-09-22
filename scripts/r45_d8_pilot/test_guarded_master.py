#!/usr/bin/env python3
"""Solver-free regression tests for the degree-eight guarded master CNF."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "generate_guarded_master.py"
SPEC = importlib.util.spec_from_file_location("tested_r45_d8_guarded_master", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
master = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = master
SPEC.loader.exec_module(master)


class GuardedMasterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = master.build_result()

    def test_exact_master_dimensions(self) -> None:
        metadata = self.result["metadata"]
        self.assertEqual(metadata["cnf"]["variables"], 282)
        self.assertEqual(metadata["cnf"]["clauses"], 55_926)
        self.assertEqual(
            metadata["cnf"]["clause_breakdown"],
            {
                "fixed_root_base": 55_006,
                "guarded_gen358_units": 675,
                "guarded_gen4416_units": 240,
                "invalid_gen358_codes": 5,
            },
        )

    def test_binary_selector_convention_and_invalid_codes(self) -> None:
        self.assertEqual(
            master.selector_cube(0, master.LEFT_SELECTOR_VARIABLES),
            (-277, -278, -279, -280, -281),
        )
        self.assertEqual(
            master.selector_cube(26, master.LEFT_SELECTOR_VARIABLES),
            (-277, 278, -279, 280, 281),
        )
        self.assertEqual(
            master.selector_cube(1, master.RIGHT_SELECTOR_VARIABLES),
            (282,),
        )
        self.assertEqual(len(self.result["invalid_left_clauses"]), 5)
        for code, blocker in zip(
            master.INVALID_LEFT_CODES,
            self.result["invalid_left_clauses"],
            strict=True,
        ):
            cube = master.selector_cube(code, master.LEFT_SELECTOR_VARIABLES)
            assignment = {abs(literal): literal > 0 for literal in cube}
            self.assertFalse(
                any(assignment[abs(literal)] == (literal > 0) for literal in blocker)
            )
            for valid_code in range(master.LEFT_RECORD_COUNT):
                valid_cube = master.selector_cube(
                    valid_code, master.LEFT_SELECTOR_VARIABLES
                )
                valid_assignment = {
                    abs(literal): literal > 0 for literal in valid_cube
                }
                self.assertTrue(
                    any(
                        valid_assignment[abs(literal)] == (literal > 0)
                        for literal in blocker
                    )
                )

    def test_all_54_specializations_match_recorded_leaf_dimacs(self) -> None:
        audit = self.result["metadata"]["specialization_audit"]
        self.assertTrue(audit["all_54_clause_sequences_equal_direct_leaf"])
        self.assertTrue(audit["all_54_dimacs_hashes_match_recorded_leaf_hashes"])
        cubes = self.result["valid_leaf_rows"]
        self.assertEqual(len(cubes), 54)
        self.assertEqual(len({tuple(row["cube"]) for row in cubes}), 54)
        self.assertTrue(all(row["cube_type"] == "valid_leaf" for row in cubes))
        self.assertEqual(audit["minimum_specialized_units"], 144)
        self.assertEqual(audit["maximum_specialized_units"], 148)
        self.assertEqual(audit["minimum_specialized_clauses"], 55_150)
        self.assertEqual(audit["maximum_specialized_clauses"], 55_154)

    def test_cover_icnf_round_trip_and_proof_order(self) -> None:
        cubes = self.result["cover_cubes"]
        rows = self.result["cover_rows"]
        self.assertEqual(len(cubes), 59)
        self.assertEqual(master.parse_icnf_bytes(self.result["cover_icnf_bytes"]), cubes)
        self.assertEqual(
            [row["cover_index_one_based"] for row in rows],
            list(range(1, 60)),
        )
        self.assertTrue(all(len(cube) == 6 for cube in cubes[:54]))
        self.assertTrue(all(len(cube) == 5 for cube in cubes[54:]))
        self.assertEqual(
            [row["cube_type"] for row in rows[:54]],
            ["valid_leaf"] * 54,
        )
        self.assertEqual(
            [row["gen358_invalid_code"] for row in rows[54:]],
            [27, 28, 29, 30, 31],
        )
        self.assertEqual(
            [row["cube_type"] for row in rows[54:]],
            ["invalid_gen358_code"] * 5,
        )

    def test_59_cubes_partition_all_64_selector_assignments(self) -> None:
        rows = self.result["cover_rows"]
        checked = 0
        for left_code in range(32):
            for right_code in range(2):
                full_cube = (
                    master.selector_cube(left_code, master.LEFT_SELECTOR_VARIABLES)
                    + master.selector_cube(right_code, master.RIGHT_SELECTOR_VARIABLES)
                )
                assignment = {
                    abs(literal): literal > 0 for literal in full_cube
                }
                matches = [
                    row for row in rows
                    if master.cube_matches_assignment(row["cube"], assignment)
                ]
                self.assertEqual(len(matches), 1)
                if left_code < 27:
                    self.assertEqual(matches[0]["cube_type"], "valid_leaf")
                    self.assertEqual(
                        matches[0]["cover_index_one_based"],
                        2 * left_code + right_code + 1,
                    )
                else:
                    self.assertEqual(
                        matches[0]["cube_type"], "invalid_gen358_code"
                    )
                    self.assertEqual(
                        matches[0]["cover_index_one_based"],
                        55 + left_code - 27,
                    )
                checked += 1
        self.assertEqual(checked, 64)

    def test_invalid_cubes_are_blocked_and_negated_cover_is_false(self) -> None:
        cubes = self.result["cover_cubes"]
        negated = self.result["negated_cover_clauses"]
        self.assertEqual(
            negated,
            tuple(tuple(-literal for literal in cube) for cube in cubes),
        )
        self.assertEqual(
            self.result["negated_cover_cnf_bytes"].splitlines()[0],
            b"p cnf 282 59",
        )
        invalid_rows = self.result["cover_rows"][54:]
        for row in invalid_rows:
            self.assertEqual(
                tuple(row["blocking_clause"]),
                tuple(-literal for literal in row["cube"]),
            )
            self.assertEqual(
                self.result["master_clauses"][
                    row["blocking_clause_index_one_based"] - 1
                ],
                tuple(row["blocking_clause"]),
            )

        for left_code in range(32):
            for right_code in range(2):
                full_cube = (
                    master.selector_cube(left_code, master.LEFT_SELECTOR_VARIABLES)
                    + master.selector_cube(right_code, master.RIGHT_SELECTOR_VARIABLES)
                )
                assignment = {
                    abs(literal): literal > 0 for literal in full_cube
                }
                cnf_value = all(
                    any(
                        assignment[abs(literal)] == (literal > 0)
                        for literal in clause
                    )
                    for clause in negated
                )
                self.assertFalse(cnf_value)
    def test_proof_scope_is_not_overstated(self) -> None:
        proof = self.result["metadata"]["proof_artifacts"]
        self.assertEqual(proof["lrat_files_present"], 1)
        self.assertEqual(proof["lrat_leaves"], ["d8_l22_r01"])
        self.assertEqual(proof["cover_leaf_certificates_required"], 59)
        self.assertTrue(proof["cover_certificate_required"])
        self.assertEqual(proof["missing_valid_direct_leaf_lrat_count"], 53)
        self.assertEqual(proof["invalid_code_leaf_lrat_present"], 0)
        self.assertIn("No cover LRAT", proof["warning"])
        leaf_formula = self.result["metadata"]["cube_manifest"][
            "leaf_certificate_formula"
        ]
        self.assertEqual(
            leaf_formula["clause_order"],
            "cube unit clauses first, then guarded_master clauses",
        )
        self.assertIn("not byte-identical", leaf_formula["warning"])

    def test_artifacts_round_trip_without_solver(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            report = master.generate(output)
            self.assertEqual(report["status"], "PASS")
            self.assertEqual(report["master_variables"], 282)
            self.assertEqual(report["master_clauses"], 55_926)
            self.assertEqual(report["cover_cubes"], 59)
            self.assertEqual(report["valid_leaf_cubes"], 54)
            self.assertEqual(master.verify(output)["master_sha256"], report["master_sha256"])


if __name__ == "__main__":
    unittest.main()
