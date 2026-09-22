#!/usr/bin/env python3
"""Solver-free deterministic tests for the red-degree-12 guarded master."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "generate_guarded_master.py"
SPEC = importlib.util.spec_from_file_location(
    "tested_r45_d12_guarded_master", MODULE_PATH
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
master = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = master
SPEC.loader.exec_module(master)


EXPECTED_LEAF_HASHES = [
    "3C01B8B4B863174D655804B7DAE162D51166E4142D07101CDE4925246D71A54E",
    "0C3DEE182FC99D960B89D291B53B9C67D7B0FB17A99294E8CB65EB76AA26547C",
    "5BF05A59558DEBB90CE89C619140F225FC14BE69E6D25D43163D77F3C060B86E",
    "7587124E82253B21799B6D575398996E0B3B2ABD9C820617A825AD84B0E14939",
    "39DE12652E1E732F47D00A0C253065A38984A8E73A3DAB821CE8626C60C335EC",
    "B18DB188F52D607E669BE1A1A941D5B2F9FA3F46B9828E80A8F2DC184B943A68",
    "EC138CA02A6F28A37ADCC90BBAA229F75DFADBFCDFD74AB785C365116542C32B",
    "41063B57071B077202C15FEB39C306AC529B10C109F63D0DEECC8F455EB3A2D9",
    "87B1BA4AEA6651794C8A6740B5E92459A2D9F68273193397A0EFBBFD56EAA2F7",
    "5A5FCE99CE4BF87426CC14083EEC4FF5E728955C06E1B11853CA10D346D21EF9",
    "466A88C25B5E621676B98E3E14EAC254BCAD82ACC7ED23B91E1C9BAF845F5426",
    "F9D37D3B235AC8BA407957E59B7FB60CE37549604F734F91799AAE8A095301D9",
]


class GuardedMasterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = master.build_result()

    def test_exact_master_dimensions(self) -> None:
        cnf = self.result["metadata"]["cnf"]
        self.assertEqual(cnf["base_variables"], 276)
        self.assertEqual(cnf["variables"], 280)
        self.assertEqual(cnf["clauses"], 54_638)
        self.assertEqual(cnf["bytes"], 1_968_652)
        self.assertEqual(
            cnf["clause_breakdown"],
            {
                "global_no_red_K4": 10_626,
                "global_no_blue_K5": 42_504,
                "red_neighbour_no_red_K3": 220,
                "blue_neighbour_no_blue_K4": 495,
                "guarded_r35_order12_units": 792,
                "invalid_dyadic_blockers": 1,
            },
        )
        self.assertEqual(len(self.result["base_clauses"]), 53_845)
        self.assertEqual(len(self.result["master_clauses"]), 54_638)

    def test_certified_order12_catalogue_and_complete_units(self) -> None:
        self.assertEqual(len(self.result["catalogue"]), 12)
        self.assertEqual(len(self.result["catalogue_units"]), 12)
        self.assertEqual(
            self.result["metadata"]["catalogue"]["source_sha256"],
            "322E7A54E67F4201BD37998AB420AFB3EEE41B1DCD6B277B7F055BDA152DA95E",
        )
        for units in self.result["catalogue_units"]:
            self.assertEqual(len(units), 66)
            self.assertEqual(len(set(map(abs, units))), 66)
            self.assertEqual(
                set(map(abs, units)),
                {
                    master.edge_var(24, left, right)
                    for left in range(12)
                    for right in range(left + 1, 12)
                },
            )

    def test_little_endian_selectors_and_single_invalid_blocker(self) -> None:
        self.assertEqual(master.SELECTOR_VARIABLES, (277, 278, 279, 280))
        self.assertEqual(master.selector_cube(0), (-277, -278, -279, -280))
        self.assertEqual(master.selector_cube(11), (277, 278, -279, 280))
        self.assertEqual(master.INVALID_CODE_CUBE, (279, 280))
        self.assertEqual(master.INVALID_CODE_BLOCKER, (-279, -280))
        self.assertEqual(self.result["invalid_blocker"], (-279, -280))

        for code in range(16):
            assignment = {
                abs(literal): literal > 0 for literal in master.selector_cube(code)
            }
            blocker_value = any(
                assignment[abs(literal)] == (literal > 0)
                for literal in master.INVALID_CODE_BLOCKER
            )
            self.assertEqual(blocker_value, code < 12)

    def test_all_specializations_are_exact_direct_catalogue_leaves(self) -> None:
        rows = self.result["valid_leaf_rows"]
        self.assertEqual(len(rows), 12)
        self.assertEqual(
            [row["specialized_leaf_cnf_sha256"] for row in rows],
            EXPECTED_LEAF_HASHES,
        )
        for index, (row, units) in enumerate(
            zip(rows, self.result["catalogue_units"], strict=True)
        ):
            self.assertEqual(row["catalogue_index_zero_based"], index)
            self.assertEqual(row["specialized_unit_count"], 66)
            self.assertEqual(row["specialized_clause_count"], 53_911)
            specialized = master.specialize_selectors(
                self.result["master_clauses"], master.selector_cube(index)
            )
            self.assertEqual(
                specialized,
                self.result["base_clauses"] + tuple((unit,) for unit in units),
            )

    def test_thirteen_cubes_partition_all_sixteen_selector_codes(self) -> None:
        cubes = self.result["cover_cubes"]
        rows = self.result["cover_rows"]
        self.assertEqual(len(cubes), 13)
        self.assertEqual(len(set(cubes)), 13)
        self.assertEqual(master.parse_icnf_bytes(self.result["cover_icnf_bytes"]), cubes)
        self.assertTrue(all(len(cube) == 4 for cube in cubes[:12]))
        self.assertEqual(cubes[12], (279, 280))

        for code in range(16):
            assignment = {
                abs(literal): literal > 0 for literal in master.selector_cube(code)
            }
            matches = [
                row for row in rows
                if master.cube_matches_assignment(row["cube"], assignment)
            ]
            self.assertEqual(len(matches), 1)
            if code < 12:
                self.assertEqual(matches[0]["cover_index_one_based"], code + 1)
                self.assertEqual(matches[0]["cube_type"], "valid_r35_order12_type")
            else:
                self.assertEqual(matches[0]["cover_index_one_based"], 13)
                self.assertEqual(
                    matches[0]["cube_type"],
                    "invalid_selector_codes_12_through_15",
                )

    def test_negated_cover_is_false_on_every_selector_assignment(self) -> None:
        self.assertEqual(
            self.result["negated_cover_clauses"],
            tuple(tuple(-literal for literal in cube) for cube in self.result["cover_cubes"]),
        )
        for code in range(16):
            assignment = {
                abs(literal): literal > 0 for literal in master.selector_cube(code)
            }
            cnf_value = all(
                any(
                    assignment[abs(literal)] == (literal > 0)
                    for literal in clause
                )
                for clause in self.result["negated_cover_clauses"]
            )
            self.assertFalse(cnf_value)

    def test_deterministic_hashes(self) -> None:
        metadata = self.result["metadata"]
        self.assertEqual(
            metadata["cnf"]["sha256"],
            "0F5049E4D2A7B465E33BA852170477711CA63220ED6F2DAD1542C558D4D8BFA8",
        )
        self.assertEqual(
            metadata["hashes"],
            {
                "base_cnf_sha256": "51A5A3D44B05FE4981A97C435BA36F3950A22A3FEDC0BBFAA6FCF41791F90FDB",
                "cover_icnf_sha256": "233C14E7871D0EC0CA28E431C90DE741B5917F3467F1A8A6CC1656743C65A492",
                "cube_manifest_sha256": "50FE3BBCF8DA882ABE78039350AF591049E57ED1FDF8EC029CE5ECB388168536",
                "leaf_hash_list_sha256": "FC72850B851466E8CA7F968336EA6A8A216972CF63FF9E91B25E77F1E52F3B9D",
                "negated_cover_cnf_sha256": "2259B34D050AE26C65ED75EB8D41A5616B9776286EECC9133215A8D5E20F8FD6",
                "valid_assumptions_sha256": "086F4EECC5E56677A9421076DFA5137EEE9255CC844ED9A11D4758D0EA6BF44D",
            },
        )

    def test_cli_artifacts_are_forced_to_explicit_s_drive_paths(self) -> None:
        accepted = Path(r"S:\CodexResearchCache\ramsey-formal\r45-d12")
        self.assertEqual(master.require_explicit_ssd_path(accepted), accepted)
        for rejected in (
            Path(r"C:\temp\r45-d12"),
            Path(r"S:relative-output"),
            Path("relative-output"),
            HERE / "guarded_master",
        ):
            with self.assertRaisesRegex(ValueError, "rooted on S"):
                master.require_explicit_ssd_path(rejected)
        with self.assertRaises(ValueError):
            master.generate(HERE / "must-not-be-created")
        self.assertFalse((HERE / "must-not-be-created").exists())

    def test_generator_does_not_overstate_proof_status(self) -> None:
        metadata = self.result["metadata"]
        self.assertEqual(metadata["status"], "GENERATED_NOT_SOLVED_OR_LRAT_CERTIFIED")
        self.assertEqual(metadata["proof_artifacts"]["present"], 0)
        self.assertEqual(metadata["proof_artifacts"]["leaf_lrat_required"], 13)
        self.assertTrue(metadata["proof_artifacts"]["cover_lrat_required"])
        self.assertIn("No SAT status", metadata["proof_artifacts"]["warning"])


if __name__ == "__main__":
    unittest.main()
