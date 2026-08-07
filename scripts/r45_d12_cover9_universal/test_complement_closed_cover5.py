from __future__ import annotations

import ast
import unittest
from pathlib import Path

from . import generate_complement_closed_cover5 as generator
from . import verify_complement_closed_cover5 as independent


class ComplementClosedCoverFiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.generated = generator.audit()
        cls.verified = independent.verify()

    def test_source_and_complement_closure_are_frozen(self) -> None:
        self.assertEqual(
            self.generated["source"]["sha256"], generator.EXPECTED_COVER_SHA256
        )
        closure = self.generated["complement_closure"]
        self.assertEqual(closure["raw_labelled_masks"], 17_640)
        self.assertEqual(closure["complemented_labelled_masks"], 17_640)
        self.assertEqual(closure["raw_complement_intersection"], 5_040)
        self.assertEqual(closure["closed_labelled_masks"], 30_240)
        self.assertEqual(closure["unique_isomorphism_classes"], 8)
        self.assertEqual(
            tuple(closure["class_representatives_graph6"]),
            generator.EXPECTED_CLASS_REPRESENTATIVES,
        )
        self.assertEqual(
            closure["raw_closure_sha256"], generator.EXPECTED_RAW_CLOSURE_SHA256
        )
        self.assertEqual(
            closure["closed_closure_sha256"],
            generator.EXPECTED_CLOSED_CLOSURE_SHA256,
        )

    def test_six_representatives_and_cube_closure_are_frozen(self) -> None:
        reduction = self.generated["cube_reduction"]
        recovered = tuple(
            (int(row["ones"], 16), int(row["fixed"], 16))
            for row in reduction["unique_s7_representatives"]
        )
        self.assertEqual(recovered, generator.CUBE_REPRESENTATIVES)
        self.assertEqual(reduction["representative_count"], 6)
        self.assertEqual(reduction["unique_cubes"], 20_160)
        self.assertEqual(reduction["widths"], {15: 5_040, 16: 10_080, 19: 5_040})
        self.assertEqual(
            reduction["cube_closure_sha256"], generator.EXPECTED_CUBE_CLOSURE_SHA256
        )
        self.assertTrue(reduction["exact_on_local_r44"])

    def test_exhaustive_two_to_twenty_one_audit(self) -> None:
        exhaustive = self.generated["exhaustive_check"]
        self.assertEqual(exhaustive["assignments"], 1 << 21)
        self.assertEqual(exhaustive["r44_assignments"], 923_012)
        self.assertEqual(exhaustive["forbidden_r44_assignments"], 30_240)
        self.assertEqual(exhaustive["rejected_r44_assignments"], 30_240)

    def test_current_cube_family_is_deletion_irredundant_only(self) -> None:
        search = self.generated["reduction_search"]
        self.assertEqual(search["cubes_with_unique_witness"], 20_160)
        self.assertEqual(search["initially_removable_cubes"], 0)
        self.assertFalse(search["individual_cube_deletion_possible"])
        self.assertFalse(search["symmetry_preserving_orbit_removal_possible"])
        self.assertEqual(
            tuple(search["orbit_removal_misses"]),
            generator.EXPECTED_ORBIT_REMOVAL_MISSES,
        )
        self.assertFalse(search["alternative_cube_families_searched"])
        self.assertFalse(search["global_minimality_conclusion"])

    def test_independent_verifier_agrees(self) -> None:
        self.assertEqual(self.verified["status"], "PASS")
        self.assertEqual(self.verified["exhaustive"]["assignments"], 1 << 21)
        self.assertEqual(self.verified["complement_closure"]["closed_masks"], 30_240)
        self.assertEqual(self.verified["cube_closure"]["cubes"], 20_160)
        self.assertEqual(
            self.verified["cube_closure"]["sha256"],
            generator.EXPECTED_CUBE_CLOSURE_SHA256,
        )
        self.assertTrue(self.verified["cube_closure"]["deletion_irredundant"])
        self.assertFalse(self.verified["scope"]["unsat_claimed"])
        self.assertFalse(self.verified["scope"]["global_minimality_claimed"])

    def test_independent_verifier_rejects_corrupted_representative(self) -> None:
        corrupted = list(independent.CUBE_REPRESENTATIVES)
        ones, fixed = corrupted[0]
        corrupted[0] = (ones ^ (fixed & -fixed), fixed)
        with self.assertRaisesRegex(ValueError, "cube"):
            independent.verify(corrupted)

    def test_independent_verifier_imports_no_project_module(self) -> None:
        source = independent.__file__
        self.assertIsNotNone(source)
        tree = ast.parse(Path(source).read_text(encoding="utf-8"))
        imports = {
            alias.name
            for node in ast.walk(tree)
            if isinstance(node, ast.Import)
            for alias in node.names
        }
        imports.update(
            node.module or ""
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
        )
        self.assertFalse(
            any(name == "scripts" or name.startswith("scripts.") for name in imports)
        )


if __name__ == "__main__":
    unittest.main()
