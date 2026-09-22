from __future__ import annotations

import itertools
import tempfile
import unittest
from pathlib import Path

from . import generate_universal as universal
from . import independent_verify


class UniversalCoverNineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cubes = universal.reduced_cubes()

    def test_frozen_counts_and_cover_identity(self) -> None:
        self.assertEqual(universal.read_cover_records(), universal.COVER_RECORDS)
        forbidden = universal.raw_forbidden_masks()
        self.assertEqual(len(forbidden), 26_460)
        self.assertEqual(len(self.cubes), 15_120)
        self.assertEqual(universal.formula_clause_count(), 11_976_030)
        self.assertEqual(universal.RAW_CLAUSE_COUNT, 20_957_310)
        self.assertEqual(universal.exact_formula_byte_count(self.cubes), 701_106_138)

    def test_reduced_encoding_is_exhaustively_exact_modulo_r44(self) -> None:
        report = universal.validate_local_reduction()
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["checked_assignments"], 1 << 21)
        self.assertEqual(report["r44_assignments"], 923_012)
        self.assertEqual(report["raw_forbidden_assignments"], 26_460)
        self.assertEqual(report["allowed_assignments_under_r44"], 896_552)

    def test_independent_verifier_and_corruption_rejection(self) -> None:
        report = independent_verify.verify(universal.REDUCED_CUBE_REPRESENTATIVES)
        self.assertEqual(report["status"], "PASS")
        corrupted = list(universal.REDUCED_CUBE_REPRESENTATIVES)
        ones, fixed = corrupted[0]
        corrupted[0] = (ones ^ (fixed & -fixed), fixed)
        with self.assertRaisesRegex(ValueError, "count mismatch|unsafely|miss"):
            independent_verify.verify(corrupted)
    def test_instantiated_clause_has_exact_cube_polarity(self) -> None:
        vertices = (0, 1, 2, 4, 6, 8, 11)
        variables = universal.subset_variables(vertices)
        cube = universal.REDUCED_CUBE_REPRESENTATIVES[0]
        clause = universal.instantiate_cube_blocker(cube, variables)
        ones, fixed = cube
        assignment = {
            variables[position]: bool((ones >> position) & 1)
            for position in range(21)
            if (fixed >> position) & 1
        }
        self.assertTrue(all(assignment[abs(literal)] != (literal > 0) for literal in clause))
        for flipped in assignment:
            changed = dict(assignment)
            changed[flipped] = not changed[flipped]
            self.assertTrue(any(changed[abs(literal)] == (literal > 0) for literal in clause))

    def test_every_reduced_clause_uses_all_seven_vertices(self) -> None:
        for _ones, fixed in self.cubes:
            support = set()
            for right in range(1, 7):
                for left in range(right):
                    if (fixed >> universal.edge_position(left, right)) & 1:
                        support.update((left, right))
            self.assertEqual(support, set(range(7)))

    def test_local_template_is_deterministic(self) -> None:
        first = universal.local_template_bytes(self.cubes)
        second = universal.local_template_bytes(self.cubes)
        self.assertEqual(first, second)
        self.assertEqual(first.count(b"\n"), 15_121)
        self.assertTrue(first.startswith(b"p cnf 21 15120\n"))

    def test_heavy_output_guard_rejects_system_disk(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "absolute on S"):
                universal.ensure_ssd(Path(directory))


if __name__ == "__main__":
    unittest.main()
