from __future__ import annotations

import unittest

from . import generate_complement_closed_cover6_two_center as two
from . import generate_universal as universal


class ComplementClosedCover6TwoCenterTests(unittest.TestCase):
    def test_complete_case_sets(self) -> None:
        for degree, expected_count in two.CASE_COUNTS.items():
            observed = two.cases(degree)
            direct = tuple(
                (p, q)
                for p in range(4)
                for q in range(12 - degree)
                if 2 <= p + q <= 7
            )
            self.assertEqual(observed, direct)
            self.assertEqual(len(observed), expected_count)
        self.assertNotIn((3, 5), two.cases(6))
        self.assertIn((3, 4), two.cases(6))

    def test_exact_units_are_variables_one_through_twenty_one(self) -> None:
        for degree in two.DEGREES:
            for p, q in two.cases(degree):
                literals = two.unit_literals(degree, p, q)
                self.assertEqual(len(literals), 21)
                self.assertEqual({abs(literal) for literal in literals}, set(range(1, 22)))
                assignment = two.exact_assignment(degree, p, q)
                self.assertEqual(
                    literals,
                    tuple(variable if assignment[variable] else -variable for variable in range(1, 22)),
                )

    def test_root_and_second_center_counts(self) -> None:
        for degree in two.DEGREES:
            for p, q in two.cases(degree):
                root = two.root_assignment(degree)
                second = two.second_assignment(degree, p, q)
                self.assertEqual(sum(root.values()), degree)
                self.assertEqual(sum(second.values()), p + q)
                self.assertEqual(1 + sum(second.values()), 1 + p + q)
                self.assertTrue(3 <= 1 + p + q <= 8)
                self.assertEqual(
                    second[universal.edge_var(12, 1, 2)],
                    p >= 1,
                )

    def test_compact_clause_encoding_round_trip(self) -> None:
        clauses = ((), (1,), (-1,), (1, -2, 66), tuple(range(1, 67)))
        for clause in clauses:
            self.assertEqual(two.decode_clause(two.encode_clause(clause)), clause)
        with self.assertRaisesRegex(ValueError, "tautological"):
            two.encode_clause((4, -4))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            two.encode_clause((4, 4))

    def test_simplification(self) -> None:
        assignment = {1: True, 2: False}
        self.assertIsNone(two.simplify_clause((1, 3), assignment))
        self.assertIsNone(two.simplify_clause((-2, 3), assignment))
        reduced = two.simplify_clause((-1, 2, -3), assignment)
        self.assertIsNotNone(reduced)
        self.assertEqual(two.decode_clause(reduced), (-3,))
        empty = two.simplify_clause((-1, 2), assignment)
        self.assertIsNotNone(empty)
        self.assertEqual(two.decode_clause(empty), ())

    def test_rejects_out_of_scope_cases(self) -> None:
        with self.assertRaisesRegex(ValueError, "degree"):
            two.cases(5)
        with self.assertRaisesRegex(ValueError, "unsupported"):
            two.second_assignment(8, 0, 0)


if __name__ == "__main__":
    unittest.main()
