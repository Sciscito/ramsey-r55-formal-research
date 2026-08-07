from __future__ import annotations

import unittest

from . import generate_two_center_branches as two
from . import generate_universal as universal


class TwoCenterTests(unittest.TestCase):
    def test_exact_case_cover(self) -> None:
        self.assertEqual(len(two.CASES), 13)
        self.assertTrue(all(0 <= p <= 3 and 0 <= q <= 3 and p + q >= 2 for p, q in two.CASES))
        self.assertEqual(set(two.EXPECTED_CASE_RESULTS), set(two.CASES))
        self.assertTrue(
            all(clauses < 1_000_000 for clauses, _, _ in two.EXPECTED_CASE_RESULTS.values())
        )
        self.assertEqual(
            min(two.EXPECTED_CASE_RESULTS.items(), key=lambda item: item[1][0]),
            (
                (2, 0),
                (
                    758_924,
                    44_764_698,
                    "D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315",
                ),
            ),
        )

    def test_assignment_blocks(self) -> None:
        assignment = two.second_assignment(2, 1)
        first = tuple(
            assignment[universal.edge_var(12, 1, vertex)] for vertex in range(2, 9)
        )
        second = tuple(
            assignment[universal.edge_var(12, 1, vertex)] for vertex in range(9, 12)
        )
        self.assertEqual(first, (True, True) + (False,) * 5)
        self.assertEqual(second, (True, False, False))

    def test_simplification_and_canonicalization(self) -> None:
        assignment = two.second_assignment(2, 1)
        true_variable = universal.edge_var(12, 1, 2)
        false_variable = universal.edge_var(12, 1, 5)
        untouched = universal.edge_var(12, 3, 4)
        self.assertIsNone(two.canonical_simplification((true_variable, untouched), assignment))
        self.assertEqual(
            two.canonical_simplification((false_variable, -untouched), assignment),
            (-untouched,),
        )


if __name__ == "__main__":
    unittest.main()
