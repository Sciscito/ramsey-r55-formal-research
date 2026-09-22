from __future__ import annotations

import unittest

from . import generate_prefix_symmetry as prefix


class PrefixSymmetryTests(unittest.TestCase):
    def test_exact_prefix_clauses(self) -> None:
        self.assertEqual(len(prefix.PREFIX_CLAUSES), 10)
        self.assertEqual(prefix.PREFIX_CLAUSES[0], (1, -2))
        self.assertEqual(prefix.PREFIX_CLAUSES[-1], (10, -11))

    def test_prefix_clauses_characterize_initial_segments(self) -> None:
        for assignment in range(1 << 11):
            satisfies = all(
                bool(assignment & (1 << (left - 1)))
                or not bool(assignment & (1 << (-right - 1)))
                for left, right in prefix.PREFIX_CLAUSES
            )
            expected = assignment == 0 or assignment == (1 << assignment.bit_count()) - 1
            self.assertEqual(satisfies, expected)


if __name__ == "__main__":
    unittest.main()
