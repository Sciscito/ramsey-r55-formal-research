from __future__ import annotations

import itertools
import unittest
from pathlib import Path

from . import minimum_order7_cover as minimum
from . import replay_minimum_lrat as replay


def satisfies(clauses: list[tuple[int, ...]], assignment: int) -> bool:
    return all(
        any(
            bool(assignment >> (abs(literal) - 1) & 1) == (literal > 0)
            for literal in clause
        )
        for clause in clauses
    )


class MinimumOrderSevenCoverTests(unittest.TestCase):
    def test_sequential_counter_small_exhaustive(self) -> None:
        variables, clauses = minimum.sequential_at_most(5, 2)
        self.assertEqual(variables, 13)
        for primary in range(1 << 5):
            extendible = any(
                satisfies(clauses, primary | auxiliary << 5)
                for auxiliary in range(1 << (variables - 5))
            )
            self.assertEqual(extendible, primary.bit_count() <= 2)

    def test_hitting_set_solver(self) -> None:
        clauses = ((0, 1), (1, 2), (2, 3))
        hit, _states = minimum.find_hitting_set(clauses, 4, 2)
        self.assertIsNotNone(hit)
        miss, _states = minimum.find_hitting_set(((0,), (1,), (2,)), 3, 2)
        self.assertIsNone(miss)

    def test_r44_mask_predicate(self) -> None:
        self.assertFalse(minimum.is_r44_order7_mask(0))
        complete = (1 << 21) - 1
        self.assertFalse(minimum.is_r44_order7_mask(complete))
        self.assertEqual(len(minimum.K4_MASKS_7), 35)

    def test_replay_source_has_exact_identity(self) -> None:
        source = replay.lean_source(
            Path(r"S:\proof\no_cover4.cnf"),
            Path(r"S:\proof\no_cover4.lrat"),
        ).decode("utf-8")
        self.assertIn("no_order7_cover_of_size_four", source)
        self.assertIn("R45OrderSevenCoverMinimumReplay", source)
        self.assertNotIn("d12_type0_core24", source)


if __name__ == "__main__":
    unittest.main()
