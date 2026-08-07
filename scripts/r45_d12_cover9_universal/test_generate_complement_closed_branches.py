from __future__ import annotations

import unittest

from . import generate_complement_closed_branches as branches


class ComplementClosedBranchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.preflight = branches.preflight()

    def test_exact_local_reductions(self) -> None:
        self.assertEqual(self.preflight["status"], "PASS")
        self.assertEqual(self.preflight["complement_closed_classes"], 8)
        self.assertEqual(self.preflight["labelled_masks"], 30_240)
        self.assertEqual(self.preflight["cubes"], 20_160)
        self.assertEqual(
            tuple(self.preflight["block_conditioned_counts"]),
            branches.BLOCK_CONDITIONED_COUNTS,
        )
        self.assertEqual(
            tuple(self.preflight["local_conditioned_counts"]),
            branches.LOCAL_CONDITIONED_COUNTS,
        )

    def test_complement_symmetry_is_visible_in_counts(self) -> None:
        self.assertEqual(
            branches.BLOCK_CONDITIONED_COUNTS,
            tuple(reversed(branches.BLOCK_CONDITIONED_COUNTS)),
        )
        self.assertEqual(
            branches.LOCAL_CONDITIONED_COUNTS,
            tuple(reversed(branches.LOCAL_CONDITIONED_COUNTS)),
        )

    def test_three_representative_degree_counts_are_frozen(self) -> None:
        observed = {
            degree: branches.clause_count(degree) for degree in branches.DEGREES
        }
        self.assertEqual(observed, branches.EXPECTED_CLAUSE_COUNTS)
        self.assertEqual(
            self.preflight["degree_clause_counts"],
            {str(key): value for key, value in branches.EXPECTED_CLAUSE_COUNTS.items()},
        )

    def test_rejects_nonrepresentative_degree(self) -> None:
        with self.assertRaisesRegex(ValueError, "degree"):
            branches.clause_count(5)


if __name__ == "__main__":
    unittest.main()
