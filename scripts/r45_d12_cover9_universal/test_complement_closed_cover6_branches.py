from __future__ import annotations

import unittest

from . import generate_complement_closed_cover6_branches as generator
from . import verify_complement_closed_cover6_branches as independent


class ComplementClosedCover6BranchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.generated = generator.preflight()
        cls.checked = independent.preflight()

    def test_independent_preflights_agree(self) -> None:
        self.assertEqual(self.generated["status"], "PASS")
        self.assertEqual(self.checked["status"], "PASS")
        for key in (
            "source_sha256",
            "records",
            "labelled_masks",
            "mask_sha256",
            "cubes",
            "cube_sha256",
            "cube_widths",
            "closed_under_complement",
            "block_conditioned_counts",
            "local_conditioned_counts",
            "degree_clause_counts",
        ):
            self.assertEqual(self.generated[key], self.checked[key], key)

    def test_frozen_local_target(self) -> None:
        self.assertEqual(self.generated["labelled_masks"], 25_200)
        self.assertEqual(self.generated["cubes"], 25_200)
        self.assertTrue(self.generated["local_exactness"]["exact_on_local_r44"])
        self.assertTrue(self.checked["local_exactness"]["exact"])
        self.assertEqual(self.checked["local_exactness"]["r44_assignments"], 923_012)

    def test_frozen_conditioning_and_global_counts(self) -> None:
        self.assertEqual(
            tuple(self.generated["block_conditioned_counts"]),
            generator.BLOCK_CONDITIONED_COUNTS,
        )
        self.assertEqual(
            tuple(self.generated["local_conditioned_counts"]),
            generator.LOCAL_CONDITIONED_COUNTS,
        )
        self.assertEqual(
            self.generated["degree_clause_counts"],
            {str(key): value for key, value in generator.EXPECTED_CLAUSE_COUNTS.items()},
        )

    def test_rejects_uncovered_degree(self) -> None:
        with self.assertRaisesRegex(ValueError, "degree"):
            generator.clause_count(5)
        with self.assertRaisesRegex(ValueError, "degree"):
            independent.degree_clause_count(5)


if __name__ == "__main__":
    unittest.main()
