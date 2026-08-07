from __future__ import annotations

import unittest

from . import generate_block_degree_branch as block
from . import generate_degree_branch as degree


class BlockDegreeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cubes = block.block_conditioned_cubes()

    def test_exact_local_counts(self) -> None:
        self.assertEqual(tuple(map(len, self.cubes)), block.BLOCK_CONDITIONED_COUNTS)

    def test_exact_global_counts(self) -> None:
        self.assertEqual(
            {value: block.clause_count(value) for value in degree.DEGREES},
            block.EXPECTED_CLAUSE_COUNTS,
        )

    def test_extreme_block_slices(self) -> None:
        self.assertEqual(len(block.block_forbidden_masks(0)), 5_040)
        self.assertEqual(len(block.block_forbidden_masks(7)), 0)


if __name__ == "__main__":
    unittest.main()
