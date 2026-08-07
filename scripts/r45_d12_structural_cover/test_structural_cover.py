from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import structural_cover


class StructuralCoverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        source = os.environ.get("R45_R44_SOURCE_DIR")
        cls.source = Path(source) if source else None

    def test_ssd_guard(self) -> None:
        with self.assertRaises(ValueError):
            structural_cover.ensure_ssd(Path("C:/heavy"))
        self.assertEqual(
            str(structural_cover.ensure_ssd(Path("S:/heavy"))),
            str(Path("S:/heavy")),
        )

    def test_expected_constants(self) -> None:
        self.assertEqual(structural_cover.EXPECTED_COUNTS[12], 1_449_166)
        self.assertEqual(len(structural_cover.EXPECTED_HASHES["r44_12.g6"]), 64)

    def test_dense_pool(self) -> None:
        if self.source is None:
            self.skipTest("R45_R44_SOURCE_DIR is unset")
        pool = structural_cover.dense_pool(self.source)
        self.assertEqual(sum(item.order == 7 for item in pool), 46)
        self.assertEqual(sum(item.order == 8 for item in pool), 53)
        self.assertTrue(all(item.edges >= (13 if item.order == 7 else 18) for item in pool))

    def test_source_hashes(self) -> None:
        if self.source is None:
            self.skipTest("R45_R44_SOURCE_DIR is unset")
        result = structural_cover.validate_source(self.source, (7, 8, 12))
        self.assertEqual(result["r44_12.g6"]["records"], 1_449_166)


if __name__ == "__main__":
    unittest.main()
