from __future__ import annotations

import unittest

from . import benchmark_cover9_gluing as benchmark


class CoverNineGluingBenchmarkTests(unittest.TestCase):
    def test_type_parser(self) -> None:
        self.assertEqual(benchmark.parse_types("0,2-4,4"), (0, 2, 3, 4))
        with self.assertRaises(ValueError):
            benchmark.parse_types("12")

    def test_raw_and_complemented_units_are_opposites(self) -> None:
        raw = benchmark.motif_units("FiIXw", "raw_dimacs")
        complemented = benchmark.motif_units("FiIXw", "complemented_dimacs")
        self.assertEqual(len(raw), 21)
        self.assertEqual(tuple(map(abs, raw)), tuple(map(abs, complemented)))
        self.assertEqual(raw, tuple(-literal for literal in complemented))
        self.assertEqual(min(map(abs, raw)), 211)
        self.assertEqual(max(map(abs, raw)), 256)

    def test_invalid_polarity_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            benchmark.motif_units("FiIXw", "implicit")


if __name__ == "__main__":
    unittest.main()
