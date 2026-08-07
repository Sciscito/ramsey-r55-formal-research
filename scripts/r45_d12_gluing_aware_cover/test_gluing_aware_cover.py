from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import benchmark_mixed_gluing as benchmark
from . import cover_audit


HERE = Path(__file__).resolve().parent


class GluingAwareCoverTests(unittest.TestCase):
    def test_frozen_cover_shapes(self) -> None:
        compact = cover_audit.cover_records(HERE / "cover7_mixed.tsv")
        dense = cover_audit.cover_records(HERE / "dense9_mixed.tsv")
        minimum = cover_audit.cover_records(HERE / "cover5_order7.tsv")
        self.assertEqual((sum(o == 7 for o, _ in compact), sum(o == 8 for o, _ in compact)), (5, 2))
        self.assertEqual((sum(o == 7 for o, _ in dense), sum(o == 8 for o, _ in dense)), (8, 1))
        self.assertEqual((sum(o == 7 for o, _ in minimum), sum(o == 8 for o, _ in minimum)), (5, 0))

    def test_mixed_units_cover_first_eight_vertices(self) -> None:
        units = benchmark.motif_units(8, "Gddzr[", "raw_dimacs")
        self.assertEqual(len(units), 28)
        self.assertEqual(len(set(map(abs, units))), 28)
        complemented = benchmark.motif_units(8, "Gddzr[", "complemented_dimacs")
        self.assertEqual(complemented, tuple(-literal for literal in units))

    def test_full_incidence_when_available(self) -> None:
        source = os.environ.get("R45_R44_SOURCE_DIR")
        incidence = os.environ.get("R45_R44_MIXED_INCIDENCE")
        if source is None or incidence is None:
            self.skipTest("mixed-cover artifact environment is unset")
        for name in ("cover7_mixed.tsv", "dense9_mixed.tsv"):
            report = cover_audit.verify(Path(source), Path(incidence), HERE / name)
            self.assertEqual(report["status"], "PASS")
            self.assertEqual(report["incidence"]["uncovered"], 0)


if __name__ == "__main__":
    unittest.main()
