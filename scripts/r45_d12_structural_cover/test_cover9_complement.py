from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import cross_check
from . import structural_cover
from . import verify_cover9


EXPECTED_COMPLEMENT_SHA256 = "943563F7A4CA67D0E756BAA799F1586A5B0EB346664A2F058420BED56DA389E3"
EXPECTED_COMPLEMENT_INCIDENCE_SHA256 = "D2B2330FBDE43AD96C5435C9F0AC8DF4B444813C694E7A69C5A226684E9FDD0B"


class CoverNineComplementTests(unittest.TestCase):
    def test_complement_records_are_exact(self) -> None:
        path = Path(__file__).with_name("cover9_complement.tsv")
        self.assertEqual(structural_cover.sha256(path), EXPECTED_COMPLEMENT_SHA256)
        records = verify_cover9.cover_records(path)
        expected = tuple(
            cross_check.encode_graph6(
                structural_cover.ramsey.complement_graph(
                    structural_cover.ramsey.decode_graph6(record)
                )
            )
            for record in verify_cover9.EXPECTED_RECORDS
        )
        self.assertEqual(records, expected)

    def test_full_complement_incidence_when_available(self) -> None:
        incidence_path = os.environ.get("R45_R44_COVER9_COMPLEMENT_INCIDENCE")
        if incidence_path is None:
            self.skipTest("full complemented incidence environment is unset")
        path = Path(incidence_path)
        self.assertEqual(
            structural_cover.sha256(path), EXPECTED_COMPLEMENT_INCIDENCE_SHA256
        )
        incidence = structural_cover.read_incidence(path)
        expected_records = verify_cover9.cover_records(
            Path(__file__).with_name("cover9_complement.tsv")
        )
        self.assertEqual((incidence.count7, incidence.count8), (9, 0))
        self.assertEqual(incidence.graph6, expected_records)
        self.assertEqual(incidence.graph_count, 1_449_166)
        self.assertEqual(
            structural_cover.uncovered_bits(incidence, range(9)).bit_count(), 0
        )


if __name__ == "__main__":
    unittest.main()
