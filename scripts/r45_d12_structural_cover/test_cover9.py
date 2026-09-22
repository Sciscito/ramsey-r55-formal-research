from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import structural_cover
from . import verify_cover9


class CoverNineTests(unittest.TestCase):
    def test_cover_records_are_fixed(self) -> None:
        path = Path(__file__).with_name("cover9.tsv")
        self.assertEqual(verify_cover9.cover_records(path), verify_cover9.EXPECTED_RECORDS)
        self.assertEqual(structural_cover.sha256(path), verify_cover9.EXPECTED_COVER_SHA256)

    def test_full_certificate_when_available(self) -> None:
        source = os.environ.get("R45_R44_SOURCE_DIR")
        incidence = os.environ.get("R45_R44_COVER9_INCIDENCE")
        if source is None or incidence is None:
            self.skipTest("full cover9 artifact environment is unset")
        report = verify_cover9.verify(Path(source), Path(incidence))
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["incidence"]["uncovered_records"], 0)


if __name__ == "__main__":
    unittest.main()
