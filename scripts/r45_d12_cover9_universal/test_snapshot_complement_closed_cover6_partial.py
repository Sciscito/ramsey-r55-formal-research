from __future__ import annotations

import unittest

from . import snapshot_complement_closed_cover6_partial as snapshot


class ComplementClosedCover6PartialSnapshotTests(unittest.TestCase):
    def test_formula_name_parser(self) -> None:
        self.assertEqual(
            snapshot.parse_formula_name("cover6_closed_d8_two_center_p1_q3.cnf"),
            (8, 1, 3),
        )

    def test_formula_name_parser_rejects_partial_and_unrelated_files(self) -> None:
        for name in (
            "cover6_closed_d8_two_center_p1_q3.cnf.partial",
            "cover9_d8_two_center_p1_q3.cnf",
            "manifest.json",
        ):
            with self.assertRaisesRegex(ValueError, "not a completed"):
                snapshot.parse_formula_name(name)


if __name__ == "__main__":
    unittest.main()
