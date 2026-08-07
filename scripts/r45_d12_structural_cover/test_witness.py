from __future__ import annotations

import itertools
import os
import unittest
from pathlib import Path

from . import verify_cover9
from . import verify_witness


EXPECTED_CLOSURE_SIZES = (5040, 2520, 5040, 2520, 2520, 2520, 2520, 2520, 1260)


class CoverNineWitnessTests(unittest.TestCase):
    def test_frozen_format_and_hash(self) -> None:
        self.assertEqual(verify_witness.HEADER.size, 24)
        self.assertEqual(verify_witness.MAGIC, b"R44WIT1\0")
        self.assertEqual(
            verify_witness.EXPECTED_WITNESS_SHA256,
            "A5C8BFC67618FB5345AD072E07237271390068B0883C12B04D4B0BEE4E379B96",
        )

    def test_exact_labelled_closure_sizes(self) -> None:
        records = verify_cover9.EXPECTED_RECORDS
        sizes = tuple(
            len(
                {
                    verify_witness.relabelled_mask(mask, permutation)
                    for permutation in itertools.permutations(range(7))
                }
            )
            for mask in (
                verify_witness.decode_short_graph6_mask(record, 7)
                for record in records
            )
        )
        self.assertEqual(sizes, EXPECTED_CLOSURE_SIZES)
        self.assertEqual(sum(sizes), 26_460)
        self.assertEqual(792 * sum(sizes), 20_956_320)

    def test_full_witness_when_available(self) -> None:
        source = os.environ.get("R45_R44_SOURCE_DIR")
        witness = os.environ.get("R45_R44_COVER9_WITNESS")
        if source is None or witness is None:
            self.skipTest("full cover9 witness environment is unset")
        report = verify_witness.verify(Path(source), Path(witness))
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["verification"]["valid_entries"], 1_449_166)
        self.assertEqual(report["verification"]["invalid_entries"], 0)


if __name__ == "__main__":
    unittest.main()
