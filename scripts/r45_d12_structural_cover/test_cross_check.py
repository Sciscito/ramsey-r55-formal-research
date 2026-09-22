from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import cross_check
from . import structural_cover


class CrossCheckTests(unittest.TestCase):
    def test_independent_graph6_roundtrip_sparse(self) -> None:
        graph = [0] * 8
        for left in range(8):
            for right in range(left + 1, 8):
                if (left * 7 + right * 11 + left * right) % 5 < 2:
                    graph[left] |= 1 << right
                    graph[right] |= 1 << left
        record = cross_check.encode_graph6(tuple(graph))
        self.assertEqual(structural_cover.ramsey.decode_graph6(record), tuple(graph))

    def test_native_python_cross_check(self) -> None:
        scanner = os.environ.get("R45_R44_SCANNER")
        source = os.environ.get("R45_R44_SOURCE_DIR")
        output = os.environ.get("R45_R44_CROSSCHECK_DIR")
        if scanner is None or source is None or output is None:
            self.skipTest("native cross-check environment is unset")
        report = cross_check.run(Path(scanner), Path(source), Path(output))
        self.assertEqual(report["status"], "PASS")
        self.assertTrue(report["padding_bits_zero"])


if __name__ == "__main__":
    unittest.main()
