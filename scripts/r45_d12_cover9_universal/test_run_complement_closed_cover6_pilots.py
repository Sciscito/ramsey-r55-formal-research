from __future__ import annotations

import unittest

from . import run_complement_closed_cover6_pilots as pilots


class ComplementClosedCover6PilotTests(unittest.TestCase):
    def test_complete_metrics(self) -> None:
        log = """c parsed 123 clauses in 0.12 seconds
c * 0.52 0.0 0 0 0 0 345
c conflicts: 345
c 0.40 88.0% solve
s UNSATISFIABLE
"""
        metrics = pilots.parse_metrics(log)
        self.assertEqual(metrics["parse_seconds"], 0.12)
        self.assertEqual(metrics["search_seconds"], 0.40)
        self.assertEqual(metrics["conflicts"], 345)
        self.assertEqual(metrics["last_solver_seconds"], 0.52)

    def test_progress_fallback(self) -> None:
        log = """c parsed 12 clauses in 0.20 seconds
c * 1.50 0 0 0 0 999
"""
        metrics = pilots.parse_metrics(log)
        self.assertEqual(metrics["conflicts"], 999)
        self.assertAlmostEqual(metrics["search_seconds"], 1.30)

    def test_batch_name_guard_is_local(self) -> None:
        self.assertEqual(pilots.Path("pilot-100k").name, "pilot-100k")
        self.assertNotEqual(pilots.Path("nested/pilot-100k").name, "nested/pilot-100k")


if __name__ == "__main__":
    unittest.main()
