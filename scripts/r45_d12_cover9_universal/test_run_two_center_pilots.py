from __future__ import annotations

import unittest

from . import run_two_center_pilots as pilots


class TwoCenterPilotBatchTests(unittest.TestCase):
    def test_completed_metrics(self) -> None:
        log = """c parsed 758924 clauses in 1.03 seconds process time
c i 1.11 116 4 0 0 167 70 35% 3 647878 38 58%
c         0.09    8.33% solve
c conflicts:                   174      1856.00    per second
"""
        self.assertEqual(
            pilots.parse_metrics(log),
            {
                "parse_seconds": 1.03,
                "search_seconds": 0.09,
                "conflicts": 174,
                "last_solver_seconds": 1.11,
            },
        )

    def test_timeout_metrics_use_last_progress_row(self) -> None:
        log = """c parsed 500 clauses in 2.50 seconds process time
c - 29.75 671 15 7 1783 22214 5494 74% 13 500 55 83%
"""
        self.assertEqual(
            pilots.parse_metrics(log),
            {
                "parse_seconds": 2.5,
                "search_seconds": 27.25,
                "conflicts": 22214,
                "last_solver_seconds": 29.75,
            },
        )


if __name__ == "__main__":
    unittest.main()
