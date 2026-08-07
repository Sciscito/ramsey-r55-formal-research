from __future__ import annotations

import unittest

from . import run_solver_pilot as pilot


class SolverPilotTests(unittest.TestCase):
    def test_status_classification(self) -> None:
        self.assertEqual(pilot.classify(0, "c limit reached\n"), "UNKNOWN_LIMIT")
        self.assertEqual(pilot.classify(10, "s SATISFIABLE\n"), "SAT")
        self.assertEqual(pilot.classify(20, "s UNSATISFIABLE\n"), "UNSAT_WITHOUT_PROOF")

    def test_inconsistent_status_is_rejected(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "inconsistent"):
            pilot.classify(20, "c no terminal status\n")

    def test_profiles_are_explicit(self) -> None:
        self.assertEqual(pilot.profile_flags("unsat"), ("--unsat",))
        self.assertEqual(pilot.profile_flags("plain"), ("--plain",))
        self.assertEqual(pilot.profile_flags("default"), ())
        with self.assertRaisesRegex(ValueError, "unsupported"):
            pilot.profile_flags("mystery")

if __name__ == "__main__":
    unittest.main()
