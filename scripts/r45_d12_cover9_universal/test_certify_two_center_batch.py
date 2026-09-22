from __future__ import annotations

import unittest
from pathlib import Path

from . import certify_two_center_batch as batch
from . import generate_two_center_branches as two


class CertifyTwoCenterBatchTests(unittest.TestCase):
    def test_order_covers_every_remaining_case_once(self) -> None:
        self.assertEqual(set(batch.CASE_ORDER), set(two.CASES) - {(2, 0)})
        self.assertEqual(
            batch.CASE_ORDER[:5], ((1, 3), (0, 3), (0, 2), (1, 2), (1, 1))
        )

    def test_theorem_identity_is_case_specific(self) -> None:
        namespace, theorem, qualified = batch.theorem_identity(2, 3)
        self.assertEqual(theorem, "cover9_d8_two_center_p2_q3_unsat")
        self.assertEqual(qualified, f"{namespace}.{theorem}")
        source = batch.lean_source(
            Path(r"S:\proof\case.cnf"), Path(r"S:\proof\case.lrat"), 2, 3
        ).decode("utf-8")
        self.assertIn('"S:/proof/case.cnf"', source)
        self.assertIn(f"#print axioms {theorem}", source)

    def test_certified_historical_case_is_selectable_for_reproduction(self) -> None:
        self.assertEqual(batch.parse_case_specification("2,0"), (2, 0))

    def test_axiom_audit(self) -> None:
        log = """'N.t' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cover9_d8_two_center_p2_q3_unsat._native.native_decide.ax_1_1]
"""
        axioms = batch.parse_axioms(log)
        self.assertTrue(batch.axioms_allowed(axioms, 2, 3))
        self.assertFalse(batch.axioms_allowed(axioms + ["sorryAx"], 2, 3))
        self.assertFalse(
            batch.axioms_allowed(["sorryAx.native_decide.ax_1_1"], 2, 3)
        )
        self.assertFalse(batch.axioms_allowed(axioms, 2, 2))


if __name__ == "__main__":
    unittest.main()
