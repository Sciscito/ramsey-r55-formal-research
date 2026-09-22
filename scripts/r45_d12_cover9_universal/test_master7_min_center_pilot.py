from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path

from . import audit_cover6_d7_min_center_source as source_audit
from . import materialize_cover6_d7_min_center_master as materializer


REPORT = Path(__file__).with_name("MASTER7_MIN_CENTER_PILOT_V1.json")
REPORT_SHA256 = (
    "12492F5291582AB59D204EF064CE3A794DD83814E388CF28991259DA8363E5B3"
)


class Master7MinCenterPilotReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = REPORT.read_bytes()
        cls.report = json.loads(cls.payload)

    def test_report_is_the_frozen_bounded_unknown_checkpoint(self) -> None:
        self.assertEqual(hashlib.sha256(self.payload).hexdigest().upper(), REPORT_SHA256)
        self.assertEqual(self.report["schema_version"], 1)
        self.assertEqual(self.report["status"], "UNKNOWN_AT_CONFLICT_LIMIT")
        self.assertEqual(self.report["result"]["solver_status"], "UNKNOWN")
        self.assertEqual(self.report["result"]["termination"], "conflict limit")
        self.assertEqual(self.report["result"]["conflicts"], 100_003)
        self.assertEqual(self.report["result"]["proof_status"], "none")
        self.assertFalse(self.report["solver"]["lrat_requested"])
        self.assertEqual(self.report["solver"]["jobs"], 1)

    def test_formula_identities_match_the_independent_source_audit(self) -> None:
        source = self.report["formula"]["source_f7"]
        master = self.report["formula"]["master7"]
        self.assertEqual(source["clauses"], source_audit.F7_CLAUSES)
        self.assertEqual(source["bytes"], source_audit.EXPECTED_F7_BYTES)
        self.assertEqual(source["sha256"], source_audit.EXPECTED_F7_SHA256)
        self.assertEqual(master["clauses"], source_audit.MASTER7_CLAUSES)
        self.assertEqual(master["bytes"], source_audit.EXPECTED_MASTER7_BYTES)
        self.assertEqual(master["sha256"], source_audit.EXPECTED_MASTER7_SHA256)
        self.assertEqual(master["normalization_clauses"], len(source_audit.EXTRA_CLAUSES))
        self.assertEqual(master["normalization_suffix_bytes"], len(materializer.EXTRA_PAYLOAD))
        self.assertTrue(master["body_reused_byte_for_byte"])

    def test_normalization_is_exactly_the_nine_audited_pairs(self) -> None:
        self.assertEqual(
            tuple(map(tuple, self.report["normalization"]["pairs"])),
            source_audit.EXPECTED_PAIRS,
        )
        self.assertEqual(
            self.report["normalization"]["source_audit_report"],
            "COVER6_D7_MIN_CENTER_SOURCE_AUDIT_V1.json",
        )
        self.assertIn("not yet composed", self.report["normalization"]["lean_min_center_scope"])

    def test_scope_does_not_turn_unknown_into_a_mathematical_claim(self) -> None:
        scope = self.report["scope"]
        self.assertIn("no SAT model", scope)
        self.assertIn("UNSAT result", scope)
        self.assertIn("new Ramsey-number bound", scope)
        self.assertIn("not justified", self.report["result"]["scientific_interpretation"])


if __name__ == "__main__":
    unittest.main()
