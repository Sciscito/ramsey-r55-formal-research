from __future__ import annotations

import hashlib
import io
import json
import os
import unittest
from pathlib import Path

from . import exact_replay_cover6_d8 as replay
from . import master8_prefix_pilot as master


class Master8PrefixPilotTests(unittest.TestCase):
    @classmethod
    def report(cls) -> dict[str, object]:
        path = Path(master.__file__).with_name("MASTER8_PREFIX_PILOT_V1.json")
        return json.loads(path.read_text(encoding="utf-8"))

    @classmethod
    def lrat_checkpoint(cls) -> dict[str, object]:
        path = Path(master.__file__).with_name("MASTER8_LRAT_CHECKPOINT_V1.json")
        return json.loads(path.read_text(encoding="utf-8"))

    def test_exact_root_prefix_and_bound_clauses(self) -> None:
        self.assertEqual(master.ROOT_UNITS, (
            (1,), (2,), (3,), (4,), (5,), (6,), (7,), (8,), (-9,), (-10,), (-11,)
        ))
        self.assertEqual(master.PREFIX_CLAUSES, (
            (12, -13), (13, -14), (14, -15), (15, -16),
            (16, -17), (17, -18), (19, -20), (20, -21),
        ))
        self.assertEqual(master.BOUND_CLAUSES, ((-15,), (13, 19), (12, 20)))

    def test_prefix_only_has_32_pairs_bounded_has_exactly_13(self) -> None:
        result = master.audit_partition()
        self.assertEqual(result["prefix_only_assignments"], 32)
        self.assertEqual(result["bounded_assignments"], 13)
        self.assertEqual(
            {tuple(pair) for pair in result["bounded_pairs"]}, set(replay.CASES)
        )

    def test_bounds_have_exact_arithmetic_meaning_on_all_prefix_pairs(self) -> None:
        models = master.assignments(master.PREFIX_CLAUSES)
        self.assertEqual(len(models), 32)
        for model in models:
            p, q = master.assignment_pair(model)
            self.assertEqual(
                master.clause_satisfied(master.BOUND_CLAUSES[0], model), p <= 3
            )
            self.assertEqual(
                master.satisfies(master.BOUND_CLAUSES[1:], model), 2 <= p + q
            )

    def test_mutated_prefix_polarity_does_not_encode_the_partition(self) -> None:
        mutated = ((-12, 13),) + master.PREFIX_CLAUSES[1:] + master.BOUND_CLAUSES
        pairs = {master.assignment_pair(model) for model in master.assignments(mutated)}
        self.assertNotEqual(pairs, set(replay.CASES))

    def test_mutated_bound_polarity_does_not_encode_the_partition(self) -> None:
        mutated_bounds = ((15,),) + master.BOUND_CLAUSES[1:]
        models = master.assignments(master.PREFIX_CLAUSES + mutated_bounds)
        pairs = {master.assignment_pair(model) for model in models}
        self.assertNotEqual(pairs, set(replay.CASES))

    def test_small_stream_has_exact_header_order_and_hash(self) -> None:
        clauses = ((1,), (2, -3), ())
        stream = io.BytesIO()
        result = master.stream_formula(clauses, len(clauses), stream)
        expected = b"p cnf 66 3\n1 0\n2 -3 0\n0\n"
        self.assertEqual(stream.getvalue(), expected)
        self.assertEqual(result["bytes"], len(expected))
        self.assertEqual(result["sha256"], hashlib.sha256(expected).hexdigest().upper())

    def test_tracked_report_is_bounded_and_honest(self) -> None:
        report = self.report()
        self.assertEqual(report["status"], "PASS_MASTER8_BOUNDED_FINGERPRINT")
        self.assertEqual(report["variant"], master.VARIANT_BOUNDED)
        self.assertEqual(report["partition"]["bounded_assignments"], 13)
        self.assertTrue(report["partition"]["exactly_historical_thirteen_cases"])
        self.assertEqual(report["formula"]["clauses"], replay.SOURCE_CLAUSES + 22)
        self.assertEqual(sum(report["formula"]["widths"].values()), report["formula"]["clauses"])
        self.assertEqual(report["formula"]["bytes"], master.BOUNDED_EXPECTED_BYTES)
        self.assertEqual(report["formula"]["sha256"], master.BOUNDED_EXPECTED_SHA256)
        self.assertIn("no SAT", report["scope"])

    def test_lrat_checkpoint_keeps_the_failed_replay_boundary_explicit(self) -> None:
        report = self.report()
        checkpoint = self.lrat_checkpoint()
        self.assertEqual(
            checkpoint["status"], "SUPERSEDED_BY_REDUCED_CORE_DUAL_REPLAY"
        )
        self.assertEqual(checkpoint["formula"]["sha256"], report["formula"]["sha256"])
        self.assertEqual(checkpoint["formula"]["clauses"], report["formula"]["clauses"])
        self.assertEqual(checkpoint["solver"]["conflicts"], 4_598)
        self.assertTrue(checkpoint["solver"]["proof_checked_during_generation"])
        self.assertEqual(checkpoint["lrat"]["bytes"], 128_131_809)
        self.assertEqual(
            checkpoint["lrat"]["sha256"],
            "B2ECDACD2D99CD6EA2929C0B370C6AAFD74FE78FDE20FFBDFE68B7D0EF860505",
        )
        self.assertEqual(
            checkpoint["lean_replay_pilot"]["status"],
            "RSS_LIMIT_BEFORE_THEOREM",
        )
        self.assertFalse(checkpoint["lean_replay_pilot"]["theorem_produced"])
        self.assertEqual(
            checkpoint["superseded_by"], "master8_core/MANIFEST.json"
        )
        self.assertIn("No formal UNSAT theorem", checkpoint["claim_boundary"])

    @unittest.skipUnless(
        os.environ.get("RAMSEY_MASTER8_FULL") == "1",
        "set RAMSEY_MASTER8_FULL=1 for the complete regenerated fingerprint",
    )
    def test_full_fingerprint_matches_report(self) -> None:
        generated = master.fingerprint(master.VARIANT_BOUNDED)
        report = self.report()
        self.assertEqual(generated["formula"], report["formula"])


if __name__ == "__main__":
    unittest.main()
