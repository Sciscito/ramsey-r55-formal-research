from __future__ import annotations

import unittest

from . import cover6_toy_chain as toy


class Cover6ToyChainTests(unittest.TestCase):
    def test_exact_component_semantics_and_unsat_statement(self) -> None:
        report = toy.preflight()
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["variables"], 10)
        self.assertEqual(report["ramsey_clauses"], 20)
        self.assertEqual(report["p3_embedding_blockers"], 60)
        self.assertEqual(report["clauses"], 80)
        self.assertEqual(report["assignments_checked"], 1024)
        self.assertEqual(report["ramsey_free_models"], 12)
        self.assertEqual(report["counterexamples"], 0)
        self.assertTrue(report["component_semantics_exact"])

    def test_dimacs_round_trip_is_exact(self) -> None:
        clauses = toy.formula_clauses()
        self.assertEqual(toy.parse_dimacs(toy.formula_bytes()), clauses)
        self.assertEqual(toy.verify_artifact()["status"], "PASS")
        self.assertEqual(toy.verify_lrat()["status"], "PASS")

    def test_manifest_closes_all_tracked_identities(self) -> None:
        report = toy.verify_manifest()
        self.assertEqual(report["status"], "PASS")
        self.assertTrue(report["all_manifest_identities_exact"])

    def test_corrupted_ramsey_literal_is_detected_semantically(self) -> None:
        base = list(toy.ramsey_clauses())
        first = base[0]
        base[0] = (-first[0], *first[1:])
        mismatch = toy.first_component_mismatch(base, toy.motif_blockers())
        self.assertIsNotNone(mismatch)
        self.assertEqual(mismatch["component"], 0)

    def test_corrupted_motif_polarity_is_detected_semantically(self) -> None:
        blockers = list(toy.motif_blockers())
        first = blockers[0]
        blockers[0] = (first[0], first[1], -first[2])
        mismatch = toy.first_component_mismatch(toy.ramsey_clauses(), blockers)
        self.assertIsNotNone(mismatch)
        self.assertEqual(mismatch["component"], 1)

    def test_zero_based_dimacs_corruption_is_rejected(self) -> None:
        lines = toy.formula_bytes().decode("ascii").splitlines()
        first_clause = lines[1].split()
        first_clause[0] = "0"
        lines[1] = " ".join(first_clause)
        payload = ("\n".join(lines) + "\n").encode("ascii")
        with self.assertRaisesRegex(ValueError, "malformed|out of range"):
            toy.parse_dimacs(payload)

    def test_trivially_unsat_wrong_encoding_is_rejected_before_replay(self) -> None:
        # Adding the empty clause creates an unquestionably UNSAT formula for
        # which a perfect LRAT could be produced, but it is not the declared
        # graph encoding and must fail the semantic/decomposition guard.
        wrong = toy.formula_bytes(toy.formula_clauses() + ((),))
        self.assertFalse(toy.eval_cnf(0, toy.parse_dimacs(wrong)))
        with self.assertRaisesRegex(ValueError, "independently reconstructed"):
            toy.verify_formula_payload(wrong, source="wrong-but-unsat.cnf")

    def test_corrupted_lrat_identity_is_rejected(self) -> None:
        payload = toy.DEFAULT_LRAT.read_bytes()
        corrupted = payload[:-1] + bytes([payload[-1] ^ 1])
        with self.assertRaisesRegex(ValueError, "LRAT identity"):
            toy.verify_lrat_payload(corrupted, source="corrupted.lrat")


if __name__ == "__main__":
    unittest.main()
