import unittest

from r45_d20_c10_vacuity import (
    DEFAULT_GRAPH_PATH,
    EXPECTED_DEGREES,
    EXPECTED_K43_TIGHT_AFTER,
    EXPECTED_K45_TIGHT_AFTER,
    OFFICIAL_GRAPH_BYTES,
    OFFICIAL_GRAPH_SHA256,
    VerificationError,
    derive_branch_counts,
    derive_minimum_anchor_vacuity,
    verify,
    verify_extremal_graph,
    verify_extremal_graph_bytes,
)


class R45D20C10VacuityTests(unittest.TestCase):
    def test_official_record_is_authenticated_and_ramsey_free(self):
        facts = verify_extremal_graph()
        self.assertEqual(facts.byte_count, 34)
        self.assertEqual(facts.sha256, OFFICIAL_GRAPH_SHA256)
        self.assertEqual(facts.order, 20)
        self.assertEqual(facts.edge_count, 100)
        self.assertEqual(facts.degrees, EXPECTED_DEGREES)
        self.assertEqual(facts.degree_multiplicities, ((9, 2), (10, 16), (11, 2)))
        self.assertEqual(facts.red_k4_count, 0)
        self.assertEqual(facts.independent_5_count, 0)

    def test_byte_change_is_rejected_before_graph_reasoning(self):
        corrupted = OFFICIAL_GRAPH_BYTES[:-2] + b"?\n"
        with self.assertRaises(VerificationError):
            verify_extremal_graph_bytes(corrupted)

    def test_minimum_anchor_d20_c10_is_empty(self):
        graph = verify_extremal_graph()
        facts = derive_minimum_anchor_vacuity(graph)
        self.assertEqual(facts.anchor_codegree, 10)
        self.assertEqual(facts.handshake_edge_lower_bound, 100)
        self.assertEqual(facts.trusted_extremal_edge_upper_bound, 100)
        self.assertFalse(facts.unique_extremal_graph_is_regular)
        self.assertTrue(facts.d20_c10_minimum_anchor_empty)

    def test_reduced_branch_totals(self):
        facts = derive_branch_counts()
        self.assertEqual(facts.eliminated_d20_c10_types, 313)
        self.assertEqual(facts.k43_before, 1_509)
        self.assertEqual(facts.k43_after, EXPECTED_K43_TIGHT_AFTER)
        self.assertEqual(facts.k45_before, 1_815)
        self.assertEqual(facts.k45_after, EXPECTED_K45_TIGHT_AFTER)

    def test_end_to_end_report(self):
        report = verify(DEFAULT_GRAPH_PATH)
        self.assertTrue(report.minimum_anchor.d20_c10_minimum_anchor_empty)
        self.assertEqual(report.branch_counts.k43_after, 1_196)
        self.assertEqual(report.branch_counts.k45_after, 1_502)
        self.assertIn("does not certify enumeration completeness", report.classification_scope)


if __name__ == "__main__":
    unittest.main()
