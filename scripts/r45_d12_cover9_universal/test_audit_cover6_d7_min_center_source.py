from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from . import audit_cover6_d7_min_center_source as audit


REPORT = Path(audit.__file__).with_name("COVER6_D7_MIN_CENTER_SOURCE_AUDIT_V1.json")


class Cover6D7MinCenterQuickTests(unittest.TestCase):
    def test_dimacs_edge_ranges_are_exact(self) -> None:
        self.assertEqual(
            tuple(audit.global_edge(0, vertex) for vertex in range(1, 12)),
            tuple(range(1, 12)),
        )
        self.assertEqual(
            tuple(audit.global_edge(1, vertex) for vertex in range(2, 8)),
            tuple(range(12, 18)),
        )
        self.assertEqual(
            tuple(audit.global_edge(1, vertex) for vertex in range(8, 12)),
            tuple(range(18, 22)),
        )

    def test_clause_arithmetic_is_the_exact_d7_layout(self) -> None:
        self.assertEqual(
            audit.arithmetic_counts(),
            {
                "base": 699,
                "root_free_k7": 4_127_760,
                "root_containing_k6": 183_960,
                "f7": 4_312_419,
                "normalization_extras": 9,
                "master7": 4_312_428,
            },
        )

    def test_nine_clauses_encode_exactly_the_nine_pairs(self) -> None:
        result = audit.audit_extra_partition()
        self.assertEqual(result["models"], 9)
        self.assertEqual(
            tuple(map(tuple, result["pairs"])),
            ((1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)),
        )
        self.assertTrue(result["all_models_are_two_sorted_prefixes"])
        self.assertTrue(result["exactly_nine_minimum_center_cases"])

    def test_every_normalization_clause_is_semantically_essential(self) -> None:
        for removed in range(len(audit.EXTRA_CLAUSES)):
            with self.subTest(removed=removed):
                mutant = (
                    audit.EXTRA_CLAUSES[:removed]
                    + audit.EXTRA_CLAUSES[removed + 1 :]
                )
                result = audit.audit_extra_partition(mutant, require_exact=False)
                self.assertFalse(result["exactly_nine_minimum_center_cases"])

    def test_literal_polarity_mutant_is_rejected(self) -> None:
        mutant = ((-12,),) + audit.EXTRA_CLAUSES[1:]
        result = audit.audit_extra_partition(mutant, require_exact=False)
        self.assertFalse(result["exactly_nine_minimum_center_cases"])

    def test_nine_extra_lines_add_exactly_seventy_three_bytes(self) -> None:
        self.assertEqual(sum(map(len, map(audit.clause_line, audit.EXTRA_CLAUSES))), 73)
        self.assertEqual(
            audit.EXPECTED_MASTER7_BYTES - audit.EXPECTED_F7_BYTES,
            73,
        )

    def test_tracked_d8_payload_metadata_has_the_reused_suffixes(self) -> None:
        report, digest = audit.read_d8_report()
        self.assertEqual(
            digest,
            "0F04DC3992BE3E87493E369305FB608DD44AE1205363CCBCCCAC601C5CDFB34B",
        )
        self.assertEqual(
            tuple(
                report["source_payloads"]["full_k7_conditioned_cubes"][
                    "neighbour_counts"
                ]
            ),
            (4, 5, 6, 7),
        )
        self.assertEqual(
            tuple(
                report["source_payloads"]["projected_k6_conditioned_cubes"][
                    "neighbour_counts"
                ]
            ),
            (3, 4, 5),
        )

    def test_frozen_stream_fingerprints_are_complete(self) -> None:
        self.assertEqual(audit.EXPECTED_F7_BYTES, 246_507_515)
        self.assertEqual(
            audit.EXPECTED_F7_SHA256,
            "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C",
        )
        self.assertEqual(audit.EXPECTED_MASTER7_BYTES, 246_507_588)
        self.assertEqual(
            audit.EXPECTED_MASTER7_SHA256,
            "DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE",
        )

    def test_tracked_report_matches_the_frozen_fingerprint(self) -> None:
        self.assertTrue(REPORT.is_file())
        report = json.loads(REPORT.read_text(encoding="utf-8"))
        self.assertEqual(report["status"], "PASS_EXACT_D7_MIN_CENTER_SOURCE_AUDIT")
        self.assertEqual(
            report["fingerprints"]["f7"]["sha256"],
            audit.EXPECTED_F7_SHA256,
        )
        self.assertEqual(
            report["fingerprints"]["master7_min_center"]["sha256"],
            audit.EXPECTED_MASTER7_SHA256,
        )
        self.assertFalse(report["normalization_boundary"]["formalized_here"])
        self.assertEqual(
            report["dimacs_convention"]["root_assignment"],
            {
                "positive_variables": [1, 2, 3, 4, 5, 6, 7],
                "negative_variables": [8, 9, 10, 11],
            },
        )


@unittest.skipUnless(
    os.environ.get("RAMSEY_COVER6_D7_FULL") == "1",
    "set RAMSEY_COVER6_D7_FULL=1 for the bounded full stream reconstruction",
)
class Cover6D7MinCenterFullTests(unittest.TestCase):
    def test_full_audit_reconstructs_payloads_and_both_streams(self) -> None:
        result = audit.full_audit()
        self.assertEqual(result["status"], "PASS_EXACT_D7_MIN_CENTER_SOURCE_AUDIT")
        self.assertEqual(
            result["fingerprints"]["f7"]["sha256"], audit.EXPECTED_F7_SHA256
        )
        self.assertEqual(
            result["fingerprints"]["master7_min_center"]["sha256"],
            audit.EXPECTED_MASTER7_SHA256,
        )
        self.assertTrue(all(result["payloads"]["reuse_checks"].values()))


if __name__ == "__main__":
    unittest.main()
