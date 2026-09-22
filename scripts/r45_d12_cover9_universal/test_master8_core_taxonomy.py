from __future__ import annotations

import json
import os
import unittest
from collections import Counter
from pathlib import Path

from . import analyze_master8_core_taxonomy as taxonomy
from . import exact_replay_cover6_d8 as replay
from . import master8_prefix_pilot as master


class Master8CoreTaxonomyTests(unittest.TestCase):
    @classmethod
    def tracked(cls) -> dict[str, object]:
        return json.loads(
            Path(taxonomy.__file__).with_name(taxonomy.REPORT_NAME).read_text(
                encoding="utf-8"
            )
        )

    def test_declarative_ranges_partition_the_master8_source(self) -> None:
        root_free, root_containing = taxonomy.declarative_ranges()
        self.assertEqual((root_free[0].first, root_free[-1].last), (718, 3_211_197))
        self.assertEqual(
            sum(item.last - item.first + 1 for item in root_free), 3_210_480
        )
        self.assertEqual(
            (root_containing[0].first, root_containing[-1].last),
            (3_211_198, 3_367_437),
        )
        self.assertEqual(
            sum(item.last - item.first + 1 for item in root_containing), 156_240
        )
        self.assertEqual(taxonomy.FINAL_FIRST, 3_367_438)
        self.assertEqual(taxonomy.FINAL_LAST, 3_367_459)

    def test_core_rows_have_exact_family_and_width_taxonomy(self) -> None:
        rows = taxonomy.core_rows()
        self.assertEqual(len(rows), 6_152)
        self.assertEqual(
            Counter(row.location.family for row in rows),
            {
                "base_ramsey": 221,
                "root_free_blocker": 3_514,
                "root_containing_blocker": 2_409,
                "final_22": 8,
            },
        )
        self.assertEqual(
            Counter(row.width for row in rows),
            {1: 1, 2: 7, 3: 39, 6: 182, 10: 1_661, 11: 748,
             15: 1_544, 16: 1_402, 17: 568},
        )
        self.assertFalse(
            any(abs(literal) <= 11 for row in rows for literal in row.clause)
        )
        self.assertEqual(
            self.tracked()["core"]["exact_taxonomy_row_sha256"],
            "CAB3314CD354215997823CC7FB37CC315DCDCAE4CA4684F5647AAAF46291EB67",
        )

    def test_final_22_reduce_exactly_to_core8_extras(self) -> None:
        rows = [
            row for row in taxonomy.core_rows()
            if row.location.family == "final_22"
        ]
        self.assertEqual(tuple(row.master_id for row in rows), taxonomy.CORE8_EXTRA_MASTER_IDS)
        self.assertEqual(tuple(row.clause for row in rows), taxonomy.CORE8_EXTRA_CLAUSES)
        self.assertEqual(
            taxonomy.CORE8_EXTRA_CLAUSES,
            (
                (12, -13), (13, -14),
                (15, -16), (16, -17), (17, -18),
                (19, -20), (20, -21), (-15,),
            ),
        )
        final = self.tracked()["sections"]["final_22"]
        self.assertEqual(final["root_units_retained"], 0)
        self.assertEqual(final["prefix_sort_clauses_retained"], 7)
        self.assertEqual(final["arithmetic_bounds_retained"], 1)

    def test_core8_extras_encode_sixteen_sorted_p_q_pairs(self) -> None:
        audit = taxonomy.audit_core8_extras()
        self.assertEqual(audit["status"], "PASS_EXACT_CORE8_FINITE_NORMALIZATION")
        self.assertEqual(audit["models_over_variables_12_to_21"], 16)
        self.assertEqual(
            {tuple(pair) for pair in audit["model_pairs"]},
            {(p, q) for p in range(4) for q in range(4)},
        )
        models = master.assignments(taxonomy.CORE8_EXTRA_CLAUSES)
        self.assertTrue(all(
            master.clause_satisfied(master.PREFIX_CLAUSES[2], model)
            for model in models
        ))
        self.assertEqual(master.PREFIX_CLAUSES[2], (14, -15))
        self.assertFalse(audit["cross_lower_bound_p_plus_q_ge_two_used"])
        self.assertFalse(audit["thirteen_case_partition_used"])

    def test_tracked_report_freezes_core8_fingerprint_and_compression(self) -> None:
        report = self.tracked()
        self.assertEqual(report["status"], "PASS_EXACT_MASTER8_CORE_TAXONOMY")
        formula = report["normalized_core8_variant"]["formula"]
        self.assertEqual(formula, {
            "bytes": taxonomy.CORE8_EXPECTED_BYTES,
            "clauses": taxonomy.CORE8_CLAUSES,
            "sha256": taxonomy.CORE8_EXPECTED_SHA256,
            "variables": replay.GLOBAL_VARIABLES,
            "widths": taxonomy.CORE8_EXPECTED_WIDTHS,
        })
        self.assertEqual(
            report["compression"]["conditioned_blocker_instances_retained"], 5_923
        )
        self.assertEqual(
            report["compression"]["distinct_conditioned_template_positions"], 1_355
        )
        self.assertEqual(
            report["compression"]["conditioned_stabilizer_orbits_touched"], 30
        )
        self.assertFalse(
            report["normalized_core8_variant"]["existing_lean_route"]
            ["thirteen_cases_needed"]
        )
        self.assertIn(
            "graph-level semantic satisfaction proof",
            report["normalized_core8_variant"]["formal_status"],
        )
        self.assertIn("graph-to-formula semantic bridge", report["scope"])

    def test_fast_reanalysis_matches_non_orbit_report_fields(self) -> None:
        generated = taxonomy.build_report(full=False)
        tracked = self.tracked()
        self.assertEqual(generated["inputs"], tracked["inputs"])
        self.assertEqual(generated["declarative_layout"], tracked["declarative_layout"])
        self.assertEqual(generated["core"], tracked["core"])
        self.assertEqual(
            generated["normalized_core8_variant"], tracked["normalized_core8_variant"]
        )
        for family in ("base_ramsey", "final_22"):
            self.assertEqual(
                generated["sections"][family], tracked["sections"][family]
            )
        for family in ("root_free_blockers", "root_containing_blockers"):
            generated_section = generated["sections"][family]
            tracked_section = tracked["sections"][family]
            for key, value in generated_section.items():
                if key != "conditions":
                    self.assertEqual(value, tracked_section[key])
            for observed, expected in zip(
                generated_section["conditions"], tracked_section["conditions"]
            ):
                for key, value in observed.items():
                    self.assertEqual(value, expected[key])

    @unittest.skipUnless(
        os.environ.get("RAMSEY_MASTER8_TAXONOMY_FULL") == "1",
        "set RAMSEY_MASTER8_TAXONOMY_FULL=1 for cube/orbit and 189 MB stream replay",
    )
    def test_full_taxonomy_matches_tracked_report(self) -> None:
        self.assertEqual(taxonomy.build_report(full=True), self.tracked())


if __name__ == "__main__":
    unittest.main()
