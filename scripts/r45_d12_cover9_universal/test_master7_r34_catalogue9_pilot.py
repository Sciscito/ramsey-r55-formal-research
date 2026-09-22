from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path

from . import materialize_cover6_d7_r34_catalogue_icnf as materializer


REPORT = Path(__file__).with_name("MASTER7_R34_CATALOGUE9_PILOT_V1.json")
REPORT_SHA256 = (
    "205E5F05132D7EDDA4C8ED14A8773CA12EB7BAEC2CB79EEC3391DD855071C323"
)


class Master7R34Catalogue9PilotReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = REPORT.read_bytes()
        cls.report = json.loads(cls.payload)

    def test_report_is_the_frozen_level_two_checkpoint(self) -> None:
        self.assertEqual(
            hashlib.sha256(self.payload).hexdigest().upper(), REPORT_SHA256
        )
        self.assertEqual(self.report["schema_version"], 1)
        self.assertEqual(
            self.report["status"], "UNSAT_WITHOUT_PROOF_ALL_NINE_R34_CUBES"
        )
        self.assertEqual(self.report["proof_level"]["level"], 2)
        self.assertIn(
            "must not be reported",
            self.report["proof_level"]["upper_bound"],
        )

    def test_source_and_incremental_identities_match_the_materializer(self) -> None:
        source = self.report["source"]["f7"]
        target = self.report["incremental_formula"]
        construction = target["construction"]
        self.assertEqual(source["clauses"], materializer.SOURCE_CLAUSES)
        self.assertEqual(source["bytes"], materializer.SOURCE_BYTES)
        self.assertEqual(source["lines"], materializer.SOURCE_LINES)
        self.assertEqual(source["sha256"], materializer.SOURCE_SHA256)
        self.assertEqual(target["bytes"], materializer.TARGET_BYTES)
        self.assertEqual(target["lines"], materializer.TARGET_LINES)
        self.assertEqual(target["sha256"], materializer.TARGET_SHA256)
        self.assertEqual(construction["cubes"], materializer.CUBE_COUNT)
        self.assertEqual(
            construction["assumption_literals_per_cube"],
            materializer.CUBE_LITERALS,
        )
        self.assertEqual(
            construction["cube_payload_bytes"],
            materializer.CUBE_PAYLOAD_BYTES,
        )
        self.assertEqual(
            construction["cube_payload_sha256"],
            materializer.CUBE_PAYLOAD_SHA256,
        )
        self.assertTrue(construction["f7_clause_body_reused_byte_for_byte"])
        self.assertFalse(construction["nine_separate_f7_copies_written"])

    def test_materializer_source_is_the_frozen_reported_program(self) -> None:
        path = Path(materializer.__file__)
        digest = hashlib.sha256(path.read_bytes()).hexdigest().upper()
        self.assertEqual(
            digest,
            self.report["incremental_formula"]["construction"][
                "materializer_sha256"
            ],
        )

    def test_cube_order_and_metrics_are_exact(self) -> None:
        rows = self.report["cube_order"]
        self.assertEqual(
            tuple(row["record"] for row in rows),
            materializer.ORDERED_R34_RECORDS,
        )
        self.assertEqual(
            tuple(tuple(row["degree_sequence"]) for row in rows),
            materializer.EXPECTED_DEGREE_SEQUENCES,
        )
        self.assertEqual(
            tuple(row["elapsed_seconds"] for row in rows),
            (0.172, 0.938, 2.469, 1.547, 2.516, 5.781, 4.297, 1.047, 4.375),
        )
        cumulative = tuple(row["cumulative_conflicts"] for row in rows)
        per_cube = tuple(row["cube_conflicts"] for row in rows)
        failed = tuple(row["failed_assumptions"] for row in rows)
        self.assertEqual(
            cumulative,
            (0, 507, 2599, 4203, 5011, 8955, 12429, 13709, 16893),
        )
        self.assertEqual(
            per_cube,
            (0, 507, 2092, 1604, 808, 3944, 3474, 1280, 3184),
        )
        self.assertEqual(failed, (14, 15, 15, 16, 14, 19, 17, 15, 11))
        self.assertEqual(
            per_cube,
            (cumulative[0],)
            + tuple(
                current - previous
                for previous, current in zip(cumulative, cumulative[1:])
            ),
        )
        self.assertEqual(sum(per_cube), self.report["result"]["conflicts"])
        self.assertTrue(all(row["status"] == "UNSATISFIABLE" for row in rows))
        self.assertTrue(rows[0]["is_exact_cover6_oracle"])
        self.assertEqual(rows[0]["cube_conflicts"], 0)
        self.assertTrue(
            all(not row["is_exact_cover6_oracle"] for row in rows[1:])
        )

    def test_solver_result_binary_logs_and_caps_are_frozen(self) -> None:
        solver = self.report["solver"]
        supervision = self.report["supervision"]
        result = self.report["result"]
        logs = self.report["logs"]
        self.assertEqual(solver["name"], "CaDiCaL")
        self.assertEqual(solver["version"], "2.1.2")
        self.assertEqual(
            solver["binary_sha256"],
            "AE6156A9C3BB46D8AC5E0A3892A5F11999EF6FD5F346304FD53DB9160FD5743B",
        )
        self.assertEqual(
            solver["flags"],
            ["--unsat", "--walk=false", "--verbose=1", "-c", "5000"],
        )
        self.assertFalse(solver["lrat_requested"])
        self.assertFalse(solver["drat_requested"])
        self.assertEqual(solver["jobs"], 1)
        self.assertEqual(
            supervision,
            {
                "wall_limit_seconds": 300,
                "rss_limit_mib": 1536,
                "log_limit_mib": 64,
                "limits_triggered": False,
            },
        )
        self.assertEqual(result["solver_status"], "UNSATISFIABLE")
        self.assertEqual(result["returncode"], 20)
        self.assertEqual(
            (
                result["cubes_solved"],
                result["cubes_unsatisfiable"],
                result["cubes_inconclusive"],
                result["cubes_satisfiable"],
            ),
            (9, 9, 0, 0),
        )
        self.assertEqual(result["conflicts"], 16_893)
        self.assertEqual(result["decisions"], 18_490)
        self.assertEqual(result["learned_clauses"], 16_723)
        self.assertEqual(result["total_process_seconds"], 28.75)
        self.assertEqual(result["total_real_seconds"], 29.16)
        self.assertEqual(result["maximum_resident_set_mib"], 1083.19)
        self.assertEqual(result["proof_status"], "none")
        self.assertEqual(
            logs["stdout"],
            {
                "name": "r34_catalogue9_5k.stdout.log",
                "bytes": 32819,
                "sha256": "72FFBEBDB4E260366B0708D4B3A58C9F1583089BE64361FA49CAAB39B4B0402E",
            },
        )
        self.assertEqual(
            logs["stderr"],
            {
                "name": "r34_catalogue9_5k.stderr.log",
                "bytes": 0,
                "sha256": "E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855",
            },
        )

    def test_formal_boundary_forbids_an_upgraded_claim(self) -> None:
        scope = self.report["scope"]
        boundary = self.report["formal_boundary"]
        self.assertIn("No LRAT", scope)
        self.assertIn("no composed S7 transport", scope)
        self.assertIn("no Lean cover6-d7 theorem", scope)
        self.assertIn("no new Ramsey-number bound", scope)
        self.assertIn("has not been composed", boundary["missing_composition"])
        self.assertIn("no LRAT", boundary["certificate_missing"])
        self.assertIn("Do not claim", boundary["claim_forbidden"])
        self.assertIn("replayable", self.report["next_action"])


if __name__ == "__main__":
    unittest.main()
