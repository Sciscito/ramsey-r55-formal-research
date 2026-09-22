import json
import unittest
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parent.parent
K43_PATH = REPOSITORY / "r55" / "K43_SCREEN_2026-08-07.json"
COVER6_PATH = (
    REPOSITORY
    / "scripts"
    / "r45_d12_cover9_universal"
    / "COVER6_D8_CHECKPOINT13.json"
)


class ResearchCheckpoint20260807Tests(unittest.TestCase):
    def test_k43_screen_summary_matches_rows(self):
        data = json.loads(K43_PATH.read_text(encoding="utf-8"))
        rows = data["results"]
        self.assertEqual(len(rows), data["summary"]["selected"])
        self.assertEqual(
            sum(row["status"] == "UNSAT_WITHOUT_LRAT" for row in rows),
            data["summary"]["unsat_without_lrat"],
        )
        self.assertEqual(
            sum(row["status"] == "UNKNOWN" for row in rows),
            data["summary"]["unknown_at_conflict_limit"],
        )
        self.assertEqual(data["summary"]["cnfs_retained"], 0)
        self.assertEqual(len({row["branch"] for row in rows}), len(rows))

    def test_cover6_checkpoint_is_complete_and_arithmetically_consistent(self):
        data = json.loads(COVER6_PATH.read_text(encoding="utf-8"))
        rows = data["results"]
        cases = {(row["p"], row["q"]) for row in rows}
        self.assertEqual(cases, {tuple(case) for case in data["case_order"]})
        self.assertEqual(len(rows), data["formula_totals"]["cases"])
        self.assertEqual(
            sum(row["clauses"] for row in rows),
            data["formula_totals"]["clauses"],
        )
        self.assertEqual(
            sum(row["bytes"] for row in rows),
            data["formula_totals"]["bytes"],
        )
        self.assertEqual(
            sum(row["conflicts"] for row in rows),
            data["solver_batch"]["total_conflicts"],
        )
        self.assertFalse(data["solver"]["proof_emitted"])
        self.assertEqual(
            data["result_status_for_every_case"],
            "UNSAT_WITHOUT_PROOF",
        )


if __name__ == "__main__":
    unittest.main()
