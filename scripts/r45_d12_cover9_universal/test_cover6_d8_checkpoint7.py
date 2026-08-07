from __future__ import annotations

import json
import re
import unittest
from pathlib import Path

from . import generate_complement_closed_cover6_two_center as two


HERE = Path(__file__).resolve().parent
CHECKPOINT = HERE / "COVER6_D8_CHECKPOINT7.json"
SHA256 = re.compile(r"^[0-9A-F]{64}$")


class Cover6D8Checkpoint7Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(CHECKPOINT.read_text(encoding="utf-8"))

    def test_partial_partition_is_honest_and_complete(self) -> None:
        split = self.data["two_center_split"]
        completed = {tuple(case) for case in split["completed_cases"]}
        missing = {tuple(case) for case in split["missing_cases"]}
        self.assertFalse(completed & missing)
        self.assertEqual(completed | missing, set(two.cases(8)))
        self.assertEqual(len(completed), 7)
        self.assertEqual(len(missing), 6)
        self.assertEqual(split["explicit_unit_clauses_per_case"], 21)

    def test_all_completed_cases_are_proof_free_only(self) -> None:
        rows = self.data["cases"]
        self.assertEqual({(row["p"], row["q"]) for row in rows}, {
            tuple(case) for case in self.data["two_center_split"]["completed_cases"]
        })
        self.assertTrue(all(row["status"] == "UNSAT_WITHOUT_PROOF" for row in rows))
        self.assertFalse(self.data["certified"])
        self.assertFalse(self.data["solver"]["proof_emitted"])
        self.assertEqual(self.data["lrat_status"], "not generated")

    def test_all_frozen_hashes_are_uppercase_sha256(self) -> None:
        hashes = [
            self.data["source_cover6"]["sha256"],
            self.data["local_reduction"]["mask_sha256"],
            self.data["local_reduction"]["cube_sha256"],
            self.data["generated_degree_8_formula"]["sha256"],
            self.data["two_center_split"]["partial_manifest_sha256"],
            self.data["solver"]["sha256"],
            self.data["solver"]["batch_manifest_sha256"],
            *(row["sha256"] for row in self.data["cases"]),
        ]
        self.assertTrue(all(SHA256.fullmatch(digest) for digest in hashes))


if __name__ == "__main__":
    unittest.main()
