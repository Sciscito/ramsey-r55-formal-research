from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path, PurePosixPath

from . import certify_two_center_batch as certify
from . import consolidate_two_center_certificates as consolidate
from . import generate_two_center_branches as two


class ConsolidatedCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest = json.loads(
            (consolidate.Path(__file__).with_name("TWO_CENTER_CERTIFICATES.json")).read_text(
                encoding="utf-8"
            )
        )

    def test_schema_and_case_cover(self) -> None:
        self.assertEqual(self.manifest["schema_version"], 2)
        self.assertEqual(
            self.manifest["status"],
            "THIRTEEN_OF_THIRTEEN_EXACT_CNFS_LEAN_LRAT_CERTIFIED",
        )
        self.assertEqual(self.manifest["certificate_count"], 13)
        cases = {tuple(row["case"]) for row in self.manifest["cases"]}
        self.assertEqual(cases, set(two.CASES))

    def test_formula_identities_match_generator_constants(self) -> None:
        for row in self.manifest["cases"]:
            case = tuple(row["case"])
            formula = row["formula"]
            self.assertEqual(
                (formula["clauses"], formula["bytes"], formula["sha256"]),
                two.EXPECTED_CASE_RESULTS[case],
            )

    def test_replays_have_exact_theorem_and_axioms(self) -> None:
        for row in self.manifest["cases"]:
            p, q = row["case"]
            replay = row["lean_replay"]
            self.assertEqual(replay["status"], "LEAN_LRAT_REPLAY_SUCCEEDED")
            self.assertEqual(replay["theorem"], certify.theorem_identity(p, q)[2])
            self.assertTrue(certify.axioms_allowed(replay["axioms"], p, q))
            self.assertEqual(row["solver"]["flags"], list(certify.SOLVER_FLAGS))

    def test_aggregates_and_portable_artifact_paths(self) -> None:
        sizes = [row["lrat"]["bytes"] for row in self.manifest["cases"]]
        self.assertEqual(self.manifest["total_lrat_bytes"], sum(sizes))
        self.assertEqual(self.manifest["maximum_lrat_bytes"], max(sizes))
        self.assertEqual(len({row["lrat"]["sha256"] for row in self.manifest["cases"]}), 13)
        for row in self.manifest["cases"]:
            for section in (
                "formula",
                "lrat",
                "source_certificate",
                "source_batch_manifest",
            ):
                path = PurePosixPath(row[section]["artifact_path"])
                self.assertFalse(path.is_absolute())
                self.assertNotIn("..", path.parts)
                self.assertEqual(path.parts[0], two.OUTPUT_DIRECTORY)
        self.assertEqual(
            self.manifest["artifact_root_policy"]["required_storage"],
            "absolute path on drive S:",
        )

        def keys(value: object) -> set[str]:
            if isinstance(value, dict):
                nested = (keys(item) for item in value.values())
                return set(value) | set().union(*nested)
            if isinstance(value, list):
                return set().union(*(keys(item) for item in value))
            return set()

        self.assertNotIn("local_path", keys(self.manifest))
    def test_p2_q0_three_generation_audit(self) -> None:
        audit = self.manifest["p2_q0_determinism_audit"]
        self.assertEqual(audit["identical_generations"], 3)
        identities = {
            (row["bytes"], row["sha256"])
            for row in [audit["canonical"], *audit["historical"]]
        }
        self.assertEqual(len(identities), 1)

    def test_verify_manifest_requires_exact_json_content(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            path.write_text(json.dumps(self.manifest), encoding="utf-8")
            consolidate.verify_manifest(self.manifest, path)
            path.write_text(
                json.dumps({**self.manifest, "certificate_count": 12}),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "consolidated manifest mismatch"):
                consolidate.verify_manifest(self.manifest, path)


if __name__ == "__main__":
    unittest.main()
