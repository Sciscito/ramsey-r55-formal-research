from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from . import publish_cover6_d7_r34_fodpo_core as publisher


class FoDPOCorePublisherTests(unittest.TestCase):
    def test_preflight_is_local_honest_and_exact(self) -> None:
        report = publisher.preflight()
        self.assertEqual(report["status"], "PREFLIGHT_ONLY_NO_S_NO_SOLVER_NO_LEAN")
        self.assertEqual(report["leaf"], "FoDPO")
        self.assertEqual(report["core_clauses"], 7_686)
        self.assertIn("never invokes a SAT solver", report["solver_policy"])
        self.assertIn("no semantics", report["formal_boundary"])

    def test_frozen_external_identities_are_the_certified_fodpo_core(self) -> None:
        self.assertEqual(
            publisher.EXACT_EXTERNAL_ARTIFACTS[publisher.CORE_CNF_NAME],
            {
                "bytes": 388_178,
                "lines": 7_687,
                "sha256": "5AD1DA30B83A78BE10A9029D4B885B233F0FCDE6F57747260231DFFBA6063B45",
            },
        )
        self.assertEqual(
            publisher.EXACT_EXTERNAL_ARTIFACTS[publisher.CORE_LRAT_NAME]["sha256"],
            "9947702DC26FF5F97ABE7279014F309073196CE1F225CAA677EE496BA447E1C1",
        )
        self.assertEqual(
            publisher.EXACT_EXTERNAL_ARTIFACTS[publisher.MAPPING_NAME]["sha256"],
            "D1BE4CB5C4F2DC989A70C58E95A386F360FCF2D5351108545F435BA8B2EE62D8",
        )
        self.assertEqual(
            publisher.EXTERNAL_MANIFEST["sha256"],
            "D64864D8F75555BCBE8A4A68239A9FCFD18394C556898B73DDD023A61B5813C2",
        )

    def test_replay_is_repo_relative_and_has_exact_endpoint(self) -> None:
        payload = publisher.tracked_replay_source()
        publisher.assert_portable(payload, "test replay")
        text = payload.decode("utf-8")
        self.assertIn(
            "../../scripts/r45_d12_cover9_universal/master7_r34_fodpo_core/",
            text,
        )
        self.assertNotIn("S:/", text)
        self.assertNotIn("C:/", text)
        self.assertIn("cover6_d7_r34_fodpo_core_unsat", text)
        self.assertIn("#print axioms", text)

    def test_attributes_freeze_every_byte_sensitive_family(self) -> None:
        self.assertEqual(
            publisher.attributes_source(),
            b"*.cnf binary\n*.lrat binary\n*.tsv binary\n*.json -text\n"
            b"*.lean -text\n*.log -text\n",
        )

    def test_path_portability_rejects_drive_unc_and_file_uri(self) -> None:
        for payload in (
            b'C:\\cache\\core.cnf',
            b'S:/cache/core.cnf',
            b'"\\\\server\\share\\core.cnf"',
            b"file:///tmp/core.cnf",
        ):
            with self.subTest(payload=payload):
                with self.assertRaisesRegex(
                    publisher.FoDPOPublicationError, "absolute path"
                ):
                    publisher.assert_portable(payload, "mutant")
        publisher.assert_portable(
            b"../../scripts/r45_d12_cover9_universal/core.cnf", "relative"
        )

    def test_mapping_parser_requires_exact_7686_strict_rows(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "core_clause_map.tsv"
            with path.open("w", encoding="ascii", newline="") as stream:
                stream.write("core_clause_id\tfodpo_clause_id\tclause_sha256\n")
                for value in range(1, publisher.CORE_CLAUSES + 1):
                    stream.write(f"{value}\t{value}\t{'A' * 64}\n")
            indices = publisher.read_zero_based_indices(path)
            self.assertEqual(len(indices), publisher.CORE_CLAUSES)
            self.assertEqual(indices[:3], [0, 1, 2])
            self.assertEqual(indices[-1], publisher.CORE_CLAUSES - 1)

    def test_mapping_parser_rejects_duplicate_source_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "core_clause_map.tsv"
            with path.open("w", encoding="ascii", newline="") as stream:
                stream.write("core_clause_id\tfodpo_clause_id\tclause_sha256\n")
                stream.write(f"1\t1\t{'A' * 64}\n")
                stream.write(f"2\t1\t{'B' * 64}\n")
            with self.assertRaisesRegex(
                publisher.FoDPOPublicationError, "strict/in-bounds"
            ):
                publisher.read_zero_based_indices(path)

    def test_generated_module_exposes_announced_interface(self) -> None:
        payload = publisher.lean_module_source(list(range(publisher.CORE_CLAUSES)))
        publisher.assert_portable(payload, "generated module")
        text = payload.decode("utf-8")
        for needle in (
            "namespace LRATCatcher.Tests.R44Cover6Master7R34FoDPOCore",
            "def foDPOCatalogueIndex : Fin 9 := ⟨6, by decide⟩",
            "def foDPOICNFIndex : Fin 9 := ⟨6, by decide⟩",
            "def foDPOCoreZeroBasedIndices",
            "theorem foDPOCoreSelection_eq_certifiedCore",
            "theorem foDPOBranchSource_unsat",
            "theorem foDPOICNFBranchSource_unsat",
            "theorem foDPORelabeled_unitTail_eval_true",
        ):
            self.assertIn(needle, text)
        self.assertIn("foDPOCoreZeroBasedIndices.size = 7686", text)

    def test_clause_hash_audit_rejects_mutant(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cnf = root / "core.cnf"
            mapping = root / "map.tsv"
            clause = b"1 -2 0\n"
            cnf.write_bytes(b"p cnf 66 7686\n" + clause)
            mapping.write_text(
                "core_clause_id\tfodpo_clause_id\tclause_sha256\n"
                + f"1\t1\t{hashlib.sha256(clause).hexdigest().upper()}\n",
                encoding="ascii",
                newline="",
            )
            publisher.verify_mapping_clause_hashes(mapping, cnf)
            mapping.write_text(
                "core_clause_id\tfodpo_clause_id\tclause_sha256\n"
                + f"1\t1\t{'0' * 64}\n",
                encoding="ascii",
                newline="",
            )
            with self.assertRaisesRegex(
                publisher.FoDPOPublicationError, "clause hash mismatch"
            ):
                publisher.verify_mapping_clause_hashes(mapping, cnf)

    def test_clause_hash_audit_rejects_one_trailing_mapping_row(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cnf = root / "core.cnf"
            mapping = root / "map.tsv"
            clause = b"1 -2 0\n"
            digest = hashlib.sha256(clause).hexdigest().upper()
            cnf.write_bytes(b"p cnf 66 7686\n" + clause)
            mapping.write_text(
                "core_clause_id\tfodpo_clause_id\tclause_sha256\n"
                + f"1\t1\t{digest}\n"
                + f"2\t2\t{digest}\n",
                encoding="ascii",
                newline="",
            )
            with self.assertRaisesRegex(
                publisher.FoDPOPublicationError, "CNF/map lengths differ"
            ):
                publisher.verify_mapping_clause_hashes(mapping, cnf)

    def test_write_new_refuses_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            target = root / "new.bin"
            with mock.patch.object(publisher, "REPOSITORY", root):
                publisher.write_new(target, b"first")
                with self.assertRaises(FileExistsError):
                    publisher.write_new(target, b"second")
            self.assertEqual(target.read_bytes(), b"first")

    def test_tracked_core_and_generated_module_match_exact_golden_data(self) -> None:
        verification = publisher.verify_portable_core()
        self.assertEqual(verification["status"], "PASS_EXACT_TRACKED_FODPO_CORE")
        self.assertEqual(verification["index_count"], 7_686)
        self.assertEqual(
            verification["module"]["sha256"],
            "09F9244CD512AEDE1BFCDF6434E893F9695B6E08B703DC3D87E598B5083540B8",
        )
        self.assertEqual(
            verification["reduced_pair"]["proof"]["rat_additions"], 0
        )
        self.assertEqual(
            verification["reduced_pair"]["proof"]["rup_additions"], 12_107
        )
        for name in (
            publisher.REDUCTION_NAME,
            publisher.REPLAY_NAME,
            publisher.ATTRIBUTES_NAME,
        ):
            publisher.assert_portable(
                (publisher.TRACKED_DIRECTORY / name).read_bytes(), name
            )


if __name__ == "__main__":
    unittest.main()
