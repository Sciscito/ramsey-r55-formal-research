from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from . import publish_cover6_d7_r34_fcuj_core as publisher


class FCUjCorePublisherTests(unittest.TestCase):
    def test_preflight_is_local_honest_and_exact(self) -> None:
        report = publisher.preflight()
        self.assertEqual(report["status"], "PREFLIGHT_ONLY_NO_S_NO_SOLVER_NO_LEAN")
        self.assertEqual(report["leaf"], "FCUj_")
        self.assertEqual(report["core_clauses"], 1_104)
        self.assertIn("never invokes a SAT solver", report["solver_policy"])
        self.assertIn("no semantics", report["formal_boundary"])

    def test_frozen_external_identities_are_the_certified_fcuj_core(self) -> None:
        self.assertEqual(
            publisher.EXACT_EXTERNAL_ARTIFACTS[publisher.CORE_CNF_NAME],
            {
                "bytes": 51_238,
                "lines": 1_105,
                "sha256": "B166C31CD69B44D0480602DA904947588E71A7E70C13369E93CB61DD7C9DBC88",
            },
        )
        self.assertEqual(
            publisher.EXACT_EXTERNAL_ARTIFACTS[publisher.CORE_LRAT_NAME]["sha256"],
            "3069B9CCECC754D0480A8E07BB1FE197B4A25F85745205E963410B059956B739",
        )
        self.assertEqual(
            publisher.EXACT_EXTERNAL_ARTIFACTS[publisher.MAPPING_NAME]["sha256"],
            "F8E4DA255A42846DFCBC5968B776CEE05560C4EFE8CCBD0699294A525199F723",
        )
        self.assertEqual(
            publisher.EXTERNAL_MANIFEST["sha256"],
            "A5DE6752F17CF8A96BF6EC5053F19AFC5738E7DED22F582A995F00D178482564",
        )

    def test_replay_is_repo_relative_and_has_exact_endpoint(self) -> None:
        payload = publisher.tracked_replay_source()
        publisher.assert_portable(payload, "test replay")
        text = payload.decode("utf-8")
        self.assertIn(
            "../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/",
            text,
        )
        self.assertNotIn("S:/", text)
        self.assertNotIn("C:/", text)
        self.assertIn("cover6_d7_r34_fcuj__core_unsat", text)
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
                    publisher.FCUjPublicationError, "absolute path"
                ):
                    publisher.assert_portable(payload, "mutant")
        publisher.assert_portable(
            b"../../scripts/r45_d12_cover9_universal/core.cnf", "relative"
        )

    def test_mapping_parser_requires_exact_1104_strict_rows(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "core_clause_map.tsv"
            with path.open("w", encoding="ascii", newline="") as stream:
                stream.write("core_clause_id\tfcuj__clause_id\tclause_sha256\n")
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
                stream.write("core_clause_id\tfcuj__clause_id\tclause_sha256\n")
                stream.write(f"1\t1\t{'A' * 64}\n")
                stream.write(f"2\t1\t{'B' * 64}\n")
            with self.assertRaisesRegex(
                publisher.FCUjPublicationError, "strict/in-bounds"
            ):
                publisher.read_zero_based_indices(path)

    def test_generated_module_exposes_announced_interface(self) -> None:
        payload = publisher.lean_module_source(list(range(publisher.CORE_CLAUSES)))
        publisher.assert_portable(payload, "generated module")
        text = payload.decode("utf-8")
        for needle in (
            "namespace LRATCatcher.Tests.R44Cover6Master7R34FCUjCore",
            "def fCUjCatalogueIndex : Fin 9 := ⟨0, by decide⟩",
            "def fCUjICNFIndex : Fin 9 := ⟨1, by decide⟩",
            "def fCUjCoreZeroBasedIndices",
            "theorem fCUjCoreSelection_eq_certifiedCore",
            "theorem fCUjBranchSource_unsat",
            "theorem fCUjICNFBranchSource_unsat",
            "theorem fCUjRelabeled_unitTail_eval_true",
        ):
            self.assertIn(needle, text)
        self.assertIn("fCUjCoreZeroBasedIndices.size = 1104", text)

    def test_clause_hash_audit_rejects_mutant(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cnf = root / "core.cnf"
            mapping = root / "map.tsv"
            clause = b"1 -2 0\n"
            cnf.write_bytes(b"p cnf 66 1104\n" + clause)
            mapping.write_text(
                "core_clause_id\tfcuj__clause_id\tclause_sha256\n"
                + f"1\t1\t{hashlib.sha256(clause).hexdigest().upper()}\n",
                encoding="ascii",
                newline="",
            )
            publisher.verify_mapping_clause_hashes(mapping, cnf)
            mapping.write_text(
                "core_clause_id\tfcuj__clause_id\tclause_sha256\n"
                + f"1\t1\t{'0' * 64}\n",
                encoding="ascii",
                newline="",
            )
            with self.assertRaisesRegex(
                publisher.FCUjPublicationError, "clause hash mismatch"
            ):
                publisher.verify_mapping_clause_hashes(mapping, cnf)

    def test_clause_hash_audit_rejects_one_trailing_mapping_row(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cnf = root / "core.cnf"
            mapping = root / "map.tsv"
            clause = b"1 -2 0\n"
            digest = hashlib.sha256(clause).hexdigest().upper()
            cnf.write_bytes(b"p cnf 66 1104\n" + clause)
            mapping.write_text(
                "core_clause_id\tfcuj__clause_id\tclause_sha256\n"
                + f"1\t1\t{digest}\n"
                + f"2\t2\t{digest}\n",
                encoding="ascii",
                newline="",
            )
            with self.assertRaisesRegex(
                publisher.FCUjPublicationError, "CNF/map lengths differ"
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
        self.assertEqual(verification["status"], "PASS_EXACT_TRACKED_FCUJ_CORE")
        self.assertEqual(verification["index_count"], 1_104)
        self.assertEqual(
            verification["module"]["sha256"],
            "417DF92BCF5BB13613838E60D2B7AA26CE971BE6F5E3B845127B1393D558167B",
        )
        self.assertEqual(
            verification["reduced_pair"]["proof"]["rat_additions"], 0
        )
        self.assertEqual(
            verification["reduced_pair"]["proof"]["rup_additions"], 1_257
        )
        for name in (
            publisher.REDUCTION_NAME,
            publisher.REPLAY_NAME,
            publisher.ATTRIBUTES_NAME,
        ):
            publisher.assert_portable(
                (publisher.TRACKED_DIRECTORY / name).read_bytes(), name
            )

    def test_complete_publication_matches_golden_manifest_and_report(self) -> None:
        verification = publisher.verify_complete()
        self.assertEqual(
            verification["status"], "PASS_MASTER7_R34_FCUJ_TRACKED_CORE_V1"
        )
        self.assertEqual(
            verification["manifest"]["sha256"],
            "55116503F986898E807D377B2AD228DDC48BDC9F1C288819A90603F5A4583BD0",
        )
        self.assertEqual(
            verification["report"]["sha256"],
            "9189FB834A1D2CA700F5AE7A4904216E758AB1615AFDE5EC434286732E8446C1",
        )


if __name__ == "__main__":
    unittest.main()
