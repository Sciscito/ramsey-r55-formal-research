from __future__ import annotations

import hashlib
import shutil
import tempfile
import unittest
from pathlib import Path

from . import generate_cover6_d7_r34_core_semantic_payload as generator


HERE = Path(__file__).resolve().parent
CORE_DIRECTORY = HERE / "master7_r34_fodpo_core"
PAYLOAD_PATH = HERE / "MASTER7_R34_FODPO_CORE_SEMANTIC_WITNESSES_V1.bin"
MANIFEST_PATH = HERE / "MASTER7_R34_FODPO_CORE_SEMANTIC_PAYLOAD_V1.json"


class FoDPOCoreSemanticPayloadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.bundle = generator.build_bundle(
            CORE_DIRECTORY,
            "FoDPO",
            reference_core_module=None,
            reference_core_indices_definition=None,
            reference_semantics_module=None,
            reference_witness_definition=None,
        )

    def test_end_to_end_exact_taxonomy_and_payload(self) -> None:
        report = self.bundle.manifest
        self.assertEqual(
            report["status"],
            "PASS_EXACT_D7_R34_SELECTED_CORE_SEMANTIC_PAYLOAD",
        )
        self.assertEqual(
            report["taxonomy"]["family_counts"],
            {
                "base": 183,
                "root_free_k7": 4_221,
                "root_containing_k6": 3_264,
                "unit": 18,
            },
        )
        payload = report["witness_payload"]
        self.assertEqual(payload["entries"], 7_485)
        self.assertEqual(payload["characters"], 18_713)
        self.assertEqual(
            payload["sha256"],
            "A58428A50A1977ACF3237917107E4462110EAA4B1A62E7B22DD9DC3C17A9D5A2",
        )
        self.assertEqual(
            hashlib.sha256(self.bundle.payload).hexdigest().upper(),
            payload["sha256"],
        )
        self.assertTrue(
            report["taxonomy"]
            ["all_selected_clauses_equal_exact_python_reconstruction_of_branchSource"]
        )
        self.assertEqual(
            report["taxonomy"]["ordered_semantic_view_sha256"],
            "A929C65B050615DB4019E508180471DDDD02DA6386CD4A58BAC0ABE1183638D5",
        )
        self.assertIsNone(
            report["lean_consumer_contract"]["core_index_reference"]
        )
        self.assertIsNone(
            report["lean_consumer_contract"]["witness_table_reference"]
        )

    def test_tracked_artifacts_match_deterministic_rebuild(self) -> None:
        result = generator.verify_artifacts(
            self.bundle,
            PAYLOAD_PATH,
            MANIFEST_PATH,
        )
        self.assertEqual(
            result["status"],
            "PASS_TRACKED_D7_R34_CORE_SEMANTIC_ARTIFACTS_EXACT",
        )

    @staticmethod
    def _copy_core(directory: Path) -> None:
        spec = generator.select_leaf("FoDPO")
        base = spec.target_name.removesuffix(".cnf")
        for name in (f"{base}_core.cnf", "core_clause_map.tsv"):
            shutil.copyfile(CORE_DIRECTORY / name, directory / name)

    def test_mapping_order_mutant_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            self._copy_core(directory)
            mapping = directory / "core_clause_map.tsv"
            lines = mapping.read_text(encoding="ascii").splitlines()
            first = lines[1].split("\t")
            second = lines[2].split("\t")
            second[1] = first[1]
            lines[2] = "\t".join(second)
            mapping.write_text("\n".join(lines) + "\n", encoding="ascii", newline="")
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "not strictly increasing",
            ):
                generator.build_bundle(
                    directory,
                    "FoDPO",
                    reference_core_module=None,
                    reference_core_indices_definition=None,
                    reference_semantics_module=None,
                    reference_witness_definition=None,
                )

    def test_unit_source_index_mutant_is_rejected_by_exact_tail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            self._copy_core(directory)
            mapping = directory / "core_clause_map.tsv"
            lines = mapping.read_text(encoding="ascii").splitlines()
            fields = lines[-12].split("\t")
            self.assertEqual(fields[1], "4312427")
            fields[1] = "4312426"
            lines[-12] = "\t".join(fields)
            mapping.write_text("\n".join(lines) + "\n", encoding="ascii", newline="")
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "branchSource clause mismatch",
            ):
                generator.build_bundle(
                    directory,
                    "FoDPO",
                    reference_core_module=None,
                    reference_core_indices_definition=None,
                    reference_semantics_module=None,
                    reference_witness_definition=None,
                )

    def test_clause_polarity_mutant_with_updated_hash_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            self._copy_core(directory)
            spec = generator.select_leaf("FoDPO")
            base = spec.target_name.removesuffix(".cnf")
            cnf = directory / f"{base}_core.cnf"
            rows = cnf.read_bytes().splitlines(keepends=True)
            literals = tuple(map(int, rows[1].split()))
            mutant = (-literals[0], *literals[1:-1])
            rows[1] = generator.source.clause_line(mutant)
            cnf.write_bytes(b"".join(rows))

            mapping = directory / "core_clause_map.tsv"
            lines = mapping.read_text(encoding="ascii").splitlines()
            first = lines[1].split("\t")
            first[2] = hashlib.sha256(rows[1]).hexdigest().upper()
            lines[1] = "\t".join(first)
            mapping.write_text("\n".join(lines) + "\n", encoding="ascii", newline="")
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "branchSource clause mismatch",
            ):
                generator.build_bundle(
                    directory,
                    "FoDPO",
                    reference_core_module=None,
                    reference_core_indices_definition=None,
                    reference_semantics_module=None,
                    reference_witness_definition=None,
                )


if __name__ == "__main__":
    unittest.main()
