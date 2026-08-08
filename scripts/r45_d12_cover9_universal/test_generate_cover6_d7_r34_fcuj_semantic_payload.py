from __future__ import annotations

import hashlib
import shutil
import tempfile
import unittest
from pathlib import Path

from . import generate_cover6_d7_r34_core_semantic_payload as generator


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
CORE_DIRECTORY = HERE / "master7_r34_fcuj_core"
PAYLOAD_PATH = HERE / "MASTER7_R34_FCUJ_CORE_SEMANTIC_WITNESSES_V1.bin"
MANIFEST_PATH = HERE / "MASTER7_R34_FCUJ_CORE_SEMANTIC_PAYLOAD_V1.json"
CORE_MODULE = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master7R34FCUjCore.lean"
)


class FCUjCoreSemanticPayloadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.bundle = generator.build_bundle(
            CORE_DIRECTORY,
            "FCUj_",
            reference_core_module=None,
            reference_core_indices_definition=None,
            reference_semantics_module=None,
            reference_witness_definition=None,
        )

    def test_end_to_end_exact_taxonomy_polarities_and_payload(self) -> None:
        report = self.bundle.manifest
        self.assertEqual(
            report["status"],
            "PASS_EXACT_D7_R34_SELECTED_CORE_SEMANTIC_PAYLOAD",
        )
        self.assertEqual(
            report["taxonomy"]["family_counts"],
            {
                "base": 98,
                "root_free_k7": 476,
                "root_containing_k6": 514,
                "unit": 16,
            },
        )
        self.assertEqual(
            report["taxonomy"]["unit_tail"],
            {
                "retained_positions_zero_based": [
                    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 17, 18
                ],
                "retained_literals": [
                    -12, -13, 14, -15, 16, -17, -22, -23,
                    24, -25, 26, -31, -32, 39, 41, 46,
                ],
            },
        )
        payload = report["witness_payload"]
        self.assertEqual(payload["entries"], 990)
        self.assertEqual(payload["characters"], 2_475)
        self.assertEqual(
            payload["sha256"],
            "1509D60BF036DB9C8333357EA18B9C0E57C7FA14DF186F6C32EAE765F22DF97D",
        )
        self.assertEqual(
            payload["sections"],
            {
                "root_free_k7": {"entry_offset": 0, "entries": 476},
                "root_containing_k6": {
                    "entry_offset": 476,
                    "entries": 514,
                    "canonical_lift_order": "minimum (fixed, ones)",
                    "lift_multiplicity_counts": {"1": 514},
                },
            },
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
            "8EAFA4E28B838A3F9AEA39B358C9D60659EDD07A5ECDF6B7BA69B204CBB0EC53",
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

    def test_tracked_core_index_table_exactly_matches_mapping(self) -> None:
        linked = generator.build_bundle(
            CORE_DIRECTORY,
            "FCUj_",
            reference_core_module=CORE_MODULE,
            reference_core_indices_definition="fCUjCoreZeroBasedIndices",
            reference_semantics_module=None,
            reference_witness_definition=None,
        )
        reference = linked.manifest["lean_consumer_contract"][
            "core_index_reference"
        ]
        self.assertEqual(reference["entries"], 1_104)
        self.assertTrue(reference["exactly_matches_mapping"])

    @staticmethod
    def _copy_core(directory: Path) -> None:
        spec = generator.select_leaf("FCUj_")
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
                    "FCUj_",
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
            row_index = next(
                index
                for index, line in enumerate(lines[1:], 1)
                if line.split("\t")[1] == "4312435"
            )
            fields = lines[row_index].split("\t")
            fields[1] = "4312434"
            lines[row_index] = "\t".join(fields)
            mapping.write_text("\n".join(lines) + "\n", encoding="ascii", newline="")
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "branchSource clause mismatch",
            ):
                generator.build_bundle(
                    directory,
                    "FCUj_",
                    reference_core_module=None,
                    reference_core_indices_definition=None,
                    reference_semantics_module=None,
                    reference_witness_definition=None,
                )

    def test_clause_polarity_mutant_with_updated_hash_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            self._copy_core(directory)
            spec = generator.select_leaf("FCUj_")
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
                    "FCUj_",
                    reference_core_module=None,
                    reference_core_indices_definition=None,
                    reference_semantics_module=None,
                    reference_witness_definition=None,
                )

    def test_tracked_witness_payload_mutant_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            payload = Path(temporary) / "mutated.bin"
            original = PAYLOAD_PATH.read_bytes()
            payload.write_bytes(bytes((original[0] ^ 1,)) + original[1:])
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "generated artifact differs",
            ):
                generator.verify_artifacts(
                    self.bundle,
                    payload,
                    MANIFEST_PATH,
                )


if __name__ == "__main__":
    unittest.main()
