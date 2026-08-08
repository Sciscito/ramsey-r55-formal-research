from __future__ import annotations

import contextlib
import hashlib
import io
import shutil
import tempfile
import unittest
from pathlib import Path

from . import generate_cover6_d7_r34_core_semantic_payload as generator


class D7R34CoreSemanticPayloadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.bundle = generator.build_bundle()

    def test_fgravegow_end_to_end_exact_taxonomy_and_payload(self) -> None:
        report = self.bundle.manifest
        self.assertEqual(
            report["status"],
            "PASS_EXACT_D7_R34_SELECTED_CORE_SEMANTIC_PAYLOAD",
        )
        self.assertEqual(
            report["taxonomy"]["family_counts"],
            {
                "base": 168,
                "root_free_k7": 3_227,
                "root_containing_k6": 2_396,
                "unit": 16,
            },
        )
        payload = report["witness_payload"]
        self.assertEqual(payload["entries"], 5_623)
        self.assertEqual(payload["characters"], 14_058)
        self.assertEqual(
            payload["sha256"],
            "2CD6F423E9053A83E65D093FFB33BDAB53AB42FB2A0ABAE334BF51D364E62E38",
        )
        self.assertEqual(
            hashlib.sha256(self.bundle.payload).hexdigest().upper(),
            payload["sha256"],
        )
        self.assertTrue(
            report["taxonomy"]
            ["all_selected_clauses_equal_exact_python_reconstruction_of_branchSource"]
        )
        self.assertTrue(
            report["lean_consumer_contract"]["core_index_reference"]
            ["exactly_matches_mapping"]
        )
        self.assertTrue(
            report["lean_consumer_contract"]["witness_table_reference"]
            ["exactly_matches_generated_payload_and_chunks"]
        )

    def test_payload_is_directly_consumable_as_the_pure_lean_table(self) -> None:
        report = self.bundle.manifest
        spec = generator.select_leaf("FgraveGOW")
        lean = generator.lean_table_source(
            self.bundle.payload, spec, report["taxonomy"]["family_counts"]
        )
        source = lean.decode("utf-8")
        chunks = generator.witnesses.extract_lean_string_array(
            source, "witnessChunks"
        )
        self.assertEqual("".join(chunks).encode("ascii"), self.bundle.payload)
        self.assertEqual(
            hashlib.sha256(lean).hexdigest().upper(),
            report["lean_consumer_contract"]["rendered_pure_data_module_sha256"],
        )

    def test_cli_fgravegow_keeps_only_its_frozen_defaults(self) -> None:
        args = generator.parse_cli([])
        self.assertEqual(args.leaf, "FgraveGOW")
        self.assertEqual(args.core_directory, generator.FGRAVEGOW_CORE_DIRECTORY)
        self.assertEqual(args.payload, generator.PAYLOAD_PATH)
        self.assertEqual(args.manifest, generator.MANIFEST_PATH)
        self.assertFalse(args.without_lean_references)

    def test_cli_other_leaf_rejects_every_implicit_fgravegow_path(self) -> None:
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr), self.assertRaises(SystemExit) as raised:
            generator.parse_cli(
                ["audit", "--leaf", "FoDPO", "--without-lean-references"]
            )
        self.assertEqual(raised.exception.code, 2)
        message = stderr.getvalue()
        self.assertIn("--core-directory", message)
        self.assertIn("--payload", message)
        self.assertIn("--manifest", message)

    def test_cli_other_leaf_requires_explicit_absence_of_lean_references(self) -> None:
        explicit = [
            "audit",
            "--leaf", "FoDPO",
            "--core-directory", "future-core",
            "--payload", "future-payload.bin",
            "--manifest", "future-manifest.json",
        ]
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr), self.assertRaises(SystemExit) as raised:
            generator.parse_cli(explicit)
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("--without-lean-references", stderr.getvalue())

        args = generator.parse_cli(explicit + ["--without-lean-references"])
        self.assertEqual(args.core_directory, Path("future-core"))
        self.assertEqual(args.payload, Path("future-payload.bin"))
        self.assertEqual(args.manifest, Path("future-manifest.json"))
        self.assertTrue(args.without_lean_references)

    def test_tracked_payload_and_manifest_match_deterministic_rebuild(self) -> None:
        result = generator.verify_artifacts(self.bundle)
        self.assertEqual(
            result["status"],
            "PASS_TRACKED_D7_R34_CORE_SEMANTIC_ARTIFACTS_EXACT",
        )

    @staticmethod
    def _copy_core(directory: Path) -> None:
        spec = generator.select_leaf("FgraveGOW")
        base = spec.target_name.removesuffix(".cnf")
        for name in (f"{base}_core.cnf", "core_clause_map.tsv"):
            shutil.copyfile(generator.FGRAVEGOW_CORE_DIRECTORY / name, directory / name)

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
                generator.build_bundle(directory)

    def test_source_index_mutant_is_rejected_by_branch_source_reconstruction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            self._copy_core(directory)
            mapping = directory / "core_clause_map.tsv"
            lines = mapping.read_text(encoding="ascii").splitlines()
            first = lines[1].split("\t")
            self.assertEqual(first[1], "61")
            first[1] = "62"
            lines[1] = "\t".join(first)
            mapping.write_text("\n".join(lines) + "\n", encoding="ascii", newline="")
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "branchSource clause mismatch",
            ):
                generator.build_bundle(directory)

    def test_clause_polarity_mutant_with_updated_row_hash_is_still_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            self._copy_core(directory)
            spec = generator.select_leaf("FgraveGOW")
            base = spec.target_name.removesuffix(".cnf")
            cnf = directory / f"{base}_core.cnf"
            rows = cnf.read_bytes().splitlines(keepends=True)
            literals = tuple(map(int, rows[1].split()))
            self.assertEqual(literals[-1], 0)
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
                generator.build_bundle(directory)

    def test_cube_payload_order_mutant_is_rejected_before_clause_generation(self) -> None:
        original = generator.source.D7_NEW_CUBE_PAYLOAD.read_bytes()
        mutant = original[7:14] + original[:7] + original[14:]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "mutated.bin"
            path.write_bytes(mutant)
            with self.assertRaisesRegex(
                generator.D7CoreSemanticPayloadError,
                "SHA-256 changed",
            ):
                generator.load_catalogues(path, generator.MASTER8_INDEXED_SOURCE)


if __name__ == "__main__":
    unittest.main()
