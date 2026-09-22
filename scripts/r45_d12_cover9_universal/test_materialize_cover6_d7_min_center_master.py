from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from . import materialize_cover6_d7_min_center_master as materializer


def identity(name: str, payload: bytes) -> materializer.FormulaIdentity:
    return materializer.FormulaIdentity(
        name=name,
        header=payload.splitlines(keepends=True)[0],
        bytes=len(payload),
        sha256=hashlib.sha256(payload).hexdigest().upper(),
        lines=payload.count(b"\n"),
    )


class TinyFixture:
    source_name = "tiny_f7.cnf"
    master_name = "tiny_master7.cnf"
    source_header = b"p cnf 3 2\n"
    master_header = b"p cnf 3 3\n"
    body = b"1 -2 0\n-1 3 0\n"
    extras = b"2 0\n"
    source_payload = source_header + body
    master_payload = master_header + body + extras
    source_identity = identity(source_name, source_payload)
    master_identity = identity(master_name, master_payload)


class Master7MaterializerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_source(self, payload: bytes = TinyFixture.source_payload) -> Path:
        path = self.directory / TinyFixture.source_name
        path.write_bytes(payload)
        return path

    def materialize(self) -> dict[str, object]:
        return materializer.materialize_checked(
            self.directory,
            TinyFixture.source_identity,
            TinyFixture.master_identity,
            TinyFixture.extras,
        )

    def test_preflight_freezes_exact_real_identities_and_suffix(self) -> None:
        result = materializer.preflight()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["source"]["bytes"], 246_507_515)
        self.assertEqual(
            result["source"]["sha256"],
            "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C",
        )
        self.assertEqual(result["master"]["bytes"], 246_507_588)
        self.assertEqual(
            result["master"]["sha256"],
            "DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE",
        )
        self.assertEqual(result["extra_bytes"], 73)
        self.assertEqual(len(result["extra_clauses"]), 9)

    def test_tiny_output_is_exact_header_body_and_suffix(self) -> None:
        self.write_source()
        result = self.materialize()
        target = self.directory / TinyFixture.master_name
        self.assertEqual(result["status"], "GENERATED_EXACT_MASTER7_WITHOUT_SOLVER")
        self.assertEqual(target.read_bytes(), TinyFixture.master_payload)
        self.assertFalse(
            (self.directory / f"{TinyFixture.master_name}{materializer.PARTIAL_SUFFIX}").exists()
        )
        verified = materializer.verify_checked(
            self.directory,
            TinyFixture.source_identity,
            TinyFixture.master_identity,
            TinyFixture.extras,
        )
        self.assertEqual(verified["status"], "PASS_EXACT_MASTER7_LAYOUT")
        self.assertTrue(verified["body_reused_byte_for_byte"])
        self.assertTrue(verified["exact_nine_clause_suffix"])

    def test_mutated_source_body_is_rejected_before_partial_creation(self) -> None:
        mutant = TinyFixture.source_header + b"3 -2 0\n-1 3 0\n"
        self.assertEqual(len(mutant), len(TinyFixture.source_payload))
        self.write_source(mutant)
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "formula identity mismatch"
        ):
            self.materialize()
        self.assertFalse(
            (self.directory / f"{TinyFixture.master_name}{materializer.PARTIAL_SUFFIX}").exists()
        )

    def test_mutated_source_header_is_rejected(self) -> None:
        mutant = b"p cnf 3 9\n" + TinyFixture.body
        self.write_source(mutant)
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "DIMACS header mismatch"
        ):
            self.materialize()

    def test_mutated_expected_hash_is_rejected(self) -> None:
        source = self.write_source()
        wrong = materializer.FormulaIdentity(
            name=TinyFixture.source_name,
            header=TinyFixture.source_header,
            bytes=len(TinyFixture.source_payload),
            sha256="0" * 64,
            lines=TinyFixture.source_payload.count(b"\n"),
        )
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "formula identity mismatch"
        ):
            materializer.inspect_formula(source, wrong)

    def test_mutated_source_name_is_rejected(self) -> None:
        source = self.write_source()
        wrong = materializer.FormulaIdentity(
            name="not_the_producer_name.cnf",
            header=TinyFixture.source_header,
            bytes=len(TinyFixture.source_payload),
            sha256=TinyFixture.source_identity.sha256,
            lines=TinyFixture.source_payload.count(b"\n"),
        )
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "formula name mismatch"
        ):
            materializer.inspect_formula(source, wrong)

    def test_existing_target_is_never_overwritten(self) -> None:
        self.write_source()
        target = self.directory / TinyFixture.master_name
        target.write_bytes(b"keep me")
        with self.assertRaisesRegex(FileExistsError, "refusing to overwrite"):
            self.materialize()
        self.assertEqual(target.read_bytes(), b"keep me")

    def test_residual_partial_is_never_overwritten(self) -> None:
        self.write_source()
        partial = self.directory / (
            TinyFixture.master_name + materializer.PARTIAL_SUFFIX
        )
        partial.write_bytes(b"forensic residue")
        with self.assertRaisesRegex(FileExistsError, "refusing residual"):
            self.materialize()
        self.assertEqual(partial.read_bytes(), b"forensic residue")
        self.assertFalse((self.directory / TinyFixture.master_name).exists())

    def test_verify_refuses_residual_partial(self) -> None:
        self.write_source()
        (self.directory / TinyFixture.master_name).write_bytes(
            TinyFixture.master_payload
        )
        partial = self.directory / (
            TinyFixture.master_name + materializer.PARTIAL_SUFFIX
        )
        partial.write_bytes(b"forensic residue")
        with self.assertRaisesRegex(FileExistsError, "refusing residual"):
            materializer.verify_checked(
                self.directory,
                TinyFixture.source_identity,
                TinyFixture.master_identity,
                TinyFixture.extras,
            )

    def test_verify_rejects_output_body_mutant(self) -> None:
        self.write_source()
        target = self.directory / TinyFixture.master_name
        target.write_bytes(TinyFixture.master_header + b"1 2 0\n-1 3 0\n" + TinyFixture.extras)
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "formula identity mismatch"
        ):
            materializer.verify_checked(
                self.directory,
                TinyFixture.source_identity,
                TinyFixture.master_identity,
                TinyFixture.extras,
            )

    def test_public_generate_and_verify_reject_non_s_paths_first(self) -> None:
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "absolute S: path"
        ):
            materializer.generate(self.directory)
        with self.assertRaisesRegex(
            materializer.Master7MaterializationError, "absolute S: path"
        ):
            materializer.verify(self.directory)


if __name__ == "__main__":
    unittest.main()
