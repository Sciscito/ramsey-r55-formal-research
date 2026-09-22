from __future__ import annotations

import hashlib
import os
import tempfile
import unittest
from pathlib import Path

from . import materialize_cover6_d7_r34_fgravegow_leaf as materializer


def identity(name: str, payload: bytes) -> materializer.StreamIdentity:
    return materializer.StreamIdentity(
        name=name,
        header=payload.splitlines(keepends=True)[0],
        bytes=len(payload),
        sha256=hashlib.sha256(payload).hexdigest().upper(),
        lines=payload.count(b"\n"),
    )


class TinyFixture:
    source_name = "tiny_f7.cnf"
    target_name = "tiny_fgravegow.cnf"
    source_header = b"p cnf 3 2\n"
    target_header = b"p cnf 3 4\n"
    body = b"1 -2 0\n-1 3 0\n"
    units = b"1 0\n-2 0\n"
    source_payload = source_header + body
    target_payload = target_header + body + units
    source_identity = identity(source_name, source_payload)
    target_identity = identity(target_name, target_payload)


class FgraveGowLeafPreflightTests(unittest.TestCase):
    def test_preflight_freezes_selection_and_both_stream_identities(self) -> None:
        result = materializer.preflight()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["selection"]["record"], "F`GOW")
        self.assertEqual(
            result["selection"]["source_catalogue_index_zero_based"], 5
        )
        self.assertEqual(result["selection"]["incremental_position_one_based"], 6)
        self.assertEqual(result["selection"]["cube"], list(materializer.EXPECTED_CUBE))
        self.assertEqual(result["source"]["clauses"], 4_312_419)
        self.assertEqual(result["source"]["bytes"], 246_507_515)
        self.assertEqual(
            result["source"]["sha256"],
            "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C",
        )
        self.assertEqual(result["target"]["variables"], 66)
        self.assertEqual(result["target"]["clauses"], 4_312_440)
        self.assertEqual(result["target"]["bytes"], 246_507_635)
        self.assertEqual(result["target"]["lines"], 4_312_441)
        self.assertEqual(
            result["target"]["sha256"],
            "78D066E03B1F55FACBF8839BCC409E0D45BABF93FA6D266628BB526D2F5E5971",
        )

    def test_unit_payload_is_exact_and_frozen(self) -> None:
        payload = materializer.unit_payload()
        self.assertEqual(payload.count(b"\n"), 21)
        self.assertEqual(len(payload), 120)
        self.assertEqual(
            materializer.sha256_bytes(payload),
            "4C2D8603575965D0CB08E3CDC7AC7AD463CA369D4EDDB645E565599A0F13373F",
        )
        self.assertEqual(
            payload.splitlines(),
            [f"{literal} 0".encode("ascii") for literal in materializer.EXPECTED_CUBE],
        )

    def test_duplicate_missing_and_out_of_range_unit_mutants_are_rejected(self) -> None:
        cube = materializer.EXPECTED_CUBE
        with self.assertRaisesRegex(materializer.FgraveGowLeafError, "repeats"):
            materializer.unit_payload(cube[:-1] + (cube[0],))
        with self.assertRaisesRegex(materializer.FgraveGowLeafError, "21 variables"):
            materializer.unit_payload(cube[:-1])
        with self.assertRaisesRegex(materializer.FgraveGowLeafError, "outside 1..66"):
            materializer.unit_line(67)

    def test_public_commands_reject_non_s_paths_before_large_io(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            with self.assertRaisesRegex(
                materializer.FgraveGowLeafError, "absolute S: path"
            ):
                materializer.generate(path)
            with self.assertRaisesRegex(
                materializer.FgraveGowLeafError, "absolute S: path"
            ):
                materializer.verify(path)


class FgraveGowLeafTinyMaterializerTests(unittest.TestCase):
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
            TinyFixture.target_identity,
            TinyFixture.units,
        )

    def test_tiny_output_is_rewritten_header_exact_body_then_units(self) -> None:
        self.write_source()
        result = self.materialize()
        target = self.directory / TinyFixture.target_name
        self.assertEqual(
            result["status"],
            "GENERATED_EXACT_F7_R34_FGRAVEGOW_LEAF_WITHOUT_SOLVER",
        )
        self.assertEqual(target.read_bytes(), TinyFixture.target_payload)
        verified = materializer.verify_checked(
            self.directory,
            TinyFixture.source_identity,
            TinyFixture.target_identity,
            TinyFixture.units,
        )
        self.assertEqual(
            verified["status"], "PASS_EXACT_F7_R34_FGRAVEGOW_LEAF_LAYOUT"
        )
        self.assertTrue(verified["body_reused_byte_for_byte"])
        self.assertTrue(verified["exact_ordered_unit_suffix"])

    def test_mutated_source_is_rejected_before_partial_creation(self) -> None:
        mutant = TinyFixture.source_header + b"3 -2 0\n-1 3 0\n"
        self.assertEqual(len(mutant), len(TinyFixture.source_payload))
        self.write_source(mutant)
        with self.assertRaisesRegex(
            materializer.FgraveGowLeafError, "stream identity mismatch"
        ):
            self.materialize()
        self.assertFalse(
            (
                self.directory
                / f"{TinyFixture.target_name}{materializer.PARTIAL_SUFFIX}"
            ).exists()
        )

    def test_existing_target_and_residual_partial_are_never_overwritten(self) -> None:
        self.write_source()
        target = self.directory / TinyFixture.target_name
        target.write_bytes(b"keep target")
        with self.assertRaisesRegex(FileExistsError, "refusing to overwrite"):
            self.materialize()
        self.assertEqual(target.read_bytes(), b"keep target")
        target.unlink()
        partial = self.directory / (
            TinyFixture.target_name + materializer.PARTIAL_SUFFIX
        )
        partial.write_bytes(b"keep partial")
        with self.assertRaisesRegex(FileExistsError, "refusing residual"):
            self.materialize()
        self.assertEqual(partial.read_bytes(), b"keep partial")

    def test_wrong_expected_target_hash_cleans_runner_owned_partial(self) -> None:
        self.write_source()
        wrong = materializer.StreamIdentity(
            name=TinyFixture.target_name,
            header=TinyFixture.target_header,
            bytes=len(TinyFixture.target_payload),
            sha256="0" * 64,
            lines=TinyFixture.target_payload.count(b"\n"),
        )
        with self.assertRaisesRegex(
            materializer.FgraveGowLeafError, "leaf identity mismatch"
        ):
            materializer.materialize_checked(
                self.directory,
                TinyFixture.source_identity,
                wrong,
                TinyFixture.units,
            )
        self.assertFalse((self.directory / TinyFixture.target_name).exists())
        self.assertFalse(
            (
                self.directory
                / f"{TinyFixture.target_name}{materializer.PARTIAL_SUFFIX}"
            ).exists()
        )

    def test_layout_check_rejects_mutated_unit_suffix(self) -> None:
        self.write_source()
        mutant_units = TinyFixture.units.replace(b"-2 0", b"-3 0")
        mutant_payload = TinyFixture.target_header + TinyFixture.body + mutant_units
        (self.directory / TinyFixture.target_name).write_bytes(mutant_payload)
        mutant_identity = identity(TinyFixture.target_name, mutant_payload)
        with self.assertRaisesRegex(
            materializer.FgraveGowLeafError, "exact ordered 21-unit payload"
        ):
            materializer.verify_checked(
                self.directory,
                TinyFixture.source_identity,
                mutant_identity,
                TinyFixture.units,
            )

    def test_verify_refuses_residual_partial(self) -> None:
        self.write_source()
        (self.directory / TinyFixture.target_name).write_bytes(
            TinyFixture.target_payload
        )
        partial = self.directory / (
            TinyFixture.target_name + materializer.PARTIAL_SUFFIX
        )
        partial.write_bytes(b"forensic residue")
        with self.assertRaisesRegex(FileExistsError, "refusing residual"):
            materializer.verify_checked(
                self.directory,
                TinyFixture.source_identity,
                TinyFixture.target_identity,
                TinyFixture.units,
            )


@unittest.skipUnless(
    os.environ.get("RAMSEY_COVER6_D7_FGRAVEGOW_FULL") == "1",
    "set RAMSEY_COVER6_D7_FGRAVEGOW_FULL=1 for primitive reconstruction",
)
class FgraveGowLeafFullFingerprintTests(unittest.TestCase):
    def test_local_primitives_reproduce_both_frozen_hashes(self) -> None:
        result = materializer.primitive_fingerprint()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["source"]["sha256"], materializer.SOURCE_SHA256)
        self.assertEqual(result["target"]["sha256"], materializer.TARGET_SHA256)


if __name__ == "__main__":
    unittest.main()
