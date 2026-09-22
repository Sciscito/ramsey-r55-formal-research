from __future__ import annotations

import hashlib
import os
import tempfile
import unittest
from pathlib import Path

from . import materialize_cover6_d7_r34_catalogue_icnf as materializer


def identity(
    name: str,
    payload: bytes,
) -> materializer.StreamIdentity:
    return materializer.StreamIdentity(
        name=name,
        header=payload.splitlines(keepends=True)[0],
        bytes=len(payload),
        sha256=hashlib.sha256(payload).hexdigest().upper(),
        lines=payload.count(b"\n"),
    )


class TinyFixture:
    source_name = "tiny_f7.cnf"
    target_name = "tiny_r34.inccnf"
    source_header = b"p cnf 3 2\n"
    target_header = b"p inccnf\n"
    body = b"1 -2 0\n-1 3 0\n"
    cubes = b"a 1 -2 0\na -1 2 0\n"
    source_payload = source_header + body
    target_payload = target_header + body + cubes
    source_identity = identity(source_name, source_payload)
    target_identity = identity(target_name, target_payload)


class R34CatalogueIcnfPreflightTests(unittest.TestCase):
    def test_preflight_freezes_the_exact_single_stream(self) -> None:
        result = materializer.preflight()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["source"]["clauses"], 4_312_419)
        self.assertEqual(result["source"]["bytes"], 246_507_515)
        self.assertEqual(
            result["source"]["sha256"],
            "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C",
        )
        self.assertEqual(result["target"]["bytes"], 246_508_227)
        self.assertEqual(result["target"]["lines"], 4_312_429)
        self.assertEqual(
            result["target"]["sha256"],
            "CD4C3BB7D0850F75028346B6CD1AA4493D9FD837BFC595503D3E5DA750703180",
        )
        self.assertEqual(result["target"]["header"], "p inccnf")

    def test_catalogue_is_nine_complete_assignments_with_oracle_first(self) -> None:
        result = materializer.audit_catalogue()
        self.assertEqual(len(result["records"]), 9)
        self.assertEqual(result["records"][0], materializer.ORACLE_RECORD)
        self.assertEqual(result["oracle"]["position_one_based"], 1)
        self.assertTrue(result["oracle"]["exact_cover6_record"])
        self.assertEqual(len(result["cubes"]), 9)
        self.assertEqual(len(set(map(tuple, result["cubes"]))), 9)
        self.assertTrue(all(len(cube) == 21 for cube in result["cubes"]))
        self.assertTrue(
            all(
                {abs(literal) for literal in cube}
                == set(materializer.H_VARIABLES)
                for cube in result["cubes"]
            )
        )

    def test_cube_payload_and_source_catalogue_are_frozen(self) -> None:
        self.assertEqual(len(materializer.CUBE_PAYLOAD), 720)
        self.assertEqual(
            materializer.sha256_bytes(materializer.CUBE_PAYLOAD),
            "78EC8EE01955937D451617A4F5D1D302E880A09F24A2582338A15C0D1496652C",
        )
        self.assertEqual(materializer.read_r34_records(), materializer.ORDERED_R34_RECORDS)
        self.assertEqual(
            tuple(
                materializer.degree_sequence(materializer.graph6_mask(record))
                for record in materializer.ORDERED_R34_RECORDS
            ),
            materializer.EXPECTED_DEGREE_SEQUENCES,
        )

    def test_bad_graph6_and_malformed_cube_are_rejected(self) -> None:
        with self.assertRaisesRegex(
            materializer.R34CatalogueIcnfError, "order-seven graph6"
        ):
            materializer.graph6_mask("bad")
        cube = materializer.cube_for_record(materializer.ORACLE_RECORD)
        with self.assertRaisesRegex(
            materializer.R34CatalogueIcnfError, "repeats a variable"
        ):
            materializer.cube_line(cube[:-1] + (cube[0],))

    def test_public_commands_reject_non_s_paths_before_large_io(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            with self.assertRaisesRegex(
                materializer.R34CatalogueIcnfError, "absolute S: path"
            ):
                materializer.generate(path)
            with self.assertRaisesRegex(
                materializer.R34CatalogueIcnfError, "absolute S: path"
            ):
                materializer.verify(path)


class R34CatalogueIcnfTinyMaterializerTests(unittest.TestCase):
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
            TinyFixture.cubes,
        )

    def test_tiny_output_is_header_body_and_ordered_cubes(self) -> None:
        self.write_source()
        result = self.materialize()
        target = self.directory / TinyFixture.target_name
        self.assertEqual(
            result["status"],
            "GENERATED_EXACT_F7_R34_CATALOGUE9_ICNF_WITHOUT_SOLVER",
        )
        self.assertEqual(target.read_bytes(), TinyFixture.target_payload)
        verified = materializer.verify_checked(
            self.directory,
            TinyFixture.source_identity,
            TinyFixture.target_identity,
            TinyFixture.cubes,
        )
        self.assertEqual(
            verified["status"], "PASS_EXACT_F7_R34_CATALOGUE9_ICNF_LAYOUT"
        )
        self.assertTrue(verified["body_reused_byte_for_byte"])
        self.assertTrue(verified["exact_ordered_cube_suffix"])

    def test_mutated_source_is_rejected_before_partial_creation(self) -> None:
        mutant = TinyFixture.source_header + b"3 -2 0\n-1 3 0\n"
        self.assertEqual(len(mutant), len(TinyFixture.source_payload))
        self.write_source(mutant)
        with self.assertRaisesRegex(
            materializer.R34CatalogueIcnfError, "stream identity mismatch"
        ):
            self.materialize()
        self.assertFalse(
            (self.directory / f"{TinyFixture.target_name}{materializer.PARTIAL_SUFFIX}").exists()
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

    def test_wrong_expected_target_hash_cleans_partial(self) -> None:
        self.write_source()
        wrong = materializer.StreamIdentity(
            name=TinyFixture.target_name,
            header=TinyFixture.target_header,
            bytes=len(TinyFixture.target_payload),
            sha256="0" * 64,
            lines=TinyFixture.target_payload.count(b"\n"),
        )
        with self.assertRaisesRegex(
            materializer.R34CatalogueIcnfError, "incremental stream identity mismatch"
        ):
            materializer.materialize_checked(
                self.directory,
                TinyFixture.source_identity,
                wrong,
                TinyFixture.cubes,
            )
        self.assertFalse((self.directory / TinyFixture.target_name).exists())
        self.assertFalse(
            (self.directory / f"{TinyFixture.target_name}{materializer.PARTIAL_SUFFIX}").exists()
        )

    def test_layout_check_rejects_a_mutated_cube_suffix(self) -> None:
        self.write_source()
        mutant_cubes = TinyFixture.cubes.replace(b"a -1 2 0", b"a -1 3 0")
        mutant_payload = TinyFixture.target_header + TinyFixture.body + mutant_cubes
        target = self.directory / TinyFixture.target_name
        target.write_bytes(mutant_payload)
        mutant_identity = identity(TinyFixture.target_name, mutant_payload)
        with self.assertRaisesRegex(
            materializer.R34CatalogueIcnfError, "exact ordered R34 cube payload"
        ):
            materializer.verify_checked(
                self.directory,
                TinyFixture.source_identity,
                mutant_identity,
                TinyFixture.cubes,
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
                TinyFixture.cubes,
            )


@unittest.skipUnless(
    os.environ.get("RAMSEY_COVER6_D7_R34_ICNF_FULL") == "1",
    "set RAMSEY_COVER6_D7_R34_ICNF_FULL=1 for local primitive reconstruction",
)
class R34CatalogueIcnfFullFingerprintTests(unittest.TestCase):
    def test_local_primitives_reproduce_both_frozen_hashes(self) -> None:
        result = materializer.primitive_fingerprint()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["source"]["sha256"], materializer.SOURCE_SHA256)
        self.assertEqual(result["target"]["sha256"], materializer.TARGET_SHA256)


if __name__ == "__main__":
    unittest.main()
