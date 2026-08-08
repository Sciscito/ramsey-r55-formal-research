from __future__ import annotations

import dataclasses
import hashlib
import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from . import cover6_d7_r34_leaf_registry as registry
from . import cover6_d7_r34_safety as safety
from . import materialize_cover6_d7_r34_fgravegow_leaf as frozen_leaf
from . import materialize_cover6_d7_r34_leaf as subject


HERE = Path(__file__).resolve().parent
FROZEN_FILE_IDENTITIES = {
    "materialize_cover6_d7_r34_fgravegow_leaf.py": (
        20_035,
        "D88539604ED56B19C2A8E0E10C2BF72F3DD94C103D3CAFFE312914E570AF01A6",
    ),
    "run_cover6_d7_r34_fgravegow_lrat.py": (
        38_049,
        "E8F6D112EF6D718E57F750D3ADEDEF571A157DBCFC76CEC1DD971549B4B0A519",
    ),
    "reduce_cover6_d7_r34_fgravegow_lrat_core.py": (
        79_015,
        "641B1ECCB9A0E02B16F699FB23BD694292E6A4D04B8592B5E232F33C3928F031",
    ),
}


def identity(payload: bytes, name: str) -> subject.StreamIdentity:
    return subject.StreamIdentity(
        name,
        payload.splitlines(keepends=True)[0],
        len(payload),
        hashlib.sha256(payload).hexdigest().upper(),
        payload.count(b"\n"),
    )


class RegistryTests(unittest.TestCase):
    def test_exact_inventory_and_first_leaf(self) -> None:
        audit = registry.audit_registry()
        self.assertEqual(audit["status"], "PASS_FROZEN_R34_LEAF_REGISTRY_NO_S_NO_SOLVER")
        self.assertEqual(len(registry.ACTIONABLE_LEAVES), 7)
        self.assertEqual(
            registry.ACTIONABLE_SLUGS,
            ("FCUj_", "FKgraveXo", "F_GZ_", "FgraveAZO", "FoDPO", "FoDPW", "FqOxo"),
        )
        self.assertEqual(registry.FIRST_LEAF_SLUG, "FoDPO")
        self.assertIn("3,474-conflict", registry.FIRST_LEAF_RATIONALE)
        self.assertEqual(registry.select_actionable("FoDPO").pilot_conflicts, 3_474)

    def test_excluded_sentinels_fail_closed(self) -> None:
        for slug in ("FGgraveXo", "FgraveGOW", "unknown"):
            with self.subTest(slug=slug):
                with self.assertRaises(registry.R34LeafRegistryError):
                    registry.select_actionable(slug)

    def test_cube_mutants_fail_payload_validation(self) -> None:
        spec = registry.select_actionable("FoDPO")
        repeated = dataclasses.replace(spec, cube=(spec.cube[0],) + spec.cube[1:-1] + (spec.cube[0],))
        with self.assertRaises(subject.R34LeafMaterializerError):
            subject.unit_payload(repeated)
        flipped = dataclasses.replace(spec, cube=(-spec.cube[0],) + spec.cube[1:])
        with self.assertRaises(subject.R34LeafMaterializerError):
            subject.unit_payload(flipped)

    def test_fgravegow_path_is_still_byte_exact(self) -> None:
        for name, (expected_bytes, expected_hash) in FROZEN_FILE_IDENTITIES.items():
            payload = (HERE / name).read_bytes()
            self.assertEqual((len(payload), hashlib.sha256(payload).hexdigest().upper()), (expected_bytes, expected_hash))
        frozen = registry.LEAF_BY_SLUG["FgraveGOW"]
        self.assertEqual(frozen.target_sha256, frozen_leaf.TARGET_SHA256)
        self.assertEqual(frozen.target_bytes, frozen_leaf.TARGET_BYTES)
        self.assertEqual(frozen.cube, frozen_leaf.EXPECTED_CUBE)


class MaterializerTests(unittest.TestCase):
    SOURCE = b"p cnf 3 2\n1 0\n-2 3 0\n"
    UNITS = b"-3 0\n"
    TARGET = b"p cnf 3 3\n1 0\n-2 3 0\n-3 0\n"

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.source_id = identity(self.SOURCE, "toy.cnf")
        self.target_id = identity(self.TARGET, "toy_leaf.cnf")
        (self.directory / self.source_id.name).write_bytes(self.SOURCE)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_small_stream_generate_verify_and_no_overwrite(self) -> None:
        generated = subject.materialize_checked(
            self.directory, self.source_id, self.target_id, self.UNITS
        )
        self.assertEqual(generated["target"]["sha256"], self.target_id.sha256)
        self.assertEqual((self.directory / self.target_id.name).read_bytes(), self.TARGET)
        verified = subject.verify_checked(
            self.directory, self.source_id, self.target_id, self.UNITS
        )
        self.assertEqual(verified["status"], "PASS_EXACT_PARAMETERIZED_R34_LEAF_LAYOUT")
        with self.assertRaises(FileExistsError):
            subject.materialize_checked(
                self.directory, self.source_id, self.target_id, self.UNITS
            )

    def test_bad_expected_hash_quarantines_created_random_partial(self) -> None:
        mutant = dataclasses.replace(self.target_id, sha256="0" * 64)
        with self.assertRaises(subject.R34LeafMaterializerError):
            subject.materialize_checked(
                self.directory, self.source_id, mutant, self.UNITS
            )
        partials = list(self.directory.glob(f"{mutant.name}.partial.*"))
        self.assertEqual(len(partials), 1)
        self.assertEqual(partials[0].read_bytes(), self.TARGET)
        self.assertFalse((self.directory / mutant.name).exists())
        self.assertTrue((self.directory / self.source_id.name).exists())

    @unittest.skipUnless(os.name == "nt", "Windows file locks are required")
    def test_partial_replacement_is_denied_during_validation(self) -> None:
        original_compare = subject.compare_exact_layout
        replacement_attempted = False
        replacement_denied = False

        def substitute_partial(*args: object, **kwargs: object) -> None:
            nonlocal replacement_attempted, replacement_denied
            original_compare(*args, **kwargs)  # type: ignore[arg-type]
            target = args[1]
            assert isinstance(target, Path)
            if f"{subject.PARTIAL_SUFFIX}." in target.name:
                replacement_attempted = True
                try:
                    target.unlink()
                except PermissionError:
                    replacement_denied = True

        with mock.patch.object(
            subject, "compare_exact_layout", side_effect=substitute_partial
        ):
            subject.materialize_checked(
                self.directory, self.source_id, self.target_id, self.UNITS
            )
        self.assertTrue(replacement_attempted)
        self.assertTrue(replacement_denied)
        self.assertEqual(
            (self.directory / self.target_id.name).read_bytes(), self.TARGET
        )

    @unittest.skipUnless(os.name == "nt", "Windows file locks are required")
    def test_windows_partial_lock_closes_before_atomic_rename(self) -> None:
        source = self.directory / self.source_id.name
        partial = self.directory / "rename.partial"
        target = self.directory / "rename.final"
        partial.write_bytes(b"exact")
        with safety.WindowsReadLocks([partial]):
            with self.assertRaises(PermissionError):
                os.rename(partial, target)
        # The distinct source can remain immutable while the now-unlocked
        # partial is renamed.
        with safety.WindowsReadLocks([source]):
            os.rename(partial, target)
        self.assertEqual(target.read_bytes(), b"exact")

    @unittest.skipUnless(os.name == "nt", "Windows directory guards are required")
    def test_windows_parent_guard_must_close_before_child_rename(self) -> None:
        partial = self.directory / "guarded.partial"
        target = self.directory / "guarded.final"
        partial.write_bytes(b"exact")
        with safety.WindowsDirectoryGuard(self.directory):
            with self.assertRaises(PermissionError):
                os.rename(partial, target)
        os.rename(partial, target)
        self.assertEqual(target.read_bytes(), b"exact")
        generate_source = Path(subject.__file__).read_text(encoding="utf-8")
        generate_body = generate_source.split("def generate(", 1)[1].split(
            "\ndef verify(", 1
        )[0]
        self.assertNotIn("WindowsDirectoryGuard(directory)", generate_body)

    def test_final_mutant_after_rename_is_detected_and_preserved(self) -> None:
        real_rename = os.rename

        def rename_then_mutate(source: object, target: object) -> None:
            real_rename(source, target)
            Path(target).write_bytes(b"mutant after publication")

        with mock.patch.object(subject.os, "rename", side_effect=rename_then_mutate):
            with self.assertRaises(subject.R34LeafMaterializerError):
                subject.materialize_checked(
                    self.directory, self.source_id, self.target_id, self.UNITS
                )
        target = self.directory / self.target_id.name
        self.assertEqual(target.read_bytes(), b"mutant after publication")
        self.assertFalse(
            any(
                self.directory.glob(
                    f"{self.target_id.name}{subject.PARTIAL_SUFFIX}.*"
                )
            )
        )

    @unittest.skipUnless(os.name == "nt", "Windows file locks are required")
    def test_published_target_is_write_locked_during_final_rehash(self) -> None:
        original_inspect = subject.inspect_stream
        mutation_attempted = False
        mutation_denied = False

        def probe(path: Path, *args: object, **kwargs: object) -> dict[str, int | str]:
            nonlocal mutation_attempted, mutation_denied
            if path.name == self.target_id.name and not mutation_attempted:
                mutation_attempted = True
                try:
                    path.write_bytes(b"mutant")
                except PermissionError:
                    mutation_denied = True
            return original_inspect(path, *args, **kwargs)  # type: ignore[arg-type]

        with mock.patch.object(subject, "inspect_stream", side_effect=probe):
            subject.materialize_checked(
                self.directory, self.source_id, self.target_id, self.UNITS
            )
        self.assertTrue(mutation_attempted)
        self.assertTrue(mutation_denied)
        self.assertEqual((self.directory / self.target_id.name).read_bytes(), self.TARGET)

    def test_old_residual_partial_is_preserved_but_does_not_block_fresh_random_partial(self) -> None:
        partial = self.directory / f"{self.target_id.name}.partial"
        partial.write_bytes(b"owned-by-someone-else")
        subject.materialize_checked(
            self.directory, self.source_id, self.target_id, self.UNITS
        )
        self.assertEqual(partial.read_bytes(), b"owned-by-someone-else")
        self.assertEqual((self.directory / self.target_id.name).read_bytes(), self.TARGET)

    def test_mutated_body_and_suffix_are_rejected(self) -> None:
        (self.directory / self.target_id.name).write_bytes(self.TARGET.replace(b"1 0\n", b"-1 0\n"))
        with self.assertRaises(subject.R34LeafMaterializerError):
            subject.verify_checked(
                self.directory, self.source_id, self.target_id, self.UNITS
            )

    def test_path_policy(self) -> None:
        for path in (
            Path("relative"),
            Path(r"C:\not-s"),
            Path(r"\\server\share"),
            Path(r"S:\safe\..\escape"),
        ):
            with self.subTest(path=path):
                with self.assertRaises(subject.R34LeafMaterializerError):
                    subject.require_ssd_directory(path)
        self.assertEqual(str(subject.require_ssd_directory(Path(r"S:\exact"))), r"S:\exact")

    def test_reparse_mutant_is_rejected_without_touching_s(self) -> None:
        mutant_status = SimpleNamespace(st_file_attributes=0x00000400, st_mode=0)
        with mock.patch.object(safety.os, "lstat", return_value=mutant_status):
            with self.assertRaises(safety.R34PathSafetyError):
                safety.reject_absolute_s_reparse(Path(r"S:\guarded\formula.cnf"), "mutant")

    @unittest.skipUnless(os.name == "nt", "Windows handle identity is required")
    def test_exclusive_creator_identity_matches_live_regular_file(self) -> None:
        path = self.directory / "exclusive.bin"
        with safety.create_new_exclusive_binary(path) as (stream, identity):
            stream.write(b"exact")
            self.assertEqual(safety.regular_file_stream_identity(stream, path), identity)
        self.assertEqual(safety.regular_file_object_identity(path), identity)

    @unittest.skipUnless(os.name == "nt", "Windows handle identity is required")
    def test_read_lock_rejects_handle_to_name_identity_mismatch(self) -> None:
        path = self.directory / "locked.bin"
        path.write_bytes(b"exact")
        with mock.patch.object(
            safety, "regular_file_object_identity", return_value=(-1, -1)
        ):
            with self.assertRaisesRegex(
                safety.R34PathSafetyError, "does not match live file name"
            ):
                with safety.WindowsReadLocks([path]):
                    self.fail("identity mutant must not enter the lock context")

    @unittest.skipUnless(os.name == "nt", "Windows handle identity is required")
    def test_read_lock_closes_current_handle_when_handle_validation_raises(self) -> None:
        path = self.directory / "invalid-handle.bin"
        path.write_bytes(b"exact")
        locks = safety.WindowsReadLocks([path])
        with mock.patch.object(
            safety,
            "_regular_identity_from_handle",
            side_effect=safety.R34PathSafetyError("handle mutant"),
        ):
            with self.assertRaisesRegex(safety.R34PathSafetyError, "handle mutant"):
                locks.__enter__()
        self.assertEqual(locks.handles, [])

    def test_all_streamed_fingerprints_in_one_local_pass(self) -> None:
        result = subject.primitive_fingerprints()
        self.assertEqual(
            result["status"],
            "PASS_LOCAL_STREAMED_PRIMITIVE_FINGERPRINTS_NO_S_NO_SOLVER",
        )
        self.assertTrue(result["single_f7_reconstruction_pass"])
        self.assertEqual([row["slug"] for row in result["targets"]], list(registry.ACTIONABLE_SLUGS))


if __name__ == "__main__":
    unittest.main()
