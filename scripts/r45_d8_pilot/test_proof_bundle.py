#!/usr/bin/env python3
"""Lightweight tests for the external LRAT release-bundle tooling."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "proof_bundle.py"
SPEC = importlib.util.spec_from_file_location("tested_proof_bundle", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
bundle = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = bundle
SPEC.loader.exec_module(bundle)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def fixture_data(name: str) -> bytes:
    return (f"c tiny fixture {name}\n1 0\n2 0\n0\n").encode("ascii")


def make_fixture(root: Path) -> tuple[Path, Path, bundle.BundleManifest]:
    proofs = root / "source-proofs"
    proofs.mkdir()
    rows = []
    for name in bundle.EXPECTED_PROOF_NAMES:
        data = fixture_data(name)
        (proofs / name).write_bytes(data)
        rows.append({"name": name, "bytes": len(data), "sha256": sha256(data)})
    manifest_data = {
        "schema_version": 1,
        "status": "TEST_FIXTURE",
        "bundle": {
            "lrat_files": 60,
            "leaf_lrat_files": 59,
            "cover_lrat_files": 1,
            "total_lrat_bytes": sum(row["bytes"] for row in rows),
            "required_relative_directory": bundle.EXPECTED_LINK_RELATIVE,
        },
        "files": rows,
    }
    manifest_path = root / "proof_bundle_manifest.json"
    manifest_path.write_text(
        json.dumps(manifest_data, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest_path, proofs, bundle.load_manifest(manifest_path)


class ProofBundleTests(unittest.TestCase):
    def test_manifest_rejects_traversal_name(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest_path, _proofs, _manifest = make_fixture(root)
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
            data["files"][0]["name"] = "../leaf_1.lrat"
            manifest_path.write_text(json.dumps(data), encoding="utf-8")
            with self.assertRaisesRegex(bundle.BundleError, "unsafe manifest proof name"):
                bundle.load_manifest(manifest_path)

    def test_pack_verify_and_install_round_trip(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            archives = root / "archives"
            packed = bundle.pack_bundle(manifest, proofs, archives)
            self.assertEqual(packed["status"], "PACKED_SOURCE_HASHES_VERIFIED")
            self.assertEqual(packed["format"]["compression_level"], 6)
            self.assertEqual(len(packed["archives"]), 4)
            self.assertTrue((archives / bundle.ARCHIVE_REPORT_NAME).is_file())

            for part in bundle.ARCHIVE_PARTS:
                path = archives / part.filename
                self.assertTrue(path.is_file())
                with zipfile.ZipFile(path) as archive:
                    self.assertEqual(
                        archive.namelist(),
                        [f"proofs/{name}" for name in part.proof_names],
                    )
                    self.assertTrue(
                        all(
                            info.compress_type == zipfile.ZIP_DEFLATED
                            for info in archive.infolist()
                        )
                    )

            verified = bundle.verify_archives(manifest, archives)
            self.assertEqual(verified["status"], "VERIFIED_RELEASE_ARCHIVES")
            self.assertTrue(verified["archive_report_verified"])
            self.assertEqual(verified["proof_files"], 60)

            # A clean clone keeps the small report beside the tracked manifest,
            # while the downloaded ZIPs may live alone on an external drive.
            local_report = archives / bundle.ARCHIVE_REPORT_NAME
            tracked_report = manifest.path.parent / bundle.ARCHIVE_REPORT_NAME
            local_report.replace(tracked_report)
            fallback_verified = bundle.verify_archives(manifest, archives)
            self.assertTrue(fallback_verified["archive_report_verified"])

            cache = root / "external-cache"
            installed = bundle.install_bundle(
                manifest, archives, cache, create_link=False
            )
            self.assertEqual(installed["status"], "INSTALLED_VERIFIED_PROOF_BUNDLE")
            self.assertEqual(installed["installed_files"], 60)
            self.assertEqual(installed["verified_existing_files"], 0)
            self.assertEqual(
                bundle.verify_proof_directory(manifest, cache / "proofs")["status"],
                "VERIFIED_PROOF_DIRECTORY",
            )

            resumed = bundle.install_bundle(
                manifest, archives, cache, create_link=False
            )
            self.assertEqual(resumed["installed_files"], 0)
            self.assertEqual(resumed["verified_existing_files"], 60)

    def test_default_compression_level_is_six_and_requires_an_integer(self) -> None:
        args = bundle.build_parser().parse_args(
            [
                "pack",
                "--manifest",
                "manifest.json",
                "--proofs",
                "proofs",
                "--output",
                "archives",
            ]
        )
        self.assertEqual(args.compression_level, 6)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            with self.assertRaisesRegex(bundle.BundleError, "must be an integer"):
                bundle.pack_bundle(
                    manifest,
                    proofs,
                    root / "archives",
                    compression_level=True,
                )

    def test_archive_report_rejects_forged_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            archives = root / "archives"
            bundle.pack_bundle(manifest, proofs, archives)
            report_path = archives / bundle.ARCHIVE_REPORT_NAME
            canonical = json.loads(report_path.read_text(encoding="utf-8"))

            mutations = [
                ("status", lambda row: row.__setitem__("status", "INCOMPLETE")),
                (
                    "source-name",
                    lambda row: row["source_manifest"].__setitem__(
                        "name", "other-manifest.json"
                    ),
                ),
                (
                    "source-extra-field",
                    lambda row: row["source_manifest"].__setitem__("extra", True),
                ),
                ("proof-files", lambda row: row.__setitem__("proof_files", 59)),
                ("proof-bytes", lambda row: row.__setitem__("proof_bytes", 1)),
                (
                    "format-extra-field",
                    lambda row: row["format"].__setitem__("extra", True),
                ),
                (
                    "container",
                    lambda row: row["format"].__setitem__("container", "ZIP"),
                ),
                (
                    "compression",
                    lambda row: row["format"].__setitem__("compression", "Stored"),
                ),
                (
                    "member-prefix",
                    lambda row: row["format"].__setitem__("member_prefix", "../"),
                ),
                (
                    "timestamp",
                    lambda row: row["format"].__setitem__(
                        "normalized_timestamp", "2026-08-06T00:00:00"
                    ),
                ),
            ]
            for key in canonical["format"]:
                mutations.append(
                    (
                        f"missing-format-{key}",
                        lambda row, key=key: row["format"].pop(key),
                    )
                )
            for invalid_level in (True, 0, 10, "6"):
                mutations.append(
                    (
                        f"compression-level-{invalid_level!r}",
                        lambda row, value=invalid_level: row["format"].__setitem__(
                            "compression_level", value
                        ),
                    )
                )

            for label, mutate in mutations:
                with self.subTest(label=label):
                    forged = json.loads(json.dumps(canonical))
                    mutate(forged)
                    report_path.write_text(
                        json.dumps(forged), encoding="utf-8"
                    )
                    with self.assertRaises(bundle.BundleError):
                        bundle.verify_archives(manifest, archives)

    def test_pack_reservations_refuse_collision_and_clean_placeholders(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            archives = root / "archives"
            archives.mkdir()
            collision = archives / bundle.ARCHIVE_PARTS[2].filename
            collision.write_bytes(b"foreign-output")
            with self.assertRaisesRegex(bundle.BundleError, "refusing to reserve"):
                bundle.pack_bundle(manifest, proofs, archives)
            self.assertEqual(collision.read_bytes(), b"foreign-output")
            for part in (
                bundle.ARCHIVE_PARTS[0],
                bundle.ARCHIVE_PARTS[1],
                bundle.ARCHIVE_PARTS[3],
            ):
                self.assertFalse((archives / part.filename).exists())
            self.assertFalse((archives / bundle.ARCHIVE_REPORT_NAME).exists())
            self.assertEqual(list(archives.glob(".*.partial.*")), [])

    def test_pack_never_clobbers_output_created_after_placeholder_unlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            archives = root / "archives"
            operation_name = "rename" if bundle.os.name == "nt" else "link"
            real_publish_operation = getattr(bundle.os, operation_name)
            injected = False

            def inject_collision(source, destination):
                nonlocal injected
                destination = Path(destination)
                if not injected:
                    self.assertFalse(
                        destination.exists(),
                        "collision hook must run after placeholder unlink",
                    )
                    destination.write_bytes(b"foreign-concurrent-output")
                    injected = True
                return real_publish_operation(source, destination)

            with mock.patch.object(
                bundle.os,
                operation_name,
                side_effect=inject_collision,
            ):
                with self.assertRaisesRegex(
                    bundle.BundleError, "appeared concurrently"
                ):
                    bundle.pack_bundle(manifest, proofs, archives)

            self.assertTrue(injected)
            first = archives / bundle.ARCHIVE_PARTS[0].filename
            self.assertEqual(first.read_bytes(), b"foreign-concurrent-output")
            for part in bundle.ARCHIVE_PARTS[1:]:
                self.assertFalse((archives / part.filename).exists())
            self.assertFalse((archives / bundle.ARCHIVE_REPORT_NAME).exists())
            self.assertEqual(list(archives.glob(".*.partial.*")), [])
    def test_verify_rejects_proof_content_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            (proofs / "leaf_7.lrat").write_bytes(fixture_data("leaf_8.lrat"))
            with self.assertRaisesRegex(bundle.BundleError, "proof SHA-256 mismatch"):
                bundle.verify_proof_directory(manifest, proofs)

    def test_install_rejects_zip_path_traversal_before_writing(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            archives = root / "archives"
            bundle.pack_bundle(manifest, proofs, archives, compression_level=1)

            first = bundle.ARCHIVE_PARTS[0]
            first_path = archives / first.filename
            with zipfile.ZipFile(
                first_path,
                "w",
                compression=zipfile.ZIP_DEFLATED,
                allowZip64=True,
            ) as archive:
                for name in first.proof_names:
                    archive.writestr(f"proofs/{name}", fixture_data(name))
                archive.writestr("../escaped.lrat", b"malicious")
            (archives / bundle.ARCHIVE_REPORT_NAME).unlink()

            cache = root / "cache"
            escaped = root / "escaped.lrat"
            with self.assertRaisesRegex(bundle.BundleError, "unsafe ZIP member path"):
                bundle.install_bundle(
                    manifest, archives, cache, create_link=False
                )
            self.assertFalse(cache.exists())
            self.assertFalse(escaped.exists())

    def test_pack_refuses_repository_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            forbidden = bundle.REPO_ROOT / "scripts" / "r45_d8_pilot" / "zip-output"
            with self.assertRaisesRegex(bundle.BundleError, "inside repository"):
                bundle.pack_bundle(manifest, proofs, forbidden)

    def test_install_link_uses_verified_cache_proof_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, proofs, manifest = make_fixture(root)
            archives = root / "archives"
            bundle.pack_bundle(manifest, proofs, archives, compression_level=1)
            cache = root / "cache"
            expected_link = {"status": "MOCK_LINK", "kind": "junction"}
            with mock.patch.object(
                bundle,
                "link_repository_proofs",
                return_value=expected_link,
            ) as create_link:
                result = bundle.install_bundle(
                    manifest, archives, cache, create_link=True
                )
            create_link.assert_called_once_with(manifest, (cache / "proofs").resolve())
            self.assertEqual(result["repository_link"], expected_link)

    def test_link_never_replaces_an_existing_repository_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _manifest_path, _proofs, manifest = make_fixture(root)
            fake_repo = root / "repo"
            link = fake_repo.joinpath(*Path(bundle.EXPECTED_LINK_RELATIVE).parts)
            link.mkdir(parents=True)
            target = root / "target-proofs"
            target.mkdir()
            with mock.patch.object(bundle, "REPO_ROOT", fake_repo):
                with self.assertRaisesRegex(bundle.BundleError, "refusing to replace"):
                    bundle.link_repository_proofs(manifest, target)


if __name__ == "__main__":
    unittest.main()
