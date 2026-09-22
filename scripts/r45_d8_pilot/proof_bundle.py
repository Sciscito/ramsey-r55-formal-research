#!/usr/bin/env python3
"""Pack, verify, and install the external degree-eight LRAT bundle.

All paths which can hold large data are mandatory command-line arguments.  In
particular, this tool has no cache or output default on the system drive.  The
tracked ``proof_bundle_manifest.json`` is the authority for every uncompressed
LRAT name, size, and SHA-256 digest.

The release layout is four independent ZIP64/Deflate archives.  ``install``
extracts members itself instead of using ``extractall`` and accepts only the
exact ``proofs/<manifest name>`` paths, so archive path traversal is impossible.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import uuid
import zipfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import BinaryIO, Sequence


HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
ARCHIVE_REPORT_NAME = "proof_bundle_archives.json"
ARCHIVE_PREFIX = "r45-d8-lrat-v1"
EXPECTED_LINK_RELATIVE = "scripts/r45_d8_pilot/guarded_master/proofs"
COPY_BLOCK_BYTES = 1024 * 1024
SHA256_PATTERN = re.compile(r"[0-9A-Fa-f]{64}")
LEAF_PATTERN = re.compile(r"leaf_([1-9][0-9]*)\.lrat")


class BundleError(RuntimeError):
    """A malformed, incomplete, or unsafe proof bundle."""


@dataclass(frozen=True)
class ProofSpec:
    name: str
    bytes: int
    sha256: str


@dataclass(frozen=True)
class BundleManifest:
    path: Path
    sha256: str
    files: tuple[ProofSpec, ...]
    required_relative_directory: str
    raw: dict

    @property
    def by_name(self) -> dict[str, ProofSpec]:
        return {item.name: item for item in self.files}

    @property
    def total_bytes(self) -> int:
        return sum(item.bytes for item in self.files)


@dataclass(frozen=True)
class ArchivePart:
    filename: str
    proof_names: tuple[str, ...]


@dataclass
class OutputReservation:
    path: Path
    marker: bytes
    device: int
    inode: int
    published: bool = False


def leaf_names(first: int, last: int) -> tuple[str, ...]:
    return tuple(f"leaf_{index}.lrat" for index in range(first, last + 1))


ARCHIVE_PARTS = (
    ArchivePart(
        f"{ARCHIVE_PREFIX}-p01-leaves-01-20.zip",
        leaf_names(1, 20),
    ),
    ArchivePart(
        f"{ARCHIVE_PREFIX}-p02-leaves-21-22.zip",
        leaf_names(21, 22),
    ),
    ArchivePart(
        f"{ARCHIVE_PREFIX}-p03-leaves-23-36.zip",
        leaf_names(23, 36),
    ),
    ArchivePart(
        f"{ARCHIVE_PREFIX}-p04-leaves-37-59-cover.zip",
        leaf_names(37, 59) + ("cover.lrat",),
    ),
)

EXPECTED_PROOF_NAMES = leaf_names(1, 59) + ("cover.lrat",)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(COPY_BLOCK_BYTES), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _write_bytes_fsync(path: Path, data: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())


def _reserve_output(path: Path, run_id: str) -> OutputReservation:
    marker = f"proof-bundle-reservation:{run_id}:{path.name}\n".encode("ascii")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    flags |= getattr(os, "O_BINARY", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError as exc:
        raise BundleError(
            f"refusing to reserve existing package output: {path.name}"
        ) from exc
    metadata = None
    try:
        metadata = os.fstat(descriptor)
        offset = 0
        while offset < len(marker):
            written = os.write(descriptor, marker[offset:])
            if written <= 0:
                raise OSError("short write while reserving package output")
            offset += written
        os.fsync(descriptor)
    except Exception:
        os.close(descriptor)
        if metadata is not None:
            try:
                current = os.stat(path, follow_symlinks=False)
                if (
                    stat.S_ISREG(current.st_mode)
                    and current.st_dev == metadata.st_dev
                    and current.st_ino == metadata.st_ino
                ):
                    path.unlink()
            except OSError:
                pass
        raise
    os.close(descriptor)
    return OutputReservation(path, marker, metadata.st_dev, metadata.st_ino)

def _placeholder_is_owned(reservation: OutputReservation) -> bool:
    try:
        metadata = os.stat(reservation.path, follow_symlinks=False)
        return (
            stat.S_ISREG(metadata.st_mode)
            and metadata.st_dev == reservation.device
            and metadata.st_ino == reservation.inode
            and reservation.path.read_bytes() == reservation.marker
        )
    except OSError:
        return False


def _publish_reserved(source: Path, reservation: OutputReservation) -> None:
    if reservation.published or not _placeholder_is_owned(reservation):
        raise BundleError(
            f"reserved output changed concurrently: {reservation.path.name}"
        )
    reservation.path.unlink()
    try:
        if os.name == "nt":
            # Unlike replace(), Windows rename is no-clobber if another
            # process recreates the destination after our unlink.
            os.rename(source, reservation.path)
        else:
            # POSIX rename overwrites, so claim the name atomically with a
            # hard link and remove the staging name only after success.
            os.link(source, reservation.path)
            source.unlink()
    except FileExistsError as exc:
        raise BundleError(
            f"package output appeared concurrently: {reservation.path.name}"
        ) from exc
    except OSError as exc:
        if os.path.lexists(reservation.path):
            raise BundleError(
                f"package output appeared concurrently: {reservation.path.name}"
            ) from exc
        raise
    reservation.published = True


def _cleanup_owned_placeholder(reservation: OutputReservation) -> None:
    if not reservation.published and _placeholder_is_owned(reservation):
        reservation.path.unlink()


def _is_plain_manifest_name(name: str) -> bool:
    return (
        bool(name)
        and "/" not in name
        and "\\" not in name
        and name not in {".", ".."}
        and Path(name).name == name
    )


def _safe_relative_directory(value: str) -> bool:
    if not value or "\\" in value:
        return False
    path = PurePosixPath(value)
    return (
        not path.is_absolute()
        and all(part not in {"", ".", ".."} for part in path.parts)
        and path.as_posix() == value
    )


def load_manifest(path: Path) -> BundleManifest:
    resolved = path.resolve()
    if not resolved.is_file():
        raise BundleError(f"manifest not found: {resolved}")
    try:
        raw = json.loads(resolved.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise BundleError(f"cannot read manifest {resolved}: {exc}") from exc
    if not isinstance(raw, dict) or raw.get("schema_version") != 1:
        raise BundleError("proof bundle manifest must have schema_version 1")
    rows = raw.get("files")
    if not isinstance(rows, list):
        raise BundleError("proof bundle manifest has no files array")

    files: list[ProofSpec] = []
    for index, row in enumerate(rows, 1):
        if not isinstance(row, dict):
            raise BundleError(f"manifest files[{index}] is not an object")
        name = row.get("name")
        size = row.get("bytes")
        digest = row.get("sha256")
        if not isinstance(name, str) or not _is_plain_manifest_name(name):
            raise BundleError(f"unsafe manifest proof name at row {index}: {name!r}")
        if isinstance(size, bool) or not isinstance(size, int) or size < 0:
            raise BundleError(f"invalid byte size for {name}: {size!r}")
        if not isinstance(digest, str) or SHA256_PATTERN.fullmatch(digest) is None:
            raise BundleError(f"invalid SHA-256 for {name}")
        files.append(ProofSpec(name, size, digest.upper()))

    names = tuple(item.name for item in files)
    if names != EXPECTED_PROOF_NAMES:
        raise BundleError(
            "manifest proof order must be leaf_1.lrat,...,leaf_59.lrat,cover.lrat"
        )
    if len(set(names)) != len(names):
        raise BundleError("manifest contains duplicate proof names")

    bundle = raw.get("bundle")
    if not isinstance(bundle, dict):
        raise BundleError("manifest has no bundle object")
    expected_counts = {
        "lrat_files": 60,
        "leaf_lrat_files": 59,
        "cover_lrat_files": 1,
        "total_lrat_bytes": sum(item.bytes for item in files),
    }
    for key, expected in expected_counts.items():
        if bundle.get(key) != expected:
            raise BundleError(
                f"manifest bundle.{key} is {bundle.get(key)!r}, expected {expected}"
            )
    required = bundle.get("required_relative_directory")
    if not isinstance(required, str) or not _safe_relative_directory(required):
        raise BundleError("manifest required_relative_directory is unsafe")
    if required != EXPECTED_LINK_RELATIVE:
        raise BundleError(
            "manifest required_relative_directory does not name the guarded-master proofs"
        )
    return BundleManifest(
        path=resolved,
        sha256=sha256_file(resolved),
        files=tuple(files),
        required_relative_directory=required,
        raw=raw,
    )


def _ensure_external_output(path: Path, label: str) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(REPO_ROOT.resolve())
    except ValueError:
        return resolved
    raise BundleError(
        f"refusing {label} inside repository {REPO_ROOT}; choose an explicit external path"
    )


def _check_proof_directory_inventory(
    manifest: BundleManifest, proofs: Path, *, check_sizes: bool
) -> Path:
    resolved = proofs.resolve()
    if not resolved.is_dir():
        raise BundleError(f"proof directory not found: {resolved}")
    expected = set(EXPECTED_PROOF_NAMES)
    actual_lrats = {
        child.name
        for child in resolved.iterdir()
        if child.is_file() and child.name.lower().endswith(".lrat")
    }
    missing = sorted(expected - actual_lrats)
    unexpected = sorted(actual_lrats - expected)
    if missing:
        raise BundleError(f"proof directory is missing: {', '.join(missing)}")
    if unexpected:
        raise BundleError(f"proof directory has unexpected LRATs: {', '.join(unexpected)}")
    if check_sizes:
        for item in manifest.files:
            path = resolved / item.name
            if not path.is_file() or path.stat().st_size != item.bytes:
                raise BundleError(f"proof size mismatch: {item.name}")
    return resolved


def _hash_stream(stream: BinaryIO, *, expected_size: int, label: str) -> tuple[int, str]:
    digest = hashlib.sha256()
    total = 0
    while True:
        block = stream.read(COPY_BLOCK_BYTES)
        if not block:
            break
        total += len(block)
        if total > expected_size:
            raise BundleError(f"{label} exceeds its declared size")
        digest.update(block)
    return total, digest.hexdigest().upper()


def _copy_hash_stream(
    source: BinaryIO, destination: BinaryIO, *, expected_size: int, label: str
) -> tuple[int, str]:
    digest = hashlib.sha256()
    total = 0
    while True:
        block = source.read(COPY_BLOCK_BYTES)
        if not block:
            break
        total += len(block)
        if total > expected_size:
            raise BundleError(f"{label} exceeds its declared size")
        digest.update(block)
        destination.write(block)
    return total, digest.hexdigest().upper()


def _assert_content(item: ProofSpec, size: int, digest: str) -> None:
    if size != item.bytes:
        raise BundleError(
            f"proof size mismatch for {item.name}: {size} != {item.bytes}"
        )
    if digest != item.sha256:
        raise BundleError(f"proof SHA-256 mismatch for {item.name}")


def verify_proof_directory(manifest: BundleManifest, proofs: Path) -> dict:
    root = _check_proof_directory_inventory(manifest, proofs, check_sizes=True)
    for item in manifest.files:
        with (root / item.name).open("rb") as stream:
            size, digest = _hash_stream(
                stream, expected_size=item.bytes, label=item.name
            )
        _assert_content(item, size, digest)
    return {
        "schema_version": 1,
        "status": "VERIFIED_PROOF_DIRECTORY",
        "manifest_sha256": manifest.sha256,
        "proof_files": len(manifest.files),
        "proof_bytes": manifest.total_bytes,
    }


def _archive_member_name(proof_name: str) -> str:
    return f"proofs/{proof_name}"


def _validate_member_path(name: str) -> None:
    path = PurePosixPath(name)
    if (
        not name
        or "\\" in name
        or path.is_absolute()
        or any(part in {"", ".", ".."} for part in path.parts)
        or path.as_posix() != name
    ):
        raise BundleError(f"unsafe ZIP member path: {name!r}")


def _validate_archive_inventory(
    archive: Path,
    part: ArchivePart,
    manifest: BundleManifest,
) -> tuple[zipfile.ZipFile, tuple[zipfile.ZipInfo, ...]]:
    try:
        handle = zipfile.ZipFile(archive, "r", allowZip64=True)
    except (OSError, zipfile.BadZipFile) as exc:
        raise BundleError(f"cannot open ZIP {archive.name}: {exc}") from exc
    try:
        infos = tuple(handle.infolist())
        actual_names = tuple(info.filename for info in infos)
        expected_names = tuple(_archive_member_name(name) for name in part.proof_names)
        for name in actual_names:
            _validate_member_path(name)
        if actual_names != expected_names:
            raise BundleError(
                f"ZIP member inventory mismatch in {archive.name}: "
                f"expected {expected_names!r}, got {actual_names!r}"
            )
        by_name = manifest.by_name
        for info, proof_name in zip(infos, part.proof_names, strict=True):
            item = by_name[proof_name]
            mode = (info.external_attr >> 16) & 0xFFFF
            if info.is_dir() or stat.S_ISLNK(mode):
                raise BundleError(f"ZIP member is not a regular file: {info.filename}")
            if info.flag_bits & 0x1:
                raise BundleError(f"encrypted ZIP member rejected: {info.filename}")
            if info.compress_type != zipfile.ZIP_DEFLATED:
                raise BundleError(f"non-Deflate ZIP member rejected: {info.filename}")
            if info.file_size != item.bytes:
                raise BundleError(f"ZIP member size mismatch: {info.filename}")
        return handle, infos
    except Exception:
        handle.close()
        raise


def _archive_report_entry(path: Path, part: ArchivePart) -> dict:
    return {
        "name": part.filename,
        "bytes": path.stat().st_size,
        "sha256": sha256_file(path),
        "members": [_archive_member_name(name) for name in part.proof_names],
    }


def _load_archive_report(
    archive_directory: Path, manifest: BundleManifest
) -> dict | None:
    candidates = (
        archive_directory / ARCHIVE_REPORT_NAME,
        manifest.path.parent / ARCHIVE_REPORT_NAME,
    )
    path = next((candidate for candidate in candidates if candidate.is_file()), None)
    if path is None:
        return None
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise BundleError(f"cannot read archive report {path}: {exc}") from exc
    if not isinstance(report, dict) or report.get("schema_version") != 1:
        raise BundleError("archive report must have schema_version 1")
    if report.get("status") != "PACKED_SOURCE_HASHES_VERIFIED":
        raise BundleError("archive report status is not PACKED_SOURCE_HASHES_VERIFIED")
    source = report.get("source_manifest")
    if (
        not isinstance(source, dict)
        or set(source) != {"name", "sha256"}
        or source.get("name") != manifest.path.name
        or source.get("sha256") != manifest.sha256
    ):
        raise BundleError("archive report is for a different proof manifest")
    if report.get("proof_files") != len(manifest.files):
        raise BundleError("archive report proof_files mismatch")
    if report.get("proof_bytes") != manifest.total_bytes:
        raise BundleError("archive report proof_bytes mismatch")

    format_row = report.get("format")
    format_keys = {
        "container",
        "compression",
        "compression_level",
        "member_prefix",
        "normalized_timestamp",
    }
    if not isinstance(format_row, dict) or set(format_row) != format_keys:
        raise BundleError("archive report format fields mismatch")
    if (
        format_row.get("container") != "ZIP64"
        or format_row.get("compression") != "Deflate"
        or format_row.get("member_prefix") != "proofs/"
        or format_row.get("normalized_timestamp") != "1980-01-01T00:00:00"
    ):
        raise BundleError("archive report format values mismatch")
    compression_level = format_row.get("compression_level")
    if (
        isinstance(compression_level, bool)
        or not isinstance(compression_level, int)
        or compression_level not in range(1, 10)
    ):
        raise BundleError("archive report compression_level must be an integer in 1,...,9")

    rows = report.get("archives")
    if not isinstance(rows, list) or len(rows) != len(ARCHIVE_PARTS):
        raise BundleError("archive report does not list exactly four archives")
    for row, part in zip(rows, ARCHIVE_PARTS, strict=True):
        if not isinstance(row, dict) or row.get("name") != part.filename:
            raise BundleError("archive report order/name mismatch")
        if row.get("members") != [
            _archive_member_name(name) for name in part.proof_names
        ]:
            raise BundleError(f"archive report member mismatch for {part.filename}")
        if (
            isinstance(row.get("bytes"), bool)
            or not isinstance(row.get("bytes"), int)
            or row["bytes"] < 0
            or not isinstance(row.get("sha256"), str)
            or SHA256_PATTERN.fullmatch(row["sha256"]) is None
        ):
            raise BundleError(f"invalid archive report digest/size for {part.filename}")
    return report


def _verify_archive_container(
    path: Path, report_row: dict | None
) -> tuple[int, str]:
    size = path.stat().st_size
    digest = sha256_file(path)
    if report_row is not None:
        if size != report_row["bytes"]:
            raise BundleError(f"archive size mismatch: {path.name}")
        if digest != report_row["sha256"].upper():
            raise BundleError(f"archive SHA-256 mismatch: {path.name}")
    return size, digest


def verify_archives(manifest: BundleManifest, archives: Path) -> dict:
    root = archives.resolve()
    if not root.is_dir():
        raise BundleError(f"archive directory not found: {root}")
    report = _load_archive_report(root, manifest)
    report_rows = report["archives"] if report is not None else [None] * 4
    archive_results: list[dict] = []
    verified_names: list[str] = []
    for part, report_row in zip(ARCHIVE_PARTS, report_rows, strict=True):
        path = root / part.filename
        if not path.is_file():
            raise BundleError(f"missing release archive: {part.filename}")
        archive_size, archive_digest = _verify_archive_container(path, report_row)
        handle, infos = _validate_archive_inventory(path, part, manifest)
        try:
            for info, proof_name in zip(infos, part.proof_names, strict=True):
                item = manifest.by_name[proof_name]
                try:
                    with handle.open(info, "r") as stream:
                        size, digest = _hash_stream(
                            stream,
                            expected_size=item.bytes,
                            label=info.filename,
                        )
                except (OSError, EOFError, zipfile.BadZipFile) as exc:
                    raise BundleError(
                        f"cannot read ZIP member {info.filename}: {exc}"
                    ) from exc
                _assert_content(item, size, digest)
                verified_names.append(proof_name)
        finally:
            handle.close()
        archive_results.append(
            {
                "name": part.filename,
                "bytes": archive_size,
                "sha256": archive_digest,
                "proof_files": len(part.proof_names),
            }
        )
    if tuple(verified_names) != EXPECTED_PROOF_NAMES:
        raise BundleError("four archives do not cover the canonical proof order")
    return {
        "schema_version": 1,
        "status": "VERIFIED_RELEASE_ARCHIVES",
        "manifest_sha256": manifest.sha256,
        "archive_report_verified": report is not None,
        "proof_files": len(manifest.files),
        "proof_bytes": manifest.total_bytes,
        "archives": archive_results,
    }


def _zip_info(name: str) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
    info.compress_type = zipfile.ZIP_DEFLATED
    info.create_system = 3
    info.external_attr = (stat.S_IFREG | 0o644) << 16
    info.extra = b""
    info.comment = b""
    return info


def pack_bundle(
    manifest: BundleManifest,
    proofs: Path,
    output: Path,
    *,
    compression_level: int = 6,
) -> dict:
    if (
        isinstance(compression_level, bool)
        or not isinstance(compression_level, int)
        or compression_level not in range(1, 10)
    ):
        raise BundleError("compression level must be an integer in 1,...,9")
    proof_root = _check_proof_directory_inventory(
        manifest, proofs, check_sizes=True
    )
    output_root = _ensure_external_output(output, "archive output")
    output_root.mkdir(parents=True, exist_ok=True)
    final_paths = [output_root / part.filename for part in ARCHIVE_PARTS]
    report_path = output_root / ARCHIVE_REPORT_NAME

    run_id = uuid.uuid4().hex
    partials = [
        path.with_name(f".{path.name}.partial.{run_id}") for path in final_paths
    ]
    report_partial = report_path.with_name(
        f".{report_path.name}.partial.{run_id}"
    )
    publish_sources = partials + [report_partial]
    publish_paths = final_paths + [report_path]
    reservations: list[OutputReservation] = []
    entries: list[dict] = []
    try:
        # Reserve all public names before the first proof byte is compressed.
        # O_EXCL closes the check/create race between concurrent pack processes.
        for publish_path in publish_paths:
            reservations.append(_reserve_output(publish_path, run_id))

        for part, partial in zip(ARCHIVE_PARTS, partials, strict=True):
            with zipfile.ZipFile(
                partial,
                mode="x",
                compression=zipfile.ZIP_DEFLATED,
                compresslevel=compression_level,
                allowZip64=True,
                strict_timestamps=True,
            ) as archive:
                for proof_name in part.proof_names:
                    item = manifest.by_name[proof_name]
                    source_path = proof_root / proof_name
                    if source_path.stat().st_size != item.bytes:
                        raise BundleError(f"proof size changed before packing: {proof_name}")
                    info = _zip_info(_archive_member_name(proof_name))
                    with source_path.open("rb") as source, archive.open(
                        info, "w", force_zip64=True
                    ) as destination:
                        size, digest = _copy_hash_stream(
                            source,
                            destination,
                            expected_size=item.bytes,
                            label=proof_name,
                        )
                    _assert_content(item, size, digest)

            handle, _infos = _validate_archive_inventory(partial, part, manifest)
            handle.close()
            entries.append(_archive_report_entry(partial, part))

        report = {
            "schema_version": 1,
            "status": "PACKED_SOURCE_HASHES_VERIFIED",
            "source_manifest": {
                "name": manifest.path.name,
                "sha256": manifest.sha256,
            },
            "format": {
                "container": "ZIP64",
                "compression": "Deflate",
                "compression_level": compression_level,
                "member_prefix": "proofs/",
                "normalized_timestamp": "1980-01-01T00:00:00",
            },
            "proof_files": len(manifest.files),
            "proof_bytes": manifest.total_bytes,
            "archives": entries,
        }
        _write_bytes_fsync(report_partial, json_bytes(report))

        for source, reservation in zip(
            publish_sources, reservations, strict=True
        ):
            _publish_reserved(source, reservation)
        return report
    finally:
        for partial in publish_sources:
            if partial.exists():
                partial.unlink()
        for reservation in reservations:
            _cleanup_owned_placeholder(reservation)

def _extract_member_atomic(
    archive: zipfile.ZipFile,
    info: zipfile.ZipInfo,
    item: ProofSpec,
    destination: Path,
) -> str:
    if destination.exists():
        if not destination.is_file() or destination.stat().st_size != item.bytes:
            raise BundleError(f"refusing to replace existing invalid proof: {item.name}")
        with destination.open("rb") as stream:
            size, digest = _hash_stream(
                stream, expected_size=item.bytes, label=item.name
            )
        _assert_content(item, size, digest)
        return "SKIPPED_VERIFIED_EXISTING"

    partial = destination.with_name(
        f".{destination.name}.partial.{uuid.uuid4().hex}"
    )
    try:
        with archive.open(info, "r") as source, partial.open("xb") as output:
            size, digest = _copy_hash_stream(
                source,
                output,
                expected_size=item.bytes,
                label=info.filename,
            )
            output.flush()
            os.fsync(output.fileno())
        _assert_content(item, size, digest)
        if destination.exists():
            raise BundleError(f"proof appeared concurrently: {destination}")
        os.replace(partial, destination)
        return "INSTALLED"
    except (OSError, EOFError, zipfile.BadZipFile) as exc:
        raise BundleError(f"cannot install {item.name}: {exc}") from exc
    finally:
        if partial.exists():
            partial.unlink()


def _powershell_literal(value: str) -> str:
    return "'" + value.replace("'", "''") + "'"


def _create_directory_link(link: Path, target: Path) -> str:
    if os.name != "nt":
        os.symlink(target, link, target_is_directory=True)
        return "SYMLINK_CREATED"
    script = (
        "$ErrorActionPreference = 'Stop'\n"
        f"New-Item -ItemType Junction -Path {_powershell_literal(str(link))} "
        f"-Target {_powershell_literal(str(target))} | Out-Null\n"
    )
    encoded = base64.b64encode(script.encode("utf-16le")).decode("ascii")
    result = subprocess.run(
        [
            "powershell.exe",
            "-NoProfile",
            "-NonInteractive",
            "-EncodedCommand",
            encoded,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise BundleError(f"cannot create Windows junction: {detail}")
    return "JUNCTION_CREATED"


def link_repository_proofs(manifest: BundleManifest, proof_target: Path) -> dict:
    if manifest.required_relative_directory != EXPECTED_LINK_RELATIVE:
        raise BundleError("refusing non-canonical repository link destination")
    target = proof_target.resolve()
    if not target.is_dir():
        raise BundleError(f"proof link target is not a directory: {target}")
    relative = PurePosixPath(manifest.required_relative_directory)
    link = REPO_ROOT.joinpath(*relative.parts)
    if not link.parent.is_dir():
        raise BundleError(f"repository link parent does not exist: {link.parent}")
    if os.path.lexists(link):
        try:
            same = link.is_dir() and link.resolve(strict=True) == target
        except OSError:
            same = False
        if not same:
            raise BundleError(f"refusing to replace existing repository path: {link}")
        return {
            "status": "ALREADY_LINKED",
            "kind": "junction" if os.name == "nt" else "symlink",
        }
    status = _create_directory_link(link, target)
    if not link.is_dir() or link.resolve(strict=True) != target:
        raise BundleError("created repository proof link does not resolve to cache")
    return {
        "status": status,
        "kind": "junction" if os.name == "nt" else "symlink",
    }


def install_bundle(
    manifest: BundleManifest,
    archives: Path,
    cache: Path,
    *,
    create_link: bool,
) -> dict:
    archive_root = archives.resolve()
    if not archive_root.is_dir():
        raise BundleError(f"archive directory not found: {archive_root}")
    # Validate all inventories before creating the cache or writing a proof.
    report = _load_archive_report(archive_root, manifest)
    report_rows = report["archives"] if report is not None else [None] * 4
    inventories: list[tuple[ArchivePart, Path]] = []
    for part, report_row in zip(ARCHIVE_PARTS, report_rows, strict=True):
        path = archive_root / part.filename
        if not path.is_file():
            raise BundleError(f"missing release archive: {part.filename}")
        _verify_archive_container(path, report_row)
        handle, _infos = _validate_archive_inventory(path, part, manifest)
        handle.close()
        inventories.append((part, path))

    cache_root = _ensure_external_output(cache, "proof cache")
    proof_root = cache_root / "proofs"
    proof_root.mkdir(parents=True, exist_ok=True)
    existing_lrats = {
        child.name
        for child in proof_root.iterdir()
        if child.is_file() and child.name.lower().endswith(".lrat")
    }
    unexpected = sorted(existing_lrats - set(EXPECTED_PROOF_NAMES))
    if unexpected:
        raise BundleError(
            "proof cache has unexpected LRATs: " + ", ".join(unexpected)
        )

    installed = 0
    skipped = 0
    for part, path in inventories:
        handle, infos = _validate_archive_inventory(path, part, manifest)
        try:
            for info, proof_name in zip(infos, part.proof_names, strict=True):
                item = manifest.by_name[proof_name]
                status_text = _extract_member_atomic(
                    handle, info, item, proof_root / proof_name
                )
                if status_text == "INSTALLED":
                    installed += 1
                else:
                    skipped += 1
        finally:
            handle.close()
    _check_proof_directory_inventory(manifest, proof_root, check_sizes=True)
    link_result = (
        link_repository_proofs(manifest, proof_root) if create_link else None
    )
    return {
        "schema_version": 1,
        "status": "INSTALLED_VERIFIED_PROOF_BUNDLE",
        "manifest_sha256": manifest.sha256,
        "proof_files": len(manifest.files),
        "proof_bytes": manifest.total_bytes,
        "installed_files": installed,
        "verified_existing_files": skipped,
        "archive_report_verified": report is not None,
        "repository_link": link_result,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    pack = subparsers.add_parser("pack", help="create the four release ZIPs")
    pack.add_argument("--manifest", required=True, type=Path)
    pack.add_argument("--proofs", required=True, type=Path)
    pack.add_argument("--output", required=True, type=Path)
    pack.add_argument("--compression-level", type=int, default=6)

    verify = subparsers.add_parser("verify", help="verify proofs or release ZIPs")
    verify.add_argument("--manifest", required=True, type=Path)
    source = verify.add_mutually_exclusive_group(required=True)
    source.add_argument("--proofs", type=Path)
    source.add_argument("--archives", type=Path)

    install = subparsers.add_parser(
        "install", help="install ZIP members in an explicit external cache"
    )
    install.add_argument("--manifest", required=True, type=Path)
    install.add_argument("--archives", required=True, type=Path)
    install.add_argument("--cache", required=True, type=Path)
    install.add_argument(
        "--link",
        action="store_true",
        help="create the exact ignored repository junction/symlink after verification",
    )
    return parser


def run(args: argparse.Namespace) -> dict:
    manifest = load_manifest(args.manifest)
    if args.command == "pack":
        return pack_bundle(
            manifest,
            args.proofs,
            args.output,
            compression_level=args.compression_level,
        )
    if args.command == "verify":
        if args.proofs is not None:
            return verify_proof_directory(manifest, args.proofs)
        return verify_archives(manifest, args.archives)
    if args.command == "install":
        return install_bundle(
            manifest,
            args.archives,
            args.cache,
            create_link=args.link,
        )
    raise BundleError(f"unknown command: {args.command}")


def main(argv: Sequence[str] | None = None) -> int:
    try:
        result = run(build_parser().parse_args(argv))
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (BundleError, OSError, zipfile.BadZipFile) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
