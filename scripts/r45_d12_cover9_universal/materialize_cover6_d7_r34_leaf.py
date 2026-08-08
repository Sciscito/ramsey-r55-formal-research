#!/usr/bin/env python3
"""Materialize or verify one of the seven pending R34/F7 leaf formulas.

The default commands are local, solver-free preflights.  ``fingerprint``
reconstructs the exact F7 byte stream from tracked primitives and checks all
selected SHA-256 identities in one pass.  ``generate`` and ``verify`` are the
only commands that may touch a large formula; they require an existing
absolute ``S:`` directory, refuse the final name, and use a fresh random
partial that is quarantined without deletion on failure.  The frozen
``F`GOW`` route is intentionally not selectable here.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import secrets
from contextlib import nullcontext
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, Sequence

from . import audit_cover6_d7_min_center_source as source_audit
from . import cover6_d7_r34_leaf_registry as registry
from . import cover6_d7_r34_safety as safety
from . import materialize_cover6_d7_r34_catalogue_icnf as catalogue


SOURCE_NAME = "cover6_closed_block_degree_d7.cnf"
SOURCE_HEADER = b"p cnf 66 4312419\n"
TARGET_HEADER = registry.TARGET_HEADER
SOURCE_VARIABLES = 66
SOURCE_CLAUSES = 4_312_419
SOURCE_BYTES = 246_507_515
SOURCE_LINES = 4_312_420
SOURCE_SHA256 = "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C"
TARGET_CLAUSES = 4_312_440
TARGET_LINES = 4_312_441
PARTIAL_SUFFIX = ".partial"
COPY_BLOCK_BYTES = 8 * 1024 * 1024


class R34LeafMaterializerError(ValueError):
    """Raised at the first selection, identity, path, or layout mismatch."""


@dataclass(frozen=True)
class StreamIdentity:
    name: str
    header: bytes
    bytes: int
    sha256: str
    lines: int


SOURCE_IDENTITY = StreamIdentity(
    SOURCE_NAME, SOURCE_HEADER, SOURCE_BYTES, SOURCE_SHA256, SOURCE_LINES
)


def target_identity(spec: registry.LeafSpec) -> StreamIdentity:
    return StreamIdentity(
        spec.target_name,
        TARGET_HEADER,
        spec.target_bytes,
        spec.target_sha256,
        TARGET_LINES,
    )


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def unit_payload(spec: registry.LeafSpec) -> bytes:
    payload = registry.unit_payload(spec)
    if len(spec.cube) != registry.UNIT_COUNT:
        raise R34LeafMaterializerError("an R34 leaf must contain exactly 21 units")
    if {abs(literal) for literal in spec.cube} != set(catalogue.H_VARIABLES):
        raise R34LeafMaterializerError("an R34 leaf does not assign the exact K7 block")
    if any(not literal or abs(literal) > SOURCE_VARIABLES for literal in spec.cube):
        raise R34LeafMaterializerError("an R34 leaf contains an invalid unit literal")
    observed = (len(payload), sha256_bytes(payload))
    expected = (spec.unit_payload_bytes, spec.unit_payload_sha256)
    if observed != expected:
        raise R34LeafMaterializerError(
            f"unit payload identity changed for {spec.slug}: {observed} != {expected}"
        )
    return payload


def require_ssd_directory(path: Path) -> Path:
    try:
        return safety.require_absolute_s_no_parent(path, "leaf directory")
    except safety.R34PathSafetyError as error:
        raise R34LeafMaterializerError(str(error)) from error


def _lexists(path: Path) -> bool:
    try:
        os.lstat(path)
    except FileNotFoundError:
        return False
    return True


def inspect_stream(
    path: Path, identity: StreamIdentity, *, enforce_name: bool = True
) -> dict[str, int | str]:
    if enforce_name and path.name != identity.name:
        raise R34LeafMaterializerError(
            f"stream name mismatch: {path.name!r} != {identity.name!r}"
        )
    digest = hashlib.sha256()
    size = 0
    lines = 0
    with path.open("rb", buffering=COPY_BLOCK_BYTES) as stream:
        header = stream.readline()
        if header != identity.header:
            raise R34LeafMaterializerError(
                f"stream header mismatch in {path.name}: {header!r}"
            )
        digest.update(header)
        size += len(header)
        lines += 1
        for block in iter(lambda: stream.read(COPY_BLOCK_BYTES), b""):
            digest.update(block)
            size += len(block)
            lines += block.count(b"\n")
    observed = (size, digest.hexdigest().upper(), lines)
    expected = (identity.bytes, identity.sha256, identity.lines)
    if observed != expected:
        raise R34LeafMaterializerError(
            f"stream identity mismatch for {path.name}: {observed} != {expected}"
        )
    return {"name": path.name, "bytes": size, "sha256": observed[1], "lines": lines}


def _copy_body(
    source: BinaryIO,
    target: BinaryIO,
    source_identity: StreamIdentity,
    selected_identity: StreamIdentity,
    units: bytes,
) -> tuple[dict[str, int | str], dict[str, int | str]]:
    source_digest = hashlib.sha256()
    target_digest = hashlib.sha256()
    header = source.readline()
    if header != source_identity.header:
        raise R34LeafMaterializerError("F7 header changed before streaming copy")
    source_digest.update(header)
    target_digest.update(selected_identity.header)
    source_size = len(header)
    target_size = len(selected_identity.header)
    source_lines = target_lines = 1
    target.write(selected_identity.header)
    for block in iter(lambda: source.read(COPY_BLOCK_BYTES), b""):
        source_digest.update(block)
        target_digest.update(block)
        target.write(block)
        source_size += len(block)
        target_size += len(block)
        count = block.count(b"\n")
        source_lines += count
        target_lines += count
    observed_source = (
        source_size,
        source_digest.hexdigest().upper(),
        source_lines,
    )
    expected_source = (
        source_identity.bytes,
        source_identity.sha256,
        source_identity.lines,
    )
    if observed_source != expected_source:
        raise R34LeafMaterializerError(
            f"F7 changed during materialization: {observed_source} != {expected_source}"
        )
    target.write(units)
    target_digest.update(units)
    target_size += len(units)
    target_lines += units.count(b"\n")
    observed_target = (
        target_size,
        target_digest.hexdigest().upper(),
        target_lines,
    )
    expected_target = (
        selected_identity.bytes,
        selected_identity.sha256,
        selected_identity.lines,
    )
    if observed_target != expected_target:
        raise R34LeafMaterializerError(
            f"leaf stream identity mismatch: {observed_target} != {expected_target}"
        )
    return (
        {"name": source_identity.name, "bytes": source_size,
         "sha256": observed_source[1], "lines": source_lines},
        {"name": selected_identity.name, "bytes": target_size,
         "sha256": observed_target[1], "lines": target_lines},
    )


def compare_exact_layout(
    source: Path,
    target: Path,
    source_identity: StreamIdentity,
    selected_identity: StreamIdentity,
    units: bytes,
) -> None:
    with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
        with target.open("rb", buffering=COPY_BLOCK_BYTES) as target_stream:
            if source_stream.readline() != source_identity.header:
                raise R34LeafMaterializerError("F7 header changed during layout check")
            if target_stream.readline() != selected_identity.header:
                raise R34LeafMaterializerError("leaf header changed during layout check")
            remaining = source_identity.bytes - len(source_identity.header)
            while remaining:
                amount = min(COPY_BLOCK_BYTES, remaining)
                source_block = source_stream.read(amount)
                target_block = target_stream.read(amount)
                if len(source_block) != amount or target_block != source_block:
                    raise R34LeafMaterializerError(
                        "leaf body is not byte-for-byte identical to F7"
                    )
                remaining -= amount
            if source_stream.read(1):
                raise R34LeafMaterializerError("unexpected F7 suffix")
            if target_stream.read() != units:
                raise R34LeafMaterializerError("leaf suffix is not the exact unit payload")


def materialize_checked(
    directory: Path,
    source_identity: StreamIdentity,
    selected_identity: StreamIdentity,
    units: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    target = directory / selected_identity.name
    partial = directory / (
        f"{selected_identity.name}{PARTIAL_SUFFIX}.{secrets.token_hex(16)}"
    )
    source_metadata = inspect_stream(source, source_identity)
    if _lexists(target):
        raise FileExistsError(f"refusing to overwrite leaf target: {target}")
    if _lexists(partial):
        raise FileExistsError(f"fresh random leaf partial already exists: {partial}")
    with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
        with safety.create_new_exclusive_binary(
            partial, buffering=COPY_BLOCK_BYTES
        ) as (target_stream, owned_identity):
            copied_source, target_metadata = _copy_body(
                source_stream,
                target_stream,
                source_identity,
                selected_identity,
                units,
            )
            target_stream.flush()
            os.fsync(target_stream.fileno())
    if copied_source != source_metadata:
        raise R34LeafMaterializerError("F7 changed between validation and copy")
    partial_lock = (
        safety.WindowsReadLocks([partial]) if os.name == "nt" else nullcontext()
    )
    with partial_lock:
        inspect_stream(partial, selected_identity, enforce_name=False)
        compare_exact_layout(source, partial, source_identity, selected_identity, units)
        if safety.regular_file_object_identity(partial) != owned_identity:
            raise R34LeafMaterializerError("leaf partial object was replaced")
        if _lexists(target):
            raise FileExistsError(f"leaf target appeared during generation: {target}")
    # Windows denies a rename while the exact partial handle (or a parent
    # DirectoryGuard without FILE_SHARE_DELETE) is open.  Close validation,
    # then make publication the immediate next operation.  The declared
    # controlled-workspace model permits this narrow close/reopen window.
    os.rename(partial, target)
    published_lock = (
        safety.WindowsReadLocks([source, target])
        if os.name == "nt"
        else nullcontext()
    )
    with published_lock:
        if safety.regular_file_object_identity(target) != owned_identity:
            raise R34LeafMaterializerError(
                "leaf object changed across publication rename"
            )
        published = inspect_stream(target, selected_identity)
        compare_exact_layout(source, target, source_identity, selected_identity, units)
        if safety.regular_file_object_identity(target) != owned_identity:
            raise R34LeafMaterializerError("published leaf object was replaced")
        if published != target_metadata:
            raise R34LeafMaterializerError("published leaf metadata changed")
    return {
        "status": "GENERATED_EXACT_PARAMETERIZED_R34_LEAF_WITHOUT_SOLVER",
        "source": source_metadata,
        "target": published,
        "body_reused_byte_for_byte": True,
        "unit_clauses": registry.UNIT_COUNT,
        "failure_policy": "leave any fresh random partial quarantined; never delete or overwrite",
    }


def verify_checked(
    directory: Path,
    source_identity: StreamIdentity,
    selected_identity: StreamIdentity,
    units: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    target = directory / selected_identity.name
    source_metadata = inspect_stream(source, source_identity)
    target_metadata = inspect_stream(target, selected_identity)
    compare_exact_layout(source, target, source_identity, selected_identity, units)
    return {
        "status": "PASS_EXACT_PARAMETERIZED_R34_LEAF_LAYOUT",
        "source": source_metadata,
        "target": target_metadata,
        "body_reused_byte_for_byte": True,
        "exact_ordered_unit_suffix": True,
    }


def selection_payload(spec: registry.LeafSpec) -> dict[str, object]:
    return {
        "slug": spec.slug,
        "record": spec.record,
        "source_catalogue_index_zero_based": spec.source_catalogue_index_zero_based,
        "incremental_position_one_based": spec.incremental_position_one_based,
        "degree_sequence": list(spec.degree_sequence),
        "cube": list(spec.cube),
        "unit_payload_bytes": spec.unit_payload_bytes,
        "unit_payload_sha256": spec.unit_payload_sha256,
        "pilot_conflicts": spec.pilot_conflicts,
        "pilot_elapsed_seconds": spec.pilot_elapsed_seconds,
    }


def preflight(slug: str | None = None) -> dict[str, object]:
    inventory = registry.audit_registry()
    specs = registry.ACTIONABLE_LEAVES if slug is None else (registry.select_actionable(slug),)
    targets = []
    for spec in specs:
        payload = unit_payload(spec)
        expected_bytes = (
            SOURCE_BYTES - len(SOURCE_HEADER) + len(TARGET_HEADER) + len(payload)
        )
        if expected_bytes != spec.target_bytes:
            raise R34LeafMaterializerError(f"target byte arithmetic changed for {spec.slug}")
        if SOURCE_CLAUSES + registry.UNIT_COUNT != TARGET_CLAUSES:
            raise R34LeafMaterializerError("target clause arithmetic changed")
        targets.append(
            {
                "selection": selection_payload(spec),
                "target": {
                    "name": spec.target_name,
                    "variables": SOURCE_VARIABLES,
                    "clauses": TARGET_CLAUSES,
                    "bytes": spec.target_bytes,
                    "lines": TARGET_LINES,
                    "sha256": spec.target_sha256,
                },
            }
        )
    return {
        "status": "PASS_PARAMETERIZED_R34_LEAF_PREFLIGHT_NO_S_NO_SOLVER",
        "source": {
            "name": SOURCE_NAME,
            "variables": SOURCE_VARIABLES,
            "clauses": SOURCE_CLAUSES,
            "bytes": SOURCE_BYTES,
            "lines": SOURCE_LINES,
            "sha256": SOURCE_SHA256,
        },
        "targets": targets,
        "first_leaf": registry.FIRST_LEAF_SLUG,
        "first_leaf_rationale": registry.FIRST_LEAF_RATIONALE,
        "inventory_status": inventory["status"],
        "path_policy": (
            "generate/verify require existing absolute S: paths, reject '..', "
            "and reject every existing symlink/junction/reparse component; "
            "generation closes its validated partial/parent guard for the atomic "
            "Windows rename, then immediately read-locks and revalidates source "
            "plus final target; verify keeps directory/source/target guarded"
        ),
        "overwrite_policy": (
            "refuse final target; use a fresh random .partial.<128-bit> name, "
            "never delete it on failure, and track its object identity across "
            "atomic rename and post-publication rehash"
        ),
        "solver_policy": "this module never invokes a SAT solver",
        "frozen_path_policy": "FgraveGOW and FGgraveXo are explicitly unselectable",
        "formal_boundary": (
            "exact CNF construction only; no UNSAT certificate, Lean theorem, "
            "S7 composition, or Ramsey-number bound"
        ),
    }


def _emit_catalogue(
    source_digest: "hashlib._Hash",
    target_digest: "hashlib._Hash",
    variables: Sequence[int],
    compiled: Sequence[Sequence[tuple[int, bool]]],
) -> tuple[int, int]:
    tokens = tuple((str(variable), f"-{variable}") for variable in variables)
    size = 0
    written = 0
    buffer: list[str] = []
    for clause in compiled:
        buffer.append(
            " ".join(tokens[position][1 if one else 0] for position, one in clause)
            + " 0\n"
        )
        written += 1
        if len(buffer) == 2_048:
            data = "".join(buffer).encode("ascii")
            source_digest.update(data)
            target_digest.update(data)
            size += len(data)
            buffer.clear()
    if buffer:
        data = "".join(buffer).encode("ascii")
        source_digest.update(data)
        target_digest.update(data)
        size += len(data)
    return written, size


def primitive_fingerprints(slug: str | None = None) -> dict[str, object]:
    """Reconstruct F7 and one/all pending target hashes without touching S:."""

    preflight(slug)
    specs = registry.ACTIONABLE_LEAVES if slug is None else (registry.select_actionable(slug),)
    blocks = source_audit.block_catalogues()
    locals_ = source_audit.local_catalogues()
    compiled_blocks = tuple(
        tuple(source_audit.compiled_cube(cube, source_audit.LOCAL_EDGES) for cube in group)
        for group in blocks
    )
    compiled_locals = tuple(
        tuple(source_audit.compiled_cube(cube, 15) for cube in group)
        for group in locals_
    )
    source_digest = hashlib.sha256()
    target_prefix_digest = hashlib.sha256()
    source_digest.update(SOURCE_HEADER)
    target_prefix_digest.update(TARGET_HEADER)
    source_size = len(SOURCE_HEADER)
    target_prefix_size = len(TARGET_HEADER)
    written = 0
    for clause in source_audit.base_clauses():
        data = source_audit.clause_line(clause)
        source_digest.update(data)
        target_prefix_digest.update(data)
        source_size += len(data)
        target_prefix_size += len(data)
        written += 1
    for vertices in itertools.combinations(range(1, 12), 7):
        neighbour_count = sum(vertex <= 7 for vertex in vertices)
        amount, size = _emit_catalogue(
            source_digest,
            target_prefix_digest,
            source_audit.subset_variables(vertices),
            compiled_blocks[neighbour_count],
        )
        written += amount
        source_size += size
        target_prefix_size += size
    for vertices in itertools.combinations(range(1, 12), 6):
        neighbour_count = sum(vertex <= 7 for vertex in vertices)
        amount, size = _emit_catalogue(
            source_digest,
            target_prefix_digest,
            source_audit.subset_variables(vertices),
            compiled_locals[neighbour_count],
        )
        written += amount
        source_size += size
        target_prefix_size += size
    source_hash = source_digest.hexdigest().upper()
    if (written, source_size, source_hash) != (
        SOURCE_CLAUSES,
        SOURCE_BYTES,
        SOURCE_SHA256,
    ):
        raise R34LeafMaterializerError("primitive F7 reconstruction identity changed")
    targets = []
    for spec in specs:
        payload = unit_payload(spec)
        digest = target_prefix_digest.copy()
        digest.update(payload)
        observed = {
            "name": spec.target_name,
            "bytes": target_prefix_size + len(payload),
            "sha256": digest.hexdigest().upper(),
            "lines": TARGET_LINES,
        }
        if (observed["bytes"], observed["sha256"]) != (
            spec.target_bytes,
            spec.target_sha256,
        ):
            raise R34LeafMaterializerError(f"primitive target hash changed for {spec.slug}")
        targets.append({"slug": spec.slug, **observed})
    return {
        "status": "PASS_LOCAL_STREAMED_PRIMITIVE_FINGERPRINTS_NO_S_NO_SOLVER",
        "source": {"clauses": written, "bytes": source_size, "sha256": source_hash},
        "targets": targets,
        "single_f7_reconstruction_pass": True,
    }


def generate(directory: Path, slug: str) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    preflight(slug)
    directory = require_ssd_directory(directory)
    try:
        safety.require_existing_directory(directory, "leaf directory")
        safety.require_existing_regular_file(
            directory / SOURCE_IDENTITY.name, "frozen F7 source"
        )
        for candidate, label in (
            (directory / spec.target_name, "leaf target"),
            (directory / f"{spec.target_name}{PARTIAL_SUFFIX}", "leaf partial"),
        ):
            safety.reject_absolute_s_reparse(candidate, label)
    except safety.R34PathSafetyError as error:
        raise R34LeafMaterializerError(str(error)) from error
    source = directory / SOURCE_IDENTITY.name
    # WindowsDirectoryGuard deliberately omits FILE_SHARE_DELETE and therefore
    # blocks a child rename.  Keep the immutable source locked, while
    # materialize_checked closes its partial lock immediately before the
    # atomic publication and reopens the final target immediately afterwards.
    with safety.WindowsReadLocks([source]):
        try:
            safety.require_existing_directory(directory, "guarded leaf directory")
            safety.require_existing_regular_file(source, "locked frozen F7 source")
            for candidate, label in (
                (directory / spec.target_name, "guarded leaf target"),
                (
                    directory / f"{spec.target_name}{PARTIAL_SUFFIX}",
                    "guarded leaf partial",
                ),
            ):
                safety.reject_absolute_s_reparse(candidate, label)
        except safety.R34PathSafetyError as error:
            raise R34LeafMaterializerError(str(error)) from error
        result = materialize_checked(
            directory, SOURCE_IDENTITY, target_identity(spec), unit_payload(spec)
        )
        target = directory / spec.target_name
        with safety.WindowsReadLocks([source, target]):
            try:
                safety.require_existing_regular_file(
                    target, "locked published leaf target"
                )
                safety.require_existing_regular_file(source, "locked frozen F7 source")
                safety.require_existing_directory(directory, "guarded leaf directory")
            except safety.R34PathSafetyError as error:
                raise R34LeafMaterializerError(str(error)) from error
            final_target = inspect_stream(target, target_identity(spec))
            compare_exact_layout(
                source, target, SOURCE_IDENTITY, target_identity(spec), unit_payload(spec)
            )
            if final_target != result["target"]:
                raise R34LeafMaterializerError(
                    "published leaf changed before guarded generate return"
                )
            result["selection"] = selection_payload(spec)
            return result


def verify(directory: Path, slug: str) -> dict[str, object]:
    spec = registry.select_actionable(slug)
    preflight(slug)
    directory = require_ssd_directory(directory)
    try:
        safety.require_existing_directory(directory, "leaf directory")
        safety.require_existing_regular_file(
            directory / SOURCE_IDENTITY.name, "frozen F7 source"
        )
        safety.require_existing_regular_file(
            directory / spec.target_name, "leaf target"
        )
    except safety.R34PathSafetyError as error:
        raise R34LeafMaterializerError(str(error)) from error
    source = directory / SOURCE_IDENTITY.name
    target = directory / spec.target_name
    with safety.WindowsDirectoryGuard(directory), safety.WindowsReadLocks(
        [source, target]
    ):
        try:
            safety.require_existing_directory(directory, "guarded leaf directory")
            safety.require_existing_regular_file(source, "locked frozen F7 source")
            safety.require_existing_regular_file(target, "locked leaf target")
            safety.reject_absolute_s_reparse(
                directory / f"{spec.target_name}{PARTIAL_SUFFIX}",
                "guarded leaf partial",
            )
        except safety.R34PathSafetyError as error:
            raise R34LeafMaterializerError(str(error)) from error
        result = verify_checked(
            directory, SOURCE_IDENTITY, target_identity(spec), unit_payload(spec)
        )
        result["selection"] = selection_payload(spec)
        return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        default="preflight",
        choices=("inventory", "preflight", "fingerprint", "generate", "verify"),
    )
    parser.add_argument("--leaf", choices=registry.ACTIONABLE_SLUGS)
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    if args.command == "inventory":
        result = registry.audit_registry()
    elif args.command == "preflight":
        result = preflight(args.leaf)
    elif args.command == "fingerprint":
        result = primitive_fingerprints(args.leaf)
    else:
        if args.leaf is None or args.directory is None:
            parser.error("generate/verify require --leaf and --directory")
        result = generate(args.directory, args.leaf) if args.command == "generate" else verify(args.directory, args.leaf)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
