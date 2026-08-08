#!/usr/bin/env python3
"""Materialize one exact F7 leaf for the order-seven R34 record F-grave-GOW.

The target is the frozen degree-seven source body followed by 21 unit clauses
fixing all internal edges of the positive root neighbourhood. The selected
record is source catalogue index five and incremental-screen position six.

Preflight and primitive fingerprinting use only tracked repository inputs.
Generation and verification require an existing absolute S: directory,
refuse an existing target or residual partial, and invoke no SAT solver.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from dataclasses import dataclass
from pathlib import Path, PureWindowsPath
from typing import BinaryIO, Sequence

from . import audit_cover6_d7_min_center_source as source_audit
from . import materialize_cover6_d7_r34_catalogue_icnf as catalogue


SOURCE_NAME = "cover6_closed_block_degree_d7.cnf"
TARGET_NAME = "cover6_closed_f7_r34_i6_FgraveGOW.cnf"
PARTIAL_SUFFIX = ".partial"

SOURCE_HEADER = b"p cnf 66 4312419\n"
TARGET_HEADER = b"p cnf 66 4312440\n"
SOURCE_BYTES = 246_507_515
SOURCE_SHA256 = "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C"
SOURCE_LINES = 4_312_420
SOURCE_CLAUSES = 4_312_419

TARGET_VARIABLES = 66
TARGET_CLAUSES = 4_312_440
TARGET_BYTES = 246_507_635
TARGET_LINES = 4_312_441
TARGET_SHA256 = "78D066E03B1F55FACBF8839BCC409E0D45BABF93FA6D266628BB526D2F5E5971"

TICK = chr(96)
RECORD = "F" + TICK + "GOW"
SOURCE_CATALOGUE_INDEX_ZERO_BASED = 5
INCREMENTAL_POSITION_ONE_BASED = 6
EXPECTED_CUBE = (
    12,
    -13,
    -14,
    -15,
    -16,
    -17,
    -22,
    -23,
    -24,
    -25,
    -26,
    31,
    32,
    -33,
    -34,
    -39,
    40,
    -41,
    -46,
    47,
    52,
)
UNIT_COUNT = 21
UNIT_PAYLOAD_BYTES = 120
UNIT_PAYLOAD_SHA256 = (
    "4C2D8603575965D0CB08E3CDC7AC7AD463CA369D4EDDB645E565599A0F13373F"
)

COPY_BLOCK_BYTES = 8 * 1024 * 1024


class FgraveGowLeafError(ValueError):
    """Raised at the first selection, identity, path, or layout mismatch."""


@dataclass(frozen=True)
class StreamIdentity:
    name: str
    header: bytes
    bytes: int
    sha256: str
    lines: int


SOURCE_IDENTITY = StreamIdentity(
    SOURCE_NAME,
    SOURCE_HEADER,
    SOURCE_BYTES,
    SOURCE_SHA256,
    SOURCE_LINES,
)
TARGET_IDENTITY = StreamIdentity(
    TARGET_NAME,
    TARGET_HEADER,
    TARGET_BYTES,
    TARGET_SHA256,
    TARGET_LINES,
)


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def unit_line(literal: int) -> bytes:
    if not 1 <= abs(literal) <= TARGET_VARIABLES:
        raise FgraveGowLeafError(f"unit literal outside 1..66: {literal}")
    return f"{literal} 0\n".encode("ascii")


def unit_payload(cube: Sequence[int] = EXPECTED_CUBE) -> bytes:
    if len(cube) != UNIT_COUNT:
        raise FgraveGowLeafError("the selected R34 leaf must assign 21 variables")
    if len({abs(literal) for literal in cube}) != UNIT_COUNT:
        raise FgraveGowLeafError("the selected R34 leaf repeats a variable")
    if {abs(literal) for literal in cube} != set(catalogue.H_VARIABLES):
        raise FgraveGowLeafError("the selected R34 leaf does not assign the exact K7 block")
    return b"".join(unit_line(literal) for literal in cube)


UNIT_PAYLOAD = unit_payload()


def audit_selection() -> dict[str, object]:
    source_records = catalogue.SOURCE_R34_RECORDS
    ordered_records = catalogue.ORDERED_R34_RECORDS
    if source_records[SOURCE_CATALOGUE_INDEX_ZERO_BASED] != RECORD:
        raise FgraveGowLeafError("source R34 catalogue index five changed")
    if ordered_records[INCREMENTAL_POSITION_ONE_BASED - 1] != RECORD:
        raise FgraveGowLeafError("incremental R34 position six changed")
    cube = catalogue.cube_for_record(RECORD)
    if cube != EXPECTED_CUBE:
        raise FgraveGowLeafError(f"F-grave-GOW cube changed: {cube}")
    if catalogue.degree_sequence(catalogue.graph6_mask(RECORD)) != (
        1,
        1,
        2,
        2,
        2,
        2,
        2,
    ):
        raise FgraveGowLeafError("F-grave-GOW degree sequence changed")
    payload = unit_payload(cube)
    if len(payload) != UNIT_PAYLOAD_BYTES:
        raise FgraveGowLeafError(f"unit payload byte count changed: {len(payload)}")
    if sha256_bytes(payload) != UNIT_PAYLOAD_SHA256:
        raise FgraveGowLeafError("unit payload SHA-256 changed")
    return {
        "record": RECORD,
        "source_catalogue_index_zero_based": SOURCE_CATALOGUE_INDEX_ZERO_BASED,
        "incremental_position_one_based": INCREMENTAL_POSITION_ONE_BASED,
        "degree_sequence": [1, 1, 2, 2, 2, 2, 2],
        "cube": list(cube),
        "unit_lines": payload.decode("ascii").splitlines(),
        "unit_payload_bytes": len(payload),
        "unit_payload_sha256": sha256_bytes(payload),
    }


def require_ssd_directory(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise FgraveGowLeafError(
            f"F-grave-GOW leaf directory must be an absolute S: path, got {path}"
        )
    return path


def inspect_stream(
    path: Path,
    identity: StreamIdentity,
    *,
    enforce_name: bool = True,
) -> dict[str, int | str]:
    if enforce_name and path.name != identity.name:
        raise FgraveGowLeafError(
            f"stream name mismatch: {path.name!r} != {identity.name!r}"
        )
    digest = hashlib.sha256()
    size = 0
    lines = 0
    with path.open("rb", buffering=COPY_BLOCK_BYTES) as stream:
        header = stream.readline()
        if header != identity.header:
            raise FgraveGowLeafError(
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
        raise FgraveGowLeafError(
            f"stream identity mismatch for {path.name}: {observed} != {expected}"
        )
    return {
        "name": path.name,
        "bytes": size,
        "sha256": observed[1],
        "lines": lines,
    }


def _copy_body(
    source: BinaryIO,
    target: BinaryIO,
    source_identity: StreamIdentity,
    target_identity: StreamIdentity,
    units: bytes,
) -> tuple[dict[str, int | str], dict[str, int | str]]:
    source_digest = hashlib.sha256()
    target_digest = hashlib.sha256()
    source_header = source.readline()
    if source_header != source_identity.header:
        raise FgraveGowLeafError("F7 header changed between validation and copy")
    source_digest.update(source_header)
    source_size = len(source_header)
    source_lines = 1
    target.write(target_identity.header)
    target_digest.update(target_identity.header)
    target_size = len(target_identity.header)
    target_lines = 1
    for block in iter(lambda: source.read(COPY_BLOCK_BYTES), b""):
        source_digest.update(block)
        source_size += len(block)
        source_lines += block.count(b"\n")
        target.write(block)
        target_digest.update(block)
        target_size += len(block)
        target_lines += block.count(b"\n")
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
        raise FgraveGowLeafError(
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
        target_identity.bytes,
        target_identity.sha256,
        target_identity.lines,
    )
    if observed_target != expected_target:
        raise FgraveGowLeafError(
            f"leaf identity mismatch: {observed_target} != {expected_target}"
        )
    return (
        {
            "name": source_identity.name,
            "bytes": source_size,
            "sha256": observed_source[1],
            "lines": source_lines,
        },
        {
            "name": target_identity.name,
            "bytes": target_size,
            "sha256": observed_target[1],
            "lines": target_lines,
        },
    )


def compare_exact_layout(
    source: Path,
    target: Path,
    source_identity: StreamIdentity,
    target_identity: StreamIdentity,
    units: bytes,
) -> None:
    with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
        with target.open("rb", buffering=COPY_BLOCK_BYTES) as target_stream:
            if source_stream.readline() != source_identity.header:
                raise FgraveGowLeafError("F7 header changed during layout check")
            if target_stream.readline() != target_identity.header:
                raise FgraveGowLeafError("leaf header changed during layout check")
            remaining = source_identity.bytes - len(source_identity.header)
            while remaining:
                amount = min(COPY_BLOCK_BYTES, remaining)
                source_block = source_stream.read(amount)
                target_block = target_stream.read(amount)
                if len(source_block) != amount or target_block != source_block:
                    raise FgraveGowLeafError(
                        "leaf clause body is not byte-for-byte identical to F7"
                    )
                remaining -= amount
            if source_stream.read(1):
                raise FgraveGowLeafError("unexpected F7 suffix")
            if target_stream.read() != units:
                raise FgraveGowLeafError(
                    "leaf suffix is not the exact ordered 21-unit payload"
                )


def materialize_checked(
    directory: Path,
    source_identity: StreamIdentity,
    target_identity: StreamIdentity,
    units: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    target = directory / target_identity.name
    partial = directory / f"{target_identity.name}{PARTIAL_SUFFIX}"
    source_metadata = inspect_stream(source, source_identity)
    if target.exists():
        raise FileExistsError(f"refusing to overwrite F-grave-GOW leaf: {target}")
    if partial.exists():
        raise FileExistsError(f"refusing residual leaf partial: {partial}")
    created_partial = False
    try:
        with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
            with partial.open("xb", buffering=COPY_BLOCK_BYTES) as target_stream:
                created_partial = True
                copied_source, target_metadata = _copy_body(
                    source_stream,
                    target_stream,
                    source_identity,
                    target_identity,
                    units,
                )
        if copied_source != source_metadata:
            raise FgraveGowLeafError(
                "F7 metadata differs between validation and materialization"
            )
        inspect_stream(partial, target_identity, enforce_name=False)
        compare_exact_layout(
            source, partial, source_identity, target_identity, units
        )
        if target.exists():
            raise FileExistsError(f"leaf target appeared during generation: {target}")
        os.rename(partial, target)
        created_partial = False
    finally:
        if created_partial and partial.exists():
            partial.unlink()
    published = inspect_stream(target, target_identity)
    if published != target_metadata:
        raise FgraveGowLeafError("published leaf metadata changed")
    return {
        "status": "GENERATED_EXACT_F7_R34_FGRAVEGOW_LEAF_WITHOUT_SOLVER",
        "source": source_metadata,
        "target": published,
        "body_reused_byte_for_byte": True,
        "unit_clauses": UNIT_COUNT,
        "selection": audit_selection(),
    }


def verify_checked(
    directory: Path,
    source_identity: StreamIdentity,
    target_identity: StreamIdentity,
    units: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    target = directory / target_identity.name
    partial = directory / f"{target_identity.name}{PARTIAL_SUFFIX}"
    if partial.exists():
        raise FileExistsError(f"refusing residual leaf partial: {partial}")
    source_metadata = inspect_stream(source, source_identity)
    target_metadata = inspect_stream(target, target_identity)
    compare_exact_layout(source, target, source_identity, target_identity, units)
    return {
        "status": "PASS_EXACT_F7_R34_FGRAVEGOW_LEAF_LAYOUT",
        "source": source_metadata,
        "target": target_metadata,
        "body_reused_byte_for_byte": True,
        "exact_ordered_unit_suffix": True,
    }


def preflight() -> dict[str, object]:
    selection = audit_selection()
    expected_bytes = (
        SOURCE_BYTES - len(SOURCE_HEADER) + len(TARGET_HEADER) + len(UNIT_PAYLOAD)
    )
    if expected_bytes != TARGET_BYTES:
        raise FgraveGowLeafError(f"leaf byte arithmetic changed: {expected_bytes}")
    if SOURCE_CLAUSES + UNIT_COUNT != TARGET_CLAUSES:
        raise FgraveGowLeafError("leaf clause arithmetic changed")
    if 1 + TARGET_CLAUSES != TARGET_LINES:
        raise FgraveGowLeafError("leaf line arithmetic changed")
    return {
        "status": "PASS",
        "source": {
            "name": SOURCE_NAME,
            "variables": TARGET_VARIABLES,
            "clauses": SOURCE_CLAUSES,
            "bytes": SOURCE_BYTES,
            "lines": SOURCE_LINES,
            "sha256": SOURCE_SHA256,
        },
        "target": {
            "name": TARGET_NAME,
            "variables": TARGET_VARIABLES,
            "clauses": TARGET_CLAUSES,
            "bytes": TARGET_BYTES,
            "lines": TARGET_LINES,
            "sha256": TARGET_SHA256,
        },
        "selection": selection,
        "path_policy": "generate/verify require an absolute S: directory",
        "overwrite_policy": "refuse existing target and residual .partial",
        "solver_policy": "this program never invokes a SAT solver",
        "scope": (
            "exact one-leaf construction only; no SAT, UNSAT, LRAT, Lean "
            "composition, cover6-d7 theorem, or Ramsey-number claim"
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
    for specification in compiled:
        buffer.append(
            " ".join(
                tokens[position][1 if one else 0]
                for position, one in specification
            )
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


def primitive_fingerprint() -> dict[str, object]:
    """Reconstruct F7 and the leaf hashes locally without reading S:."""

    preflight()
    blocks = source_audit.block_catalogues()
    locals_ = source_audit.local_catalogues()
    compiled_blocks = tuple(
        tuple(
            source_audit.compiled_cube(cube, source_audit.LOCAL_EDGES)
            for cube in local_catalogue
        )
        for local_catalogue in blocks
    )
    compiled_locals = tuple(
        tuple(source_audit.compiled_cube(cube, 15) for cube in local_catalogue)
        for local_catalogue in locals_
    )
    source_digest = hashlib.sha256()
    target_digest = hashlib.sha256()
    source_digest.update(SOURCE_HEADER)
    target_digest.update(TARGET_HEADER)
    source_size = len(SOURCE_HEADER)
    target_size = len(TARGET_HEADER)
    written = 0
    for clause in source_audit.base_clauses():
        data = source_audit.clause_line(clause)
        source_digest.update(data)
        target_digest.update(data)
        source_size += len(data)
        target_size += len(data)
        written += 1
    for vertices in itertools.combinations(range(1, 12), 7):
        neighbour_count = sum(vertex <= 7 for vertex in vertices)
        amount, size = _emit_catalogue(
            source_digest,
            target_digest,
            source_audit.subset_variables(vertices),
            compiled_blocks[neighbour_count],
        )
        written += amount
        source_size += size
        target_size += size
    for vertices in itertools.combinations(range(1, 12), 6):
        neighbour_count = sum(vertex <= 7 for vertex in vertices)
        amount, size = _emit_catalogue(
            source_digest,
            target_digest,
            source_audit.subset_variables(vertices),
            compiled_locals[neighbour_count],
        )
        written += amount
        source_size += size
        target_size += size
    source_hash = source_digest.hexdigest().upper()
    if (written, source_size, source_hash) != (
        SOURCE_CLAUSES,
        SOURCE_BYTES,
        SOURCE_SHA256,
    ):
        raise FgraveGowLeafError(
            f"primitive F7 reconstruction changed: {(written, source_size, source_hash)}"
        )
    target_digest.update(UNIT_PAYLOAD)
    target_size += len(UNIT_PAYLOAD)
    target_hash = target_digest.hexdigest().upper()
    if target_size != TARGET_BYTES:
        raise FgraveGowLeafError("primitive leaf byte count changed")
    if target_hash != TARGET_SHA256:
        raise FgraveGowLeafError(f"primitive leaf SHA-256 changed: {target_hash}")
    return {
        "status": "PASS",
        "mode": "local primitive reconstruction; no S: read, no write, no solver",
        "source": {
            "clauses": written,
            "bytes": source_size,
            "sha256": source_hash,
        },
        "target": {
            "variables": TARGET_VARIABLES,
            "clauses": TARGET_CLAUSES,
            "bytes": target_size,
            "lines": TARGET_LINES,
            "sha256": target_hash,
        },
    }


def generate(directory: Path) -> dict[str, object]:
    preflight()
    directory = require_ssd_directory(directory)
    return materialize_checked(
        directory,
        SOURCE_IDENTITY,
        TARGET_IDENTITY,
        UNIT_PAYLOAD,
    )


def verify(directory: Path) -> dict[str, object]:
    preflight()
    directory = require_ssd_directory(directory)
    return verify_checked(
        directory,
        SOURCE_IDENTITY,
        TARGET_IDENTITY,
        UNIT_PAYLOAD,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        default="preflight",
        choices=("preflight", "fingerprint", "generate", "verify"),
    )
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    elif args.command == "fingerprint":
        result = primitive_fingerprint()
    else:
        if args.directory is None:
            parser.error("generate/verify require --directory")
        result = generate(args.directory) if args.command == "generate" else verify(args.directory)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
