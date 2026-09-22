#!/usr/bin/env python3
"""Materialize the exact nine-case degree-seven cover6 master CNF.

The source must be the frozen F7 emitted by
``generate_complement_closed_cover6_branches.py``.  Generation verifies the
source identity, copies its body byte-for-byte under a rewritten clause-count
header, appends nine frozen normalization clauses, and checks the resulting
identity before publishing it.  Existing targets and residual partial files
are never overwritten.

Public ``generate`` and ``verify`` operations accept only an absolute S: path.
No solver or proof checker is invoked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from dataclasses import dataclass
from pathlib import Path, PureWindowsPath
from typing import BinaryIO, Sequence


SOURCE_NAME = "cover6_closed_block_degree_d7.cnf"
MASTER_NAME = "cover6_closed_master_d7_min_center9.cnf"
PARTIAL_SUFFIX = ".partial"

SOURCE_HEADER = b"p cnf 66 4312419\n"
MASTER_HEADER = b"p cnf 66 4312428\n"

EXTRA_CLAUSES: tuple[tuple[int, ...], ...] = (
    (12,),
    (-14,),
    (14, -15),
    (15, -16),
    (16, -17),
    (18, -19),
    (19, -20),
    (20, -21),
    (13, 18),
)

SOURCE_BYTES = 246_507_515
SOURCE_SHA256 = "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C"
SOURCE_LINES = 4_312_420
MASTER_BYTES = 246_507_588
MASTER_SHA256 = "DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE"
MASTER_LINES = 4_312_429

COPY_BLOCK_BYTES = 8 * 1024 * 1024


class Master7MaterializationError(ValueError):
    """Raised at the first path, identity, or byte-layout mismatch."""


@dataclass(frozen=True)
class FormulaIdentity:
    name: str
    header: bytes
    bytes: int
    sha256: str
    lines: int


SOURCE_IDENTITY = FormulaIdentity(
    name=SOURCE_NAME,
    header=SOURCE_HEADER,
    bytes=SOURCE_BYTES,
    sha256=SOURCE_SHA256,
    lines=SOURCE_LINES,
)
MASTER_IDENTITY = FormulaIdentity(
    name=MASTER_NAME,
    header=MASTER_HEADER,
    bytes=MASTER_BYTES,
    sha256=MASTER_SHA256,
    lines=MASTER_LINES,
)


def clause_line(clause: Sequence[int]) -> bytes:
    if not clause:
        raise Master7MaterializationError("normalization clauses must be nonempty")
    if any(not 1 <= abs(literal) <= 66 for literal in clause):
        raise Master7MaterializationError("normalization literal is outside 1..66")
    if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
        raise Master7MaterializationError("normalization clause is duplicate or tautological")
    return (" ".join(map(str, clause)) + " 0\n").encode("ascii")


def extra_payload(clauses: Sequence[Sequence[int]] = EXTRA_CLAUSES) -> bytes:
    return b"".join(clause_line(clause) for clause in clauses)


EXTRA_PAYLOAD = extra_payload()


def require_ssd_directory(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise Master7MaterializationError(
            f"Master7 artifact directory must be an absolute S: path, got {path}"
        )
    return path


def _identity_dict(identity: FormulaIdentity) -> dict[str, int | str]:
    return {
        "name": identity.name,
        "bytes": identity.bytes,
        "sha256": identity.sha256,
        "lines": identity.lines,
    }


def inspect_formula(
    path: Path,
    identity: FormulaIdentity,
    *,
    enforce_name: bool = True,
) -> dict[str, int | str]:
    if enforce_name and path.name != identity.name:
        raise Master7MaterializationError(
            f"formula name mismatch: {path.name!r} != {identity.name!r}"
        )
    digest = hashlib.sha256()
    size = 0
    lines = 0
    with path.open("rb", buffering=COPY_BLOCK_BYTES) as stream:
        header = stream.readline()
        if header != identity.header:
            raise Master7MaterializationError(
                f"DIMACS header mismatch in {path.name}: {header!r}"
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
        raise Master7MaterializationError(
            f"formula identity mismatch for {path.name}: {observed} != {expected}"
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
    source_identity: FormulaIdentity,
    master_identity: FormulaIdentity,
    extras: bytes,
) -> tuple[dict[str, int | str], dict[str, int | str]]:
    source_digest = hashlib.sha256()
    master_digest = hashlib.sha256()

    source_header = source.readline()
    if source_header != source_identity.header:
        raise Master7MaterializationError("source header changed between validation and copy")
    source_digest.update(source_header)
    source_size = len(source_header)
    source_lines = 1

    target.write(master_identity.header)
    master_digest.update(master_identity.header)
    master_size = len(master_identity.header)
    master_lines = 1

    for block in iter(lambda: source.read(COPY_BLOCK_BYTES), b""):
        source_digest.update(block)
        source_size += len(block)
        source_lines += block.count(b"\n")
        target.write(block)
        master_digest.update(block)
        master_size += len(block)
        master_lines += block.count(b"\n")

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
        raise Master7MaterializationError(
            f"source changed during materialization: {observed_source} != {expected_source}"
        )

    target.write(extras)
    master_digest.update(extras)
    master_size += len(extras)
    master_lines += extras.count(b"\n")
    observed_master = (
        master_size,
        master_digest.hexdigest().upper(),
        master_lines,
    )
    expected_master = (
        master_identity.bytes,
        master_identity.sha256,
        master_identity.lines,
    )
    if observed_master != expected_master:
        raise Master7MaterializationError(
            f"materialized Master7 identity mismatch: {observed_master} != {expected_master}"
        )

    return (
        {
            "name": source_identity.name,
            "bytes": source_size,
            "sha256": observed_source[1],
            "lines": source_lines,
        },
        {
            "name": master_identity.name,
            "bytes": master_size,
            "sha256": observed_master[1],
            "lines": master_lines,
        },
    )


def materialize_checked(
    directory: Path,
    source_identity: FormulaIdentity,
    master_identity: FormulaIdentity,
    extras: bytes,
) -> dict[str, object]:
    """Core materializer; public callers must apply the S: policy first.

    Keeping the path policy outside this function permits byte-sized temporary
    fixtures to test all failure modes without touching S: or rendering F7.
    """

    source = directory / source_identity.name
    target = directory / master_identity.name
    partial = directory / f"{master_identity.name}{PARTIAL_SUFFIX}"

    # First pass rejects the wrong producer output before creating a partial.
    source_metadata = inspect_formula(source, source_identity)
    if target.exists():
        raise FileExistsError(f"refusing to overwrite Master7 target: {target}")
    if partial.exists():
        raise FileExistsError(f"refusing residual Master7 partial: {partial}")

    created_partial = False
    try:
        with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
            with partial.open("xb", buffering=COPY_BLOCK_BYTES) as target_stream:
                created_partial = True
                copied_source, master_metadata = _copy_body(
                    source_stream,
                    target_stream,
                    source_identity,
                    master_identity,
                    extras,
                )
        if copied_source != source_metadata:
            raise Master7MaterializationError(
                "source metadata differs between validation and materialization"
            )
        inspect_formula(partial, master_identity, enforce_name=False)
        if target.exists():
            raise FileExistsError(f"Master7 target appeared during generation: {target}")
        # On Windows, os.rename refuses an existing destination.  This keeps
        # publication non-overwriting even if another process races this one.
        os.rename(partial, target)
        created_partial = False
    finally:
        if created_partial and partial.exists():
            partial.unlink()

    published = inspect_formula(target, master_identity)
    if published != master_metadata:
        raise Master7MaterializationError("published Master7 metadata changed")
    return {
        "status": "GENERATED_EXACT_MASTER7_WITHOUT_SOLVER",
        "source": source_metadata,
        "master": published,
        "header_rewrite": {
            "source": source_identity.header.decode("ascii").rstrip("\n"),
            "master": master_identity.header.decode("ascii").rstrip("\n"),
        },
        "appended_clauses": len(EXTRA_CLAUSES),
        "appended_bytes": len(extras),
    }


def compare_exact_layout(
    source: Path,
    master: Path,
    source_identity: FormulaIdentity,
    master_identity: FormulaIdentity,
    extras: bytes,
) -> None:
    with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
        with master.open("rb", buffering=COPY_BLOCK_BYTES) as master_stream:
            if source_stream.readline() != source_identity.header:
                raise Master7MaterializationError("source header changed during layout check")
            if master_stream.readline() != master_identity.header:
                raise Master7MaterializationError("master header changed during layout check")
            remaining = source_identity.bytes - len(source_identity.header)
            while remaining:
                amount = min(COPY_BLOCK_BYTES, remaining)
                source_block = source_stream.read(amount)
                master_block = master_stream.read(amount)
                if len(source_block) != amount or master_block != source_block:
                    raise Master7MaterializationError(
                        "Master7 body is not byte-for-byte identical to F7"
                    )
                remaining -= amount
            if source_stream.read(1):
                raise Master7MaterializationError("unexpected source suffix")
            if master_stream.read() != extras:
                raise Master7MaterializationError(
                    "Master7 suffix is not the exact nine-clause payload"
                )


def verify_checked(
    directory: Path,
    source_identity: FormulaIdentity,
    master_identity: FormulaIdentity,
    extras: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    master = directory / master_identity.name
    partial = directory / f"{master_identity.name}{PARTIAL_SUFFIX}"
    if partial.exists():
        raise FileExistsError(f"refusing residual Master7 partial: {partial}")
    source_metadata = inspect_formula(source, source_identity)
    master_metadata = inspect_formula(master, master_identity)
    compare_exact_layout(source, master, source_identity, master_identity, extras)
    return {
        "status": "PASS_EXACT_MASTER7_LAYOUT",
        "source": source_metadata,
        "master": master_metadata,
        "body_reused_byte_for_byte": True,
        "exact_nine_clause_suffix": True,
    }


def preflight() -> dict[str, object]:
    if len(EXTRA_CLAUSES) != 9:
        raise Master7MaterializationError("Master7 normalization must have nine clauses")
    if EXTRA_PAYLOAD != (
        b"12 0\n"
        b"-14 0\n"
        b"14 -15 0\n"
        b"15 -16 0\n"
        b"16 -17 0\n"
        b"18 -19 0\n"
        b"19 -20 0\n"
        b"20 -21 0\n"
        b"13 18 0\n"
    ):
        raise Master7MaterializationError("Master7 suffix bytes changed")
    expected_master_bytes = (
        SOURCE_BYTES - len(SOURCE_HEADER) + len(MASTER_HEADER) + len(EXTRA_PAYLOAD)
    )
    if expected_master_bytes != MASTER_BYTES:
        raise Master7MaterializationError("Master7 byte arithmetic changed")
    if SOURCE_LINES + len(EXTRA_CLAUSES) != MASTER_LINES:
        raise Master7MaterializationError("Master7 line arithmetic changed")
    return {
        "status": "PASS",
        "source": _identity_dict(SOURCE_IDENTITY),
        "master": _identity_dict(MASTER_IDENTITY),
        "extra_clauses": [list(clause) for clause in EXTRA_CLAUSES],
        "extra_bytes": len(EXTRA_PAYLOAD),
        "path_policy": "generate/verify require an absolute S: directory",
        "overwrite_policy": "refuse existing target and residual .partial",
        "scope": "identity and layout materializer only; no SAT, LRAT, Lean, or Ramsey-bound claim",
    }


def generate(directory: Path) -> dict[str, object]:
    preflight()
    directory = require_ssd_directory(directory)
    return materialize_checked(
        directory,
        SOURCE_IDENTITY,
        MASTER_IDENTITY,
        EXTRA_PAYLOAD,
    )


def verify(directory: Path) -> dict[str, object]:
    preflight()
    directory = require_ssd_directory(directory)
    return verify_checked(
        directory,
        SOURCE_IDENTITY,
        MASTER_IDENTITY,
        EXTRA_PAYLOAD,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", default="preflight", choices=("preflight", "generate", "verify"))
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    else:
        if args.directory is None:
            parser.error("generate/verify require --directory")
        result = generate(args.directory) if args.command == "generate" else verify(args.directory)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
