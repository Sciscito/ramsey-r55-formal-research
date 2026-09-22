#!/usr/bin/env python3
"""Build and verify one incremental F7 screen over the nine R(3,4) K7 types.

The base is the frozen degree-seven cover6 source F7. Its DIMACS header is
replaced by p inccnf and its clause body is copied byte-for-byte. Nine
assumption cubes then fix the 21 internal edges of the positive root
neighbourhood to the nine certified order-seven R(3,4) representatives.

The cover6 representative shared with that catalogue is deliberately first:
it is a cheap polarity oracle because its cube should be contradictory by
propagation. Generation and verification require an absolute S: directory,
never overwrite an existing target or partial, and invoke no SAT solver.
The default preflight reads only small tracked repository inputs.
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


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
R35_ORDER7 = REPOSITORY / "r55" / "r35_7.g6"
COVER6_TSV = (
    HERE.parent
    / "r45_d12_complement_closed_minimum"
    / "cover6_complement_closed.tsv"
)

SOURCE_NAME = "cover6_closed_block_degree_d7.cnf"
TARGET_NAME = "cover6_closed_f7_r34_catalogue9.inccnf"
PARTIAL_SUFFIX = ".partial"

SOURCE_HEADER = b"p cnf 66 4312419\n"
TARGET_HEADER = b"p inccnf\n"
SOURCE_BYTES = 246_507_515
SOURCE_SHA256 = "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C"
SOURCE_LINES = 4_312_420
SOURCE_CLAUSES = 4_312_419

R35_ORDER7_BYTES = 426
R35_ORDER7_LINES = 71
R35_ORDER7_SHA256 = (
    "DB838EEDFFE06069481E392FB6635C616A38A3C42BD130BA945B51B9B47A7AC2"
)
COVER6_TSV_SHA256 = (
    "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
)

TICK = chr(96)
ORACLE_RECORD = "FG" + TICK + "Xo"
SOURCE_R34_RECORDS = (
    "FCUj_",
    ORACLE_RECORD,
    "FK" + TICK + "Xo",
    "F_GZ_",
    "F" + TICK + "AZO",
    "F" + TICK + "GOW",
    "FoDPO",
    "FoDPW",
    "FqOxo",
)
ORDERED_R34_RECORDS = (ORACLE_RECORD,) + tuple(
    record for record in SOURCE_R34_RECORDS if record != ORACLE_RECORD
)
EXPECTED_DEGREE_SEQUENCES = (
    (1, 2, 2, 2, 3, 3, 3),
    (2, 2, 2, 3, 3, 3, 3),
    (2, 2, 2, 3, 3, 3, 3),
    (1, 2, 2, 2, 2, 2, 3),
    (2, 2, 2, 2, 2, 3, 3),
    (1, 1, 2, 2, 2, 2, 2),
    (2, 2, 2, 2, 2, 2, 2),
    (2, 2, 2, 2, 2, 3, 3),
    (2, 3, 3, 3, 3, 3, 3),
)

CUBE_COUNT = 9
CUBE_LITERALS = 21
CUBE_PAYLOAD_BYTES = 720
CUBE_PAYLOAD_SHA256 = (
    "78EC8EE01955937D451617A4F5D1D302E880A09F24A2582338A15C0D1496652C"
)
TARGET_BYTES = 246_508_227
TARGET_LINES = 4_312_429
TARGET_SHA256 = "CD4C3BB7D0850F75028346B6CD1AA4493D9FD837BFC595503D3E5DA750703180"

COPY_BLOCK_BYTES = 8 * 1024 * 1024


class R34CatalogueIcnfError(ValueError):
    """Raised at the first catalogue, identity, path, or layout mismatch."""


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


def file_metadata(path: Path) -> tuple[int, int, str]:
    digest = hashlib.sha256()
    size = 0
    lines = 0
    with path.open("rb", buffering=COPY_BLOCK_BYTES) as stream:
        for block in iter(lambda: stream.read(COPY_BLOCK_BYTES), b""):
            digest.update(block)
            size += len(block)
            lines += block.count(b"\n")
    return size, lines, digest.hexdigest().upper()


def graph6_mask(record: str) -> int:
    if len(record) != 5 or ord(record[0]) != 7 + 63:
        raise R34CatalogueIcnfError(f"not a short order-seven graph6 record: {record!r}")
    bits: list[int] = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise R34CatalogueIcnfError(f"invalid graph6 character in {record!r}")
        bits.extend((value >> shift) & 1 for shift in range(5, -1, -1))
    if any(bits[21:]):
        raise R34CatalogueIcnfError(f"nonzero graph6 padding in {record!r}")
    return sum(bit << position for position, bit in enumerate(bits[:21]))


def local_edge(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < 7:
        raise ValueError("not an edge of the local K7")
    return right * (right - 1) // 2 + left


def global_edge(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < 12:
        raise ValueError("not an edge of K12")
    return left * (23 - left) // 2 + right - left


def has_edge(mask: int, left: int, right: int) -> bool:
    return bool((mask >> local_edge(left, right)) & 1)


def degree_sequence(mask: int) -> tuple[int, ...]:
    return tuple(
        sorted(
            sum(has_edge(mask, vertex, other) for other in range(7) if other != vertex)
            for vertex in range(7)
        )
    )


def is_r34(mask: int) -> bool:
    no_triangle = all(
        not all(has_edge(mask, left, right) for left, right in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(7), 3)
    )
    no_independent_four = all(
        any(has_edge(mask, left, right) for left, right in itertools.combinations(vertices, 2))
        for vertices in itertools.combinations(range(7), 4)
    )
    return no_triangle and no_independent_four


def read_r34_records() -> tuple[str, ...]:
    size, lines, digest = file_metadata(R35_ORDER7)
    if (size, lines, digest) != (
        R35_ORDER7_BYTES,
        R35_ORDER7_LINES,
        R35_ORDER7_SHA256,
    ):
        raise R34CatalogueIcnfError("r35_7.g6 identity changed")
    records = tuple(
        line.strip()
        for line in R35_ORDER7.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    filtered = tuple(record for record in records if is_r34(graph6_mask(record)))
    if filtered != SOURCE_R34_RECORDS:
        raise R34CatalogueIcnfError(f"order-seven R34 filter changed: {filtered}")
    return (ORACLE_RECORD,) + tuple(
        record for record in filtered if record != ORACLE_RECORD
    )


def read_cover6_records() -> tuple[str, ...]:
    _size, _lines, digest = file_metadata(COVER6_TSV)
    if digest != COVER6_TSV_SHA256:
        raise R34CatalogueIcnfError("cover6 TSV identity changed")
    records = []
    for line_number, raw in enumerate(
        COVER6_TSV.read_text(encoding="ascii").splitlines(), 1
    ):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise R34CatalogueIcnfError(f"malformed cover6 row {line_number}")
        records.append(fields[1])
    return tuple(records)


H_VARIABLES = tuple(
    global_edge(left + 1, right + 1)
    for left, right in itertools.combinations(range(7), 2)
)


def cube_for_record(record: str) -> tuple[int, ...]:
    mask = graph6_mask(record)
    return tuple(
        variable if has_edge(mask, left, right) else -variable
        for variable, (left, right) in zip(
            H_VARIABLES, itertools.combinations(range(7), 2), strict=True
        )
    )


def cube_line(cube: Sequence[int]) -> bytes:
    if len(cube) != CUBE_LITERALS:
        raise R34CatalogueIcnfError("an R34 cube must assign all 21 K7 edges")
    if len({abs(literal) for literal in cube}) != CUBE_LITERALS:
        raise R34CatalogueIcnfError("an R34 cube repeats a variable")
    if any(not literal for literal in cube):
        raise R34CatalogueIcnfError("zero is not an assumption literal")
    return ("a " + " ".join(map(str, cube)) + " 0\n").encode("ascii")


def cube_payload(records: Sequence[str] = ORDERED_R34_RECORDS) -> bytes:
    return b"".join(cube_line(cube_for_record(record)) for record in records)


CUBE_PAYLOAD = cube_payload()


def audit_catalogue() -> dict[str, object]:
    records = read_r34_records()
    if records != ORDERED_R34_RECORDS or records[0] != ORACLE_RECORD:
        raise R34CatalogueIcnfError("R34 cube order changed")
    sequences = tuple(degree_sequence(graph6_mask(record)) for record in records)
    if sequences != EXPECTED_DEGREE_SEQUENCES:
        raise R34CatalogueIcnfError(f"R34 degree sequences changed: {sequences}")
    cover_intersection = tuple(record for record in records if record in read_cover6_records())
    if cover_intersection != (ORACLE_RECORD,):
        raise R34CatalogueIcnfError(
            f"cover6/R34 catalogue intersection changed: {cover_intersection}"
        )
    cubes = tuple(cube_for_record(record) for record in records)
    if len(cubes) != CUBE_COUNT or len(set(cubes)) != CUBE_COUNT:
        raise R34CatalogueIcnfError("R34 cubes are not nine distinct assignments")
    expected_variables = set(H_VARIABLES)
    for cube in cubes:
        if {abs(literal) for literal in cube} != expected_variables:
            raise R34CatalogueIcnfError("an R34 cube does not assign the exact K7 block")
    payload = b"".join(map(cube_line, cubes))
    if len(payload) != CUBE_PAYLOAD_BYTES:
        raise R34CatalogueIcnfError(
            f"R34 cube payload byte count changed: {len(payload)}"
        )
    if sha256_bytes(payload) != CUBE_PAYLOAD_SHA256:
        raise R34CatalogueIcnfError("R34 cube payload SHA-256 changed")
    return {
        "records": list(records),
        "degree_sequences": [list(sequence) for sequence in sequences],
        "cubes": [list(cube) for cube in cubes],
        "cube_lines": payload.decode("ascii").splitlines(),
        "cube_payload_bytes": len(payload),
        "cube_payload_sha256": sha256_bytes(payload),
        "oracle": {
            "record": ORACLE_RECORD,
            "position_one_based": 1,
            "exact_cover6_record": True,
        },
    }


def require_ssd_directory(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise R34CatalogueIcnfError(
            f"incremental F7 artifact directory must be an absolute S: path, got {path}"
        )
    return path


def inspect_stream(
    path: Path,
    identity: StreamIdentity,
    *,
    enforce_name: bool = True,
) -> dict[str, int | str]:
    if enforce_name and path.name != identity.name:
        raise R34CatalogueIcnfError(
            f"stream name mismatch: {path.name!r} != {identity.name!r}"
        )
    digest = hashlib.sha256()
    size = 0
    lines = 0
    with path.open("rb", buffering=COPY_BLOCK_BYTES) as stream:
        header = stream.readline()
        if header != identity.header:
            raise R34CatalogueIcnfError(
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
        raise R34CatalogueIcnfError(
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
    cubes: bytes,
) -> tuple[dict[str, int | str], dict[str, int | str]]:
    source_digest = hashlib.sha256()
    target_digest = hashlib.sha256()
    source_header = source.readline()
    if source_header != source_identity.header:
        raise R34CatalogueIcnfError("F7 header changed between validation and copy")
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
        raise R34CatalogueIcnfError(
            f"F7 changed during materialization: {observed_source} != {expected_source}"
        )
    target.write(cubes)
    target_digest.update(cubes)
    target_size += len(cubes)
    target_lines += cubes.count(b"\n")
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
        raise R34CatalogueIcnfError(
            f"incremental stream identity mismatch: {observed_target} != {expected_target}"
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
    cubes: bytes,
) -> None:
    with source.open("rb", buffering=COPY_BLOCK_BYTES) as source_stream:
        with target.open("rb", buffering=COPY_BLOCK_BYTES) as target_stream:
            if source_stream.readline() != source_identity.header:
                raise R34CatalogueIcnfError("F7 header changed during layout check")
            if target_stream.readline() != target_identity.header:
                raise R34CatalogueIcnfError("incremental header changed during layout check")
            remaining = source_identity.bytes - len(source_identity.header)
            while remaining:
                amount = min(COPY_BLOCK_BYTES, remaining)
                source_block = source_stream.read(amount)
                target_block = target_stream.read(amount)
                if len(source_block) != amount or target_block != source_block:
                    raise R34CatalogueIcnfError(
                        "incremental clause body is not byte-for-byte identical to F7"
                    )
                remaining -= amount
            if source_stream.read(1):
                raise R34CatalogueIcnfError("unexpected F7 suffix")
            if target_stream.read() != cubes:
                raise R34CatalogueIcnfError(
                    "incremental suffix is not the exact ordered R34 cube payload"
                )


def materialize_checked(
    directory: Path,
    source_identity: StreamIdentity,
    target_identity: StreamIdentity,
    cubes: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    target = directory / target_identity.name
    partial = directory / f"{target_identity.name}{PARTIAL_SUFFIX}"
    source_metadata = inspect_stream(source, source_identity)
    if target.exists():
        raise FileExistsError(f"refusing to overwrite incremental target: {target}")
    if partial.exists():
        raise FileExistsError(f"refusing residual incremental partial: {partial}")
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
                    cubes,
                )
        if copied_source != source_metadata:
            raise R34CatalogueIcnfError(
                "F7 metadata differs between validation and materialization"
            )
        inspect_stream(partial, target_identity, enforce_name=False)
        compare_exact_layout(
            source, partial, source_identity, target_identity, cubes
        )
        if target.exists():
            raise FileExistsError(f"incremental target appeared during generation: {target}")
        os.rename(partial, target)
        created_partial = False
    finally:
        if created_partial and partial.exists():
            partial.unlink()
    published = inspect_stream(target, target_identity)
    if published != target_metadata:
        raise R34CatalogueIcnfError("published incremental metadata changed")
    return {
        "status": "GENERATED_EXACT_F7_R34_CATALOGUE9_ICNF_WITHOUT_SOLVER",
        "source": source_metadata,
        "target": published,
        "body_reused_byte_for_byte": True,
        "cubes": CUBE_COUNT,
        "assumption_literals_per_cube": CUBE_LITERALS,
        "oracle_first": ORACLE_RECORD,
    }


def verify_checked(
    directory: Path,
    source_identity: StreamIdentity,
    target_identity: StreamIdentity,
    cubes: bytes,
) -> dict[str, object]:
    source = directory / source_identity.name
    target = directory / target_identity.name
    partial = directory / f"{target_identity.name}{PARTIAL_SUFFIX}"
    if partial.exists():
        raise FileExistsError(f"refusing residual incremental partial: {partial}")
    source_metadata = inspect_stream(source, source_identity)
    target_metadata = inspect_stream(target, target_identity)
    compare_exact_layout(source, target, source_identity, target_identity, cubes)
    return {
        "status": "PASS_EXACT_F7_R34_CATALOGUE9_ICNF_LAYOUT",
        "source": source_metadata,
        "target": target_metadata,
        "body_reused_byte_for_byte": True,
        "exact_ordered_cube_suffix": True,
    }


def preflight() -> dict[str, object]:
    catalogue = audit_catalogue()
    expected_target_bytes = (
        SOURCE_BYTES - len(SOURCE_HEADER) + len(TARGET_HEADER) + len(CUBE_PAYLOAD)
    )
    if expected_target_bytes != TARGET_BYTES:
        raise R34CatalogueIcnfError(
            f"target byte arithmetic changed: {expected_target_bytes}"
        )
    if 1 + SOURCE_CLAUSES + CUBE_COUNT != TARGET_LINES:
        raise R34CatalogueIcnfError("incremental line arithmetic changed")
    return {
        "status": "PASS",
        "source": {
            "name": SOURCE_NAME,
            "bytes": SOURCE_BYTES,
            "sha256": SOURCE_SHA256,
            "lines": SOURCE_LINES,
            "clauses": SOURCE_CLAUSES,
        },
        "target": {
            "name": TARGET_NAME,
            "bytes": TARGET_BYTES,
            "sha256": TARGET_SHA256,
            "lines": TARGET_LINES,
            "header": TARGET_HEADER.decode("ascii").rstrip("\n"),
        },
        "catalogue": catalogue,
        "path_policy": "generate/verify require an absolute S: directory",
        "overwrite_policy": "refuse existing target and residual .partial",
        "solver_policy": "this program never invokes a SAT solver",
        "scope": (
            "exact incremental source construction only; no SAT, UNSAT, proof, "
            "Lean composition, cover6-d7 theorem, or Ramsey-number claim"
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
    """Reconstruct both hashes from tracked primitives without reading S:."""

    preflight()
    blocks = source_audit.block_catalogues()
    locals_ = source_audit.local_catalogues()
    compiled_blocks = tuple(
        tuple(source_audit.compiled_cube(cube, source_audit.LOCAL_EDGES) for cube in catalogue)
        for catalogue in blocks
    )
    compiled_locals = tuple(
        tuple(source_audit.compiled_cube(cube, 15) for cube in catalogue)
        for catalogue in locals_
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
        raise R34CatalogueIcnfError(
            f"primitive F7 reconstruction changed: {(written, source_size, source_hash)}"
        )
    target_digest.update(CUBE_PAYLOAD)
    target_size += len(CUBE_PAYLOAD)
    target_hash = target_digest.hexdigest().upper()
    if target_size != TARGET_BYTES:
        raise R34CatalogueIcnfError("primitive incremental byte count changed")
    if target_hash != TARGET_SHA256:
        raise R34CatalogueIcnfError(
            f"primitive incremental SHA-256 changed: {target_hash}"
        )
    return {
        "status": "PASS",
        "mode": "local primitive reconstruction; no S: read, no write, no solver",
        "source": {
            "clauses": written,
            "bytes": source_size,
            "sha256": source_hash,
        },
        "target": {
            "bytes": target_size,
            "sha256": target_hash,
            "lines": TARGET_LINES,
        },
    }


def generate(directory: Path) -> dict[str, object]:
    preflight()
    directory = require_ssd_directory(directory)
    return materialize_checked(
        directory,
        SOURCE_IDENTITY,
        TARGET_IDENTITY,
        CUBE_PAYLOAD,
    )


def verify(directory: Path) -> dict[str, object]:
    preflight()
    directory = require_ssd_directory(directory)
    return verify_checked(
        directory,
        SOURCE_IDENTITY,
        TARGET_IDENTITY,
        CUBE_PAYLOAD,
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
