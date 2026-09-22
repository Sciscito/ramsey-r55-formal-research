#!/usr/bin/env python3
"""Add a sound root-neighbour prefix symmetry break to the universal CNF."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path

from . import generate_universal as universal


PREFIX_CLAUSES = tuple((index, -(index + 1)) for index in range(1, 11))
PREFIX_NAME = "cover9_universal_root_prefix.cnf"
MANIFEST_NAME = "prefix_manifest.json"
EXPECTED_SHA256: str | None = "6BD6355400C03874532539D69A49A6FE11AECA11E3C1FB0E8EB6FAC8422A1D3A"
EXPECTED_BYTES: int | None = 701_106_211


def hash_copy(source, target, digest: "hashlib._Hash") -> int:
    count = 0
    for block in iter(lambda: source.read(8 * 1024 * 1024), b""):
        target.write(block)
        digest.update(block)
        count += len(block)
    return count


def generate(output: Path) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    universal.verify(output)
    base_manifest = json.loads((output / "manifest.json").read_text(encoding="utf-8"))
    source_metadata = base_manifest["files"]["formula"]
    source_path = output / source_metadata["name"]
    target_path = output / PREFIX_NAME
    manifest_path = output / MANIFEST_NAME
    for path in (target_path, manifest_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace symmetry artifact: {path}")

    clause_count = int(source_metadata["clauses"]) + len(PREFIX_CLAUSES)
    partial = output / f"{PREFIX_NAME}.{os.getpid()}.partial"
    digest = hashlib.sha256()
    byte_count = 0
    try:
        with source_path.open("rb") as source, partial.open("xb", buffering=8 * 1024 * 1024) as target:
            source_header = source.readline()
            expected_source_header = (
                f"p cnf {source_metadata['variables']} {source_metadata['clauses']}\n".encode("ascii")
            )
            if source_header != expected_source_header:
                raise ValueError("source header mismatch")
            header = f"p cnf {source_metadata['variables']} {clause_count}\n".encode("ascii")
            target.write(header)
            digest.update(header)
            byte_count += len(header)
            byte_count += hash_copy(source, target, digest)
            suffix = "".join(
                " ".join(map(str, clause)) + " 0\n" for clause in PREFIX_CLAUSES
            ).encode("ascii")
            target.write(suffix)
            digest.update(suffix)
            byte_count += len(suffix)
        os.replace(partial, target_path)
    finally:
        if partial.exists():
            partial.unlink()

    formula = {
        "name": PREFIX_NAME,
        "bytes": byte_count,
        "sha256": digest.hexdigest().upper(),
        "variables": int(source_metadata["variables"]),
        "clauses": clause_count,
    }
    manifest = {
        "schema_version": 1,
        "status": "UNCERTIFIED_EQUISAT_SYMMETRY_TARGET",
        "files": {"formula": formula},
        "source_formula": source_metadata,
        "added_clauses": [list(clause) for clause in PREFIX_CLAUSES],
        "meaning": (
            "For root 0, x(0,i+1) implies x(0,i), so its neighbours form "
            "an initial segment of vertices 1..11."
        ),
        "equisatisfiability_argument": (
            "The source formula is invariant under all vertex permutations. "
            "Every source model can permute vertices 1..11 so the neighbours "
            "of vertex 0 precede its non-neighbours. The converse is inclusion."
        ),
        "formal_bridge_status": "not yet formalized in Lean",
        "proof_status": "no solver proof",
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return manifest


def verify(output: Path) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    universal.verify(output)
    manifest = json.loads((output / MANIFEST_NAME).read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported prefix manifest")
    metadata = manifest["files"]["formula"]
    path = output / metadata["name"]
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    if digest != metadata["sha256"] or size != metadata["bytes"]:
        raise ValueError("prefix formula hash or size mismatch")
    if lines != metadata["clauses"] + 1:
        raise ValueError("prefix formula line count mismatch")
    expected_suffix = "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in PREFIX_CLAUSES
    ).encode("ascii")
    with path.open("rb") as stream:
        stream.seek(-len(expected_suffix), 2)
        if stream.read() != expected_suffix:
            raise ValueError("prefix clauses differ")
    if EXPECTED_SHA256 is not None and digest != EXPECTED_SHA256:
        raise ValueError("prefix formula differs from frozen SHA-256")
    if EXPECTED_BYTES is not None and size != EXPECTED_BYTES:
        raise ValueError("prefix formula differs from frozen byte count")
    return {"status": "PASS", "sha256": digest, "bytes": size, "lines": lines}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("generate", "verify"))
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = generate(args.output) if args.command == "generate" else verify(args.output)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
