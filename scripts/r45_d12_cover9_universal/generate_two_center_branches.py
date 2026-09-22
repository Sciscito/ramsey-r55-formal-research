#!/usr/bin/env python3
"""Restrict the block-conditioned d=8 target at a second centre."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

from . import generate_block_degree_branch as block_degree
from . import generate_degree_branch as degree_branch
from . import generate_universal as universal


SOURCE_MANIFEST = "block_degree_d8_manifest.json"
OUTPUT_DIRECTORY = "two_center_d8"
SUMMARY_NAME = "manifest.json"
CASES = tuple(
    (p, q)
    for p in range(4)
    for q in range(4)
    if p + q >= 2
)

# Frozen outputs of the deterministic generator. These values make the
# lightweight repository tests sensitive to accidental changes in the
# clause construction, while the SSD-side ``verify`` command recomputes every
# file hash and line count from the large artifacts themselves.
EXPECTED_CASE_RESULTS = {
    (0, 2): (782_090, 45_849_047, "135D6FBC93D564D8A8CC188B9F8CB051250EC0FEE4A84B2064C41056CDB3DBB0"),
    (0, 3): (796_308, 46_565_434, "C4D975965816FA0ED42D3C625550C5F60B209F3842B3F6584ED1721D206CC480"),
    (1, 1): (772_886, 45_401_795, "DB45053508935CD06BD044A63FAB7D84EBAF6E9EEECCDC6A610C4906AC463313"),
    (1, 2): (791_124, 46_277_854, "FC14EFDFCE9EC724AA20E59685879141FC2215816949E3F4A7B72AB2C9BCC4A2"),
    (1, 3): (809_859, 47_163_820, "E87F54E1B87155972321C22D79615AE94048C23342778E11DAE8DA15CA4F5AA0"),
    (2, 0): (758_924, 44_764_698, "D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315"),
    (2, 1): (778_667, 45_681_042, "9FAE831828CA81ADF06675B12EBE27402067D65E40B11B4FA66C6F49F7E97202"),
    (2, 2): (799_922, 46_675_347, "281D1F4BA3F3F36F2F9CFAD7D2D752332759F4A457C56F02900A08A94EA3DADE"),
    (2, 3): (823_149, 47_717_807, "0286CA13DD06852D0D02DDA6272AF023F2BB1B7623120E4E50506572DC12E4AB"),
    (3, 0): (761_533, 44_886_711, "F3B8FD5393B46114D9992B27AD5060F5D5C7A99CCE9C0CD17039CCAF366FD904"),
    (3, 1): (782_957, 45_880_826, "0FDB749F6022601BF94C766356FAB6216F81DFCE5708A97B9109D0FAAD6F8180"),
    (3, 2): (807_070, 46_975_647, "80B118D0B04425C0C7CD75C272A281DFD7A0CBDAA0A41308F37F6DD0AC3786FA"),
    (3, 3): (833_918, 48_129_797, "8BB2DC78C8B2CA427665A1356A8DF4EF34DDC34F1CA4653611A8DAD8ED381155"),
}

Clause = tuple[int, ...]


def second_assignment(p: int, q: int) -> dict[int, bool]:
    if (p, q) not in CASES:
        raise ValueError(f"unsupported two-centre case: {(p, q)}")
    assignment = {
        universal.edge_var(12, 1, vertex): vertex <= p + 1
        for vertex in range(2, 9)
    }
    assignment.update(
        {
            universal.edge_var(12, 1, vertex): vertex <= 8 + q
            for vertex in range(9, 12)
        }
    )
    return assignment


def canonical_simplification(
    clause: Sequence[int], assignment: dict[int, bool]
) -> Clause | None:
    simplified = degree_branch.simplify_clause(clause, assignment)
    if simplified is None:
        return None
    if not simplified:
        return ()
    result = tuple(sorted(simplified, key=lambda literal: (abs(literal), literal < 0)))
    if len(result) != len(set(result)) or any(-literal in result for literal in result):
        raise ValueError("malformed simplified clause")
    return result


def read_source_metadata(output: Path) -> tuple[Path, dict[str, object]]:
    block_degree.verify(output, 8)
    manifest = json.loads((output / SOURCE_MANIFEST).read_text(encoding="utf-8"))
    metadata = manifest["files"]["formula"]
    return output / metadata["name"], metadata


def simplified_clause_set(
    source: Path, assignment: dict[int, bool]
) -> tuple[set[Clause], dict[str, int]]:
    clauses: set[Clause] = set()
    parsed = 0
    satisfied = 0
    surviving = 0
    false_literals_removed = 0
    with source.open("rt", encoding="ascii", buffering=8 * 1024 * 1024) as stream:
        header = stream.readline().split()
        if header[:3] != ["p", "cnf", "66"] or len(header) != 4:
            raise ValueError("unexpected source DIMACS header")
        expected = int(header[3])
        for line_number, line in enumerate(stream, 2):
            values = tuple(map(int, line.split()))
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError(f"malformed DIMACS clause at line {line_number}")
            clause = values[:-1]
            parsed += 1
            simplified = canonical_simplification(clause, assignment)
            if simplified is None:
                satisfied += 1
                continue
            if not simplified:
                raise RuntimeError("two-centre assignment immediately yields an empty clause")
            surviving += 1
            false_literals_removed += len(clause) - len(simplified)
            clauses.add(simplified)
    if parsed != expected:
        raise ValueError(f"source clause count mismatch: {parsed} != {expected}")
    return clauses, {
        "source_clauses": parsed,
        "satisfied_clauses_removed": satisfied,
        "surviving_before_deduplication": surviving,
        "exact_duplicates_removed": surviving - len(clauses),
        "false_literals_removed": false_literals_removed,
    }


def write_formula(path: Path, clauses: Iterable[Clause], clause_count: int) -> dict[str, object]:
    digest = hashlib.sha256()
    size = 0
    written = 0
    with path.open("xb", buffering=8 * 1024 * 1024) as stream:
        header = f"p cnf 66 {clause_count}\n".encode("ascii")
        stream.write(header)
        digest.update(header)
        size += len(header)
        buffer: list[str] = []
        for clause in clauses:
            buffer.append(" ".join(map(str, clause)) + " 0\n")
            written += 1
            if len(buffer) == 8_192:
                data = "".join(buffer).encode("ascii")
                stream.write(data)
                digest.update(data)
                size += len(data)
                buffer.clear()
        if buffer:
            data = "".join(buffer).encode("ascii")
            stream.write(data)
            digest.update(data)
            size += len(data)
    if written != clause_count:
        raise RuntimeError(f"written clause mismatch: {written} != {clause_count}")
    return {
        "name": path.name,
        "bytes": size,
        "sha256": digest.hexdigest().upper(),
        "variables": 66,
        "clauses": written,
    }


def generate_case(source: Path, directory: Path, p: int, q: int) -> dict[str, object]:
    assignment = second_assignment(p, q)
    clauses, reduction = simplified_clause_set(source, assignment)
    name = f"cover9_d8_two_center_p{p}_q{q}.cnf"
    target = directory / name
    if target.exists():
        raise FileExistsError(f"refusing to replace two-centre formula: {target}")
    partial = directory / f"{name}.{os.getpid()}.partial"
    ordered = sorted(clauses)
    width_counts = Counter(map(len, ordered))
    try:
        formula = write_formula(partial, ordered, len(ordered))
        formula["name"] = name
        os.replace(partial, target)
    finally:
        if partial.exists():
            partial.unlink()
    return {
        "p": p,
        "q": q,
        "degree_of_second_center": 1 + p + q,
        "assignment": [
            variable if value else -variable for variable, value in assignment.items()
        ],
        "formula": formula,
        "reduction": reduction,
        "widths": dict(sorted(width_counts.items())),
    }


def generate(output: Path) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    source, source_metadata = read_source_metadata(output)
    directory = output / OUTPUT_DIRECTORY
    if directory.exists():
        raise FileExistsError(f"refusing existing two-centre directory: {directory}")
    directory.mkdir(parents=False)
    cases = []
    try:
        for index, (p, q) in enumerate(CASES, 1):
            row = generate_case(source, directory, p, q)
            cases.append(row)
            print(
                f"two-centre {index}/{len(CASES)} p={p} q={q}: "
                f"{row['formula']['clauses']} clauses, {row['formula']['bytes']} bytes",
                flush=True,
            )
        manifest = {
            "schema_version": 1,
            "status": "UNCERTIFIED_TWO_CENTER_CASE_SPLIT",
            "source": source_metadata,
            "cases": cases,
            "case_order": [list(case) for case in CASES],
            "case_cover_argument": {
                "root": "degree 8, neighbours 1..8, non-neighbours 9..11",
                "second_center": "vertex 1 is chosen inside the root-neighbour block",
                "p": "number of neighbours of vertex 1 among vertices 2..8",
                "q": "number of neighbours of vertex 1 among vertices 9..11",
                "bounds": (
                    "p<=3 because four common neighbours of adjacent 0,1 would "
                    "be pairwise nonadjacent and form an independent K4; q<=3 "
                    "by block size; p+q>=2 because deg(1)=1+p+q>=3"
                ),
                "permutation": (
                    "The stabilizer of the root prefix sends the chosen second "
                    "center to vertex 1 and sorts its neighbours independently "
                    "inside vertices 2..8 and 9..11."
                ),
            },
            "formal_bridge_status": "not yet formalized in Lean",
            "proof_status": "no solver proofs",
        }
        (directory / SUMMARY_NAME).write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        return manifest
    except Exception:
        # Preserve completed heavy cases for forensic inspection, but do not
        # publish a summary manifest for a partial run.
        raise


def verify(output: Path) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    directory = output / OUTPUT_DIRECTORY
    manifest = json.loads((directory / SUMMARY_NAME).read_text(encoding="utf-8"))
    if tuple(tuple(case) for case in manifest["case_order"]) != CASES:
        raise ValueError("two-centre case order mismatch")
    checked = []
    for row in manifest["cases"]:
        metadata = row["formula"]
        path = directory / metadata["name"]
        digest, size, lines = universal.sha256_file(path, count_lines=True)
        if digest != metadata["sha256"] or size != metadata["bytes"]:
            raise ValueError(f"two-centre hash/size mismatch: {path.name}")
        if lines != metadata["clauses"] + 1:
            raise ValueError(f"two-centre line count mismatch: {path.name}")
        expected = EXPECTED_CASE_RESULTS[(row["p"], row["q"])]
        observed = (metadata["clauses"], size, digest)
        if observed != expected:
            raise ValueError(
                f"two-centre frozen result mismatch for p={row['p']}, q={row['q']}: "
                f"{observed} != {expected}"
            )
        checked.append(
            {
                "p": row["p"],
                "q": row["q"],
                "clauses": metadata["clauses"],
                "bytes": size,
                "sha256": digest,
            }
        )
    return {"status": "PASS", "cases": checked}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("generate", "verify"))
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = generate(args.output) if args.command == "generate" else verify(args.output)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
