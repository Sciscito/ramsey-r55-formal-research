#!/usr/bin/env python3
"""Split cover6 degree branches at a second centre with exact unit clauses.

For a root of degree d in {6,7,8}, vertices 1..d are its canonical
neighbours and vertex 1 is the second centre.  ``p`` counts its neighbours in
2..d and ``q`` those in d+1..11.  Every emitted DIMACS file contains all 21
root/second-centre unit clauses, not merely an external assumption list.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

from . import generate_complement_closed_cover6_branches as branches
from . import generate_degree_branch as degree_branch
from . import generate_universal as universal


DEGREES = (6, 7, 8)
CASE_COUNTS = {6: 20, 7: 17, 8: 13}
DIRECTORY_TEMPLATE = "cover6_closed_two_center_d{degree}"
SUMMARY_NAME = "manifest.json"
VARIABLE_COUNT = 66

# Filled after deterministic SSD generation and an independent replay.
EXPECTED_CASE_RESULTS: dict[int, dict[tuple[int, int], tuple[int, int, str]]] = {
    6: {},
    7: {},
    8: {},
}


def cases(degree: int) -> tuple[tuple[int, int], ...]:
    if degree not in DEGREES:
        raise ValueError(f"degree must be one of {DEGREES}")
    result = tuple(
        (p, q)
        for p in range(4)
        for q in range(12 - degree)
        if 2 <= p + q <= 7
    )
    if len(result) != CASE_COUNTS[degree]:
        raise RuntimeError(f"two-centre case count changed for d={degree}: {len(result)}")
    return result


def root_assignment(degree: int) -> dict[int, bool]:
    if degree not in DEGREES:
        raise ValueError(f"degree must be one of {DEGREES}")
    return {
        universal.edge_var(12, 0, vertex): vertex <= degree
        for vertex in range(1, 12)
    }


def second_assignment(degree: int, p: int, q: int) -> dict[int, bool]:
    if (p, q) not in cases(degree):
        raise ValueError(f"unsupported d={degree} two-centre case: {(p, q)}")
    assignment = {
        universal.edge_var(12, 1, vertex): vertex <= p + 1
        for vertex in range(2, degree + 1)
    }
    assignment.update({
        universal.edge_var(12, 1, vertex): vertex <= degree + q
        for vertex in range(degree + 1, 12)
    })
    if len(assignment) != 10:
        raise RuntimeError("second-centre assignment must fix exactly ten edges")
    return assignment


def exact_assignment(degree: int, p: int, q: int) -> dict[int, bool]:
    result = root_assignment(degree)
    second = second_assignment(degree, p, q)
    overlap = set(result) & set(second)
    if overlap:
        raise RuntimeError(f"root/second assignments unexpectedly overlap: {overlap}")
    result.update(second)
    if set(result) != set(range(1, 22)):
        raise RuntimeError("two-centre units are not exactly DIMACS variables 1..21")
    return result


def unit_literals(degree: int, p: int, q: int) -> tuple[int, ...]:
    assignment = exact_assignment(degree, p, q)
    return tuple(variable if assignment[variable] else -variable for variable in sorted(assignment))


def encode_clause(literals: Iterable[int]) -> int:
    positive = 0
    negative = 0
    for literal in literals:
        variable = abs(literal)
        if not 1 <= variable <= VARIABLE_COUNT:
            raise ValueError(f"literal out of range: {literal}")
        bit = 1 << (variable - 1)
        if literal > 0:
            if positive & bit:
                raise ValueError(f"duplicate literal: {literal}")
            if negative & bit:
                raise ValueError(f"tautological variable: {variable}")
            positive |= bit
        else:
            if negative & bit:
                raise ValueError(f"duplicate literal: {literal}")
            if positive & bit:
                raise ValueError(f"tautological variable: {variable}")
            negative |= bit
    return positive | (negative << VARIABLE_COUNT)


def decode_clause(key: int) -> tuple[int, ...]:
    positive = key & ((1 << VARIABLE_COUNT) - 1)
    negative = key >> VARIABLE_COUNT
    if positive & negative:
        raise ValueError("encoded tautological clause")
    result = []
    for variable in range(1, VARIABLE_COUNT + 1):
        bit = 1 << (variable - 1)
        if positive & bit:
            result.append(variable)
        elif negative & bit:
            result.append(-variable)
    return tuple(result)


def simplify_clause(clause: Sequence[int], assignment: dict[int, bool]) -> int | None:
    remaining = []
    for literal in clause:
        value = assignment.get(abs(literal))
        if value is None:
            remaining.append(literal)
        elif value == (literal > 0):
            return None
    return encode_clause(remaining)


def source_metadata(output: Path, degree: int) -> tuple[Path, dict[str, object]]:
    branches.verify(output, degree)
    manifest_path = output / f"cover6_closed_block_degree_d{degree}_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    metadata = manifest["files"]["formula"]
    return output / metadata["name"], metadata


def reduce_source(source: Path, degree: int, p: int, q: int) -> tuple[set[int], dict[str, int]]:
    second = second_assignment(degree, p, q)
    exact = exact_assignment(degree, p, q)
    root_variables = set(root_assignment(degree))
    keys: set[int] = set()
    parsed = 0
    satisfied = 0
    surviving = 0
    false_literals_removed = 0
    with source.open("rt", encoding="ascii", buffering=8 * 1024 * 1024) as stream:
        header = stream.readline().split()
        if header[:3] != ["p", "cnf", str(VARIABLE_COUNT)] or len(header) != 4:
            raise ValueError("unexpected cover6 source DIMACS header")
        expected = int(header[3])
        for line_number, line in enumerate(stream, 2):
            values = tuple(map(int, line.split()))
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError(f"malformed source clause at line {line_number}")
            clause = values[:-1]
            if any(abs(literal) in root_variables for literal in clause):
                raise ValueError(f"residual degree formula mentions a root variable at line {line_number}")
            parsed += 1
            reduced = simplify_clause(clause, second)
            if reduced is None:
                satisfied += 1
                continue
            surviving += 1
            false_literals_removed += sum(abs(literal) in second for literal in clause)
            keys.add(reduced)
    if parsed != expected:
        raise ValueError(f"source clause count mismatch: {parsed} != {expected}")
    residual_unique = len(keys)
    unit_keys = {encode_clause((literal,)) for literal in unit_literals(degree, p, q)}
    if keys & unit_keys:
        raise RuntimeError("residual formula unexpectedly duplicates an exact unit")
    keys.update(unit_keys)
    if len(unit_keys) != 21 or len(exact) != 21:
        raise RuntimeError("exact unit count changed")
    return keys, {
        "source_clauses": parsed,
        "satisfied_clauses_removed": satisfied,
        "surviving_before_deduplication": surviving,
        "residual_exact_duplicates_removed": surviving - residual_unique,
        "false_second_center_literals_removed": false_literals_removed,
        "unique_residual_clauses": residual_unique,
        "exact_unit_clauses_added": len(unit_keys),
        "output_clauses": len(keys),
    }


def write_formula(path: Path, keys: set[int]) -> dict[str, object]:
    digest = hashlib.sha256()
    size = 0
    written = 0
    with path.open("xb", buffering=8 * 1024 * 1024) as stream:
        header = f"p cnf {VARIABLE_COUNT} {len(keys)}\n".encode("ascii")
        stream.write(header)
        digest.update(header)
        size += len(header)
        buffer: list[str] = []
        for key in sorted(keys):
            clause = decode_clause(key)
            buffer.append(" ".join(map(str, clause)) + (" " if clause else "") + "0\n")
            written += 1
            if len(buffer) == 8_192:
                block = "".join(buffer).encode("ascii")
                stream.write(block)
                digest.update(block)
                size += len(block)
                buffer.clear()
        if buffer:
            block = "".join(buffer).encode("ascii")
            stream.write(block)
            digest.update(block)
            size += len(block)
    if written != len(keys):
        raise RuntimeError("two-centre writer count mismatch")
    return {
        "name": path.name,
        "variables": VARIABLE_COUNT,
        "clauses": written,
        "bytes": size,
        "sha256": digest.hexdigest().upper(),
    }


def generate_case(source: Path, directory: Path, degree: int, p: int, q: int) -> dict[str, object]:
    keys, reduction = reduce_source(source, degree, p, q)
    name = f"cover6_closed_d{degree}_two_center_p{p}_q{q}.cnf"
    target = directory / name
    if target.exists():
        raise FileExistsError(f"refusing to replace two-centre formula: {target}")
    partial = directory / f"{name}.{os.getpid()}.partial"
    widths = Counter(len(decode_clause(key)) for key in keys)
    try:
        formula = write_formula(partial, keys)
        formula["name"] = name
        os.replace(partial, target)
    finally:
        if partial.exists():
            partial.unlink()
    return {
        "degree": degree,
        "p": p,
        "q": q,
        "degree_of_second_center": 1 + p + q,
        "exact_unit_literals": list(unit_literals(degree, p, q)),
        "formula": formula,
        "reduction": reduction,
        "widths": dict(sorted(widths.items())),
    }


def generate(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    source, source_info = source_metadata(output, degree)
    directory = output / DIRECTORY_TEMPLATE.format(degree=degree)
    if directory.exists():
        raise FileExistsError(f"refusing existing two-centre directory: {directory}")
    directory.mkdir(parents=False)
    rows = []
    for index, (p, q) in enumerate(cases(degree), 1):
        row = generate_case(source, directory, degree, p, q)
        rows.append(row)
        metadata = row["formula"]
        print(
            f"cover6 d={degree} case {index}/{len(cases(degree))} p={p} q={q}: "
            f"{metadata['clauses']} clauses, {metadata['bytes']} bytes",
            flush=True,
        )
    manifest = {
        "schema_version": 1,
        "status": "UNCERTIFIED_EXACT_TWO_CENTER_CASE_SPLIT",
        "source": source_info,
        "degree": degree,
        "case_order": [list(case) for case in cases(degree)],
        "cases": rows,
        "case_cover_argument": {
            "root": f"degree {degree}, neighbours 1..{degree}, non-neighbours {degree + 1}..11",
            "second_center": "vertex 1 inside the root-neighbour block",
            "p": f"neighbours of vertex 1 among 2..{degree}",
            "q": f"neighbours of vertex 1 among {degree + 1}..11",
            "bounds": "p<=3; 2<=p+q<=7 from 3<=deg(1)=1+p+q<=8",
            "units": "all root and second-centre edges occur as 21 explicit unit clauses",
        },
        "formal_bridge_status": "case arithmetic and units are executable; Lean transport not yet connected",
        "proof_status": "no solver proof",
    }
    (directory / SUMMARY_NAME).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return manifest


def verify_case(path: Path, row: dict[str, object]) -> dict[str, object]:
    metadata = row["formula"]
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    if (digest, size, lines) != (
        metadata["sha256"], metadata["bytes"], metadata["clauses"] + 1
    ):
        raise ValueError(f"two-centre hash, size, or line count mismatch: {path.name}")
    expected_units = set(row["exact_unit_literals"])
    assigned_variables = {abs(literal) for literal in expected_units}
    found_units: set[int] = set()
    parsed = 0
    with path.open("rt", encoding="ascii", buffering=8 * 1024 * 1024) as stream:
        if stream.readline().rstrip("\r\n") != f"p cnf {VARIABLE_COUNT} {metadata['clauses']}":
            raise ValueError(f"two-centre header mismatch: {path.name}")
        for line_number, line in enumerate(stream, 2):
            values = tuple(map(int, line.split()))
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError(f"malformed two-centre clause at line {line_number}")
            clause = values[:-1]
            assigned_here = [literal for literal in clause if abs(literal) in assigned_variables]
            if assigned_here:
                if len(clause) != 1 or clause[0] not in expected_units:
                    raise ValueError(f"assigned variable survives outside its exact unit at line {line_number}")
                found_units.add(clause[0])
            parsed += 1
    if parsed != metadata["clauses"] or found_units != expected_units:
        raise ValueError(f"two-centre exact unit verification failed: {path.name}")
    return {"clauses": parsed, "bytes": size, "sha256": digest, "exact_units": len(found_units)}


def verify(output: Path, degree: int) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    directory = output / DIRECTORY_TEMPLATE.format(degree=degree)
    manifest = json.loads((directory / SUMMARY_NAME).read_text(encoding="utf-8"))
    if manifest.get("degree") != degree:
        raise ValueError("two-centre manifest degree mismatch")
    if tuple(tuple(case) for case in manifest.get("case_order", ())) != cases(degree):
        raise ValueError("two-centre case order mismatch")
    if len(manifest.get("cases", ())) != CASE_COUNTS[degree]:
        raise ValueError("two-centre row count mismatch")
    checked = []
    frozen = EXPECTED_CASE_RESULTS[degree]
    for row in manifest["cases"]:
        case = (int(row["p"]), int(row["q"]))
        if case not in cases(degree):
            raise ValueError(f"unexpected two-centre case: {case}")
        expected_units = unit_literals(degree, *case)
        if tuple(row["exact_unit_literals"]) != expected_units:
            raise ValueError(f"two-centre manifest units changed: {case}")
        result = verify_case(directory / row["formula"]["name"], row)
        if case in frozen:
            observed = (result["clauses"], result["bytes"], result["sha256"])
            if observed != frozen[case]:
                raise ValueError(f"frozen two-centre artifact changed for {case}: {observed}")
        checked.append({"p": case[0], "q": case[1], **result, "frozen": case in frozen})
    return {"status": "PASS", "degree": degree, "cases": checked}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("generate", "verify", "cases"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--degree", type=int, required=True, choices=DEGREES)
    args = parser.parse_args()
    if args.command == "cases":
        result = {
            "degree": args.degree,
            "cases": [list(case) for case in cases(args.degree)],
            "unit_literals": {
                f"p{p}_q{q}": list(unit_literals(args.degree, p, q))
                for p, q in cases(args.degree)
            },
        }
    else:
        if args.output is None:
            parser.error("generate/verify require --output")
        result = generate(args.output, args.degree) if args.command == "generate" else verify(args.output, args.degree)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
