#!/usr/bin/env python3
"""Freeze an honest manifest for completed cover6 two-centre CNFs only."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from . import generate_complement_closed_cover6_branches as branches
from . import generate_complement_closed_cover6_two_center as two
from . import generate_universal as universal


PARTIAL_MANIFEST = "partial_manifest_checkpoint7.json"
FORMULA_PATTERN = re.compile(r"^cover6_closed_d(\d+)_two_center_p(\d+)_q(\d+)\.cnf$")


def parse_formula_name(name: str) -> tuple[int, int, int]:
    match = FORMULA_PATTERN.fullmatch(name)
    if match is None:
        raise ValueError(f"not a completed cover6 two-centre CNF: {name}")
    return tuple(map(int, match.groups()))  # type: ignore[return-value]


def inspect_formula(path: Path, degree: int, p: int, q: int) -> dict[str, object]:
    digest, size, lines = universal.sha256_file(path, count_lines=True)
    with path.open("rt", encoding="ascii") as stream:
        header = stream.readline().split()
    if header[:3] != ["p", "cnf", "66"] or len(header) != 4:
        raise ValueError(f"bad partial formula header: {path.name}")
    clauses = int(header[3])
    if lines != clauses + 1:
        raise ValueError(f"partial formula line count mismatch: {path.name}")
    row = {
        "degree": degree,
        "p": p,
        "q": q,
        "degree_of_second_center": 1 + p + q,
        "exact_unit_literals": list(two.unit_literals(degree, p, q)),
        "formula": {
            "name": path.name,
            "variables": 66,
            "clauses": clauses,
            "bytes": size,
            "sha256": digest,
        },
        "reduction_metrics": "not retained after intentionally interrupted batch",
    }
    two.verify_case(path, row)
    return row


def snapshot(output: Path, degree: int = 8) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    branches.verify(output, degree)
    directory = output / two.DIRECTORY_TEMPLATE.format(degree=degree)
    manifest_path = directory / PARTIAL_MANIFEST
    if manifest_path.exists():
        raise FileExistsError(f"refusing to replace partial manifest: {manifest_path}")
    rows = []
    for path in sorted(directory.glob("*.cnf")):
        parsed_degree, p, q = parse_formula_name(path.name)
        if parsed_degree != degree or (p, q) not in two.cases(degree):
            raise ValueError(f"out-of-scope completed formula: {path.name}")
        rows.append(inspect_formula(path, degree, p, q))
    observed = tuple((int(row["p"]), int(row["q"])) for row in rows)
    if len(observed) != len(set(observed)):
        raise ValueError("duplicate completed two-centre cases")
    requested = two.cases(degree)
    missing = tuple(case for case in requested if case not in observed)
    source_manifest = output / f"cover6_closed_block_degree_d{degree}_manifest.json"
    manifest = {
        "schema_version": 1,
        "status": "PARTIAL_EXPLORATORY_TWO_CENTER_CASE_SET",
        "warning": "This is not a complete case cover and proves no universal UNSAT result.",
        "degree": degree,
        "source_manifest": {
            "path": str(source_manifest),
            "sha256": universal.sha256_file(source_manifest)[0],
        },
        "requested_case_order": [list(case) for case in requested],
        "completed_case_order": [list(case) for case in observed],
        "missing_case_order": [list(case) for case in missing],
        "completed_cases": len(observed),
        "requested_cases": len(requested),
        "cases": rows,
        "proof_status": "no solver run yet",
        "formal_bridge_status": "not connected",
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return manifest


def verify(output: Path, degree: int = 8) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    directory = output / two.DIRECTORY_TEMPLATE.format(degree=degree)
    manifest_path = directory / PARTIAL_MANIFEST
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("status") != "PARTIAL_EXPLORATORY_TWO_CENTER_CASE_SET":
        raise ValueError("partial status changed")
    requested = two.cases(degree)
    completed = tuple(tuple(case) for case in manifest["completed_case_order"])
    missing = tuple(tuple(case) for case in manifest["missing_case_order"])
    if set(completed) & set(missing) or set(completed) | set(missing) != set(requested):
        raise ValueError("partial completed/missing partition mismatch")
    checked = []
    for row in manifest["cases"]:
        case = (int(row["p"]), int(row["q"]))
        if case not in completed:
            raise ValueError(f"unlisted partial row: {case}")
        checked.append(two.verify_case(directory / row["formula"]["name"], row))
    return {
        "status": "PASS_PARTIAL",
        "degree": degree,
        "completed_cases": len(completed),
        "requested_cases": len(requested),
        "missing_cases": [list(case) for case in missing],
        "checked": checked,
        "manifest_sha256": universal.sha256_file(manifest_path)[0],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("snapshot", "verify"))
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--degree", type=int, choices=two.DEGREES, default=8)
    args = parser.parse_args()
    result = snapshot(args.output, args.degree) if args.command == "snapshot" else verify(args.output, args.degree)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
