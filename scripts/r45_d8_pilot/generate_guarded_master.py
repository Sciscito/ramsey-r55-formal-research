#!/usr/bin/env python3
"""Build the compact guarded master CNF for the 54 degree-eight leaves.

The formula contains the common 55,006-clause fixed-root core once.  Five
little-endian selector bits choose one of the 27 ``gen358`` parents and one
selector bit chooses one of the two ``gen4416`` targets.  Every catalogue
unit is guarded by the negation of its selector code; the five unused left
codes 27,...,31 are explicitly forbidden.

This program never invokes a SAT solver.  Its central audit specializes the
master formula under each of the 54 valid selector cubes and checks exact
clause equality, then byte-for-byte DIMACS SHA-256 equality, with the direct
leaf formula whose hash is recorded in ``results_c1000000.csv``.

The generated master is an uncertified proof target.  In particular, this
script does not claim that LRAT traces exist for the other 53 leaves.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
DIRECT_PILOT_PATH = HERE / "run_direct_pilot.py"
DEFAULT_OUTPUT = HERE / "guarded_master"
RESULTS_CSV = HERE / "evidence" / "results_c1000000.csv"
HARD_LEAF_RESULT = HERE / "evidence" / "result_d8_l10_r01_c5000000.json"
LRAT_EVIDENCE = HERE / "evidence" / "lrat"

EDGE_VARIABLE_COUNT = 276
BASE_CLAUSE_COUNT = 55_006
LEFT_SELECTOR_VARIABLES = tuple(range(277, 282))
RIGHT_SELECTOR_VARIABLES = (282,)
SELECTOR_VARIABLES = LEFT_SELECTOR_VARIABLES + RIGHT_SELECTOR_VARIABLES
MASTER_VARIABLE_COUNT = 282
LEFT_RECORD_COUNT = 27
RIGHT_RECORD_COUNT = 2
INVALID_LEFT_CODES = tuple(range(LEFT_RECORD_COUNT, 1 << len(LEFT_SELECTOR_VARIABLES)))
EXPECTED_MASTER_CLAUSE_COUNT = 55_926

Clause = tuple[int, ...]


def load_direct_pilot():
    spec = importlib.util.spec_from_file_location(
        "r45_d8_direct_pilot_for_guarded_master", DIRECT_PILOT_PATH
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {DIRECT_PILOT_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


pilot = load_direct_pilot()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def dimacs_bytes(variable_count: int, clauses: Sequence[Clause]) -> bytes:
    validate_clauses(variable_count, clauses)
    lines = [f"p cnf {variable_count} {len(clauses)}\n"]
    lines.extend(" ".join(map(str, clause)) + " 0\n" for clause in clauses)
    return "".join(lines).encode("ascii")


def validate_clauses(variable_count: int, clauses: Sequence[Clause]) -> None:
    for clause_index, clause in enumerate(clauses):
        if not clause:
            raise RuntimeError(f"empty clause at index {clause_index}")
        if any(literal == 0 or abs(literal) > variable_count for literal in clause):
            raise RuntimeError(f"invalid literal in clause {clause_index}: {clause}")
        if len(set(clause)) != len(clause):
            raise RuntimeError(f"duplicate literal in clause {clause_index}: {clause}")
        if any(-literal in clause for literal in clause):
            raise RuntimeError(f"tautological clause at index {clause_index}: {clause}")


def selector_cube(code: int, variables: Sequence[int]) -> Clause:
    if not 0 <= code < 1 << len(variables):
        raise ValueError(f"selector code {code} does not fit in {len(variables)} bits")
    return tuple(
        variable if (code >> bit_index) & 1 else -variable
        for bit_index, variable in enumerate(variables)
    )


def selector_guard(code: int, variables: Sequence[int]) -> Clause:
    """Clause false exactly on the selected little-endian binary code."""
    return tuple(-literal for literal in selector_cube(code, variables))


def icnf_bytes(cubes: Sequence[Clause]) -> bytes:
    """Strict Cover.parseICnf-compatible representation, in proof order."""
    return "".join(
        "a " + " ".join(map(str, cube)) + " 0\n" for cube in cubes
    ).encode("ascii")


def parse_icnf_bytes(data: bytes) -> tuple[Clause, ...]:
    """Strict subset of Cover.parseICnf used to audit generated iCNF."""
    cubes: list[Clause] = []
    for line_number, raw_line in enumerate(data.decode("ascii").splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("c") or line.startswith("p"):
            continue
        tokens = line.split()
        if tokens[0] != "a":
            raise RuntimeError(f"iCNF line {line_number} does not start with 'a'")
        try:
            values = [int(token) for token in tokens[1:]]
        except ValueError as exc:
            raise RuntimeError(f"non-integer iCNF token on line {line_number}") from exc
        if not values or values[-1] != 0 or values.count(0) != 1:
            raise RuntimeError(f"invalid iCNF terminator on line {line_number}")
        cubes.append(tuple(values[:-1]))
    return tuple(cubes)


def cube_matches_assignment(cube: Sequence[int], assignment: dict[int, bool]) -> bool:
    return all(
        abs(literal) in assignment
        and assignment[abs(literal)] == (literal > 0)
        for literal in cube
    )


def negated_cube_clauses(cubes: Sequence[Clause]) -> tuple[Clause, ...]:
    """DIMACS image of Cover.negCubesCNF in exactly the iCNF order."""
    return tuple(tuple(-literal for literal in cube) for cube in cubes)

def specialize_selectors(clauses: Sequence[Clause], cube: Sequence[int]) -> tuple[Clause, ...]:
    """Restrict ``clauses`` by a complete selector cube and remove selectors."""
    assignment: dict[int, bool] = {}
    for literal in cube:
        variable = abs(literal)
        if variable not in SELECTOR_VARIABLES:
            raise RuntimeError(f"cube literal {literal} is not a selector")
        value = literal > 0
        if variable in assignment and assignment[variable] != value:
            raise RuntimeError(f"contradictory cube on selector {variable}")
        assignment[variable] = value
    if set(assignment) != set(SELECTOR_VARIABLES):
        raise RuntimeError("selector cube is incomplete")

    restricted: list[Clause] = []
    for clause in clauses:
        satisfied = any(
            abs(literal) in assignment
            and assignment[abs(literal)] == (literal > 0)
            for literal in clause
        )
        if satisfied:
            continue
        reduced = tuple(
            literal for literal in clause if abs(literal) not in assignment
        )
        if not reduced:
            raise RuntimeError("valid selector cube falsifies a master clause")
        restricted.append(reduced)
    return tuple(restricted)


def read_leaf_evidence() -> dict[str, dict[str, str]]:
    with RESULTS_CSV.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != LEFT_RECORD_COUNT * RIGHT_RECORD_COUNT:
        raise RuntimeError(f"expected 54 evidence rows, found {len(rows)}")
    evidence = {
        row["leaf"]: {
            "status": row["status"],
            "leaf_cnf_sha256": row["leaf_cnf_sha256"].upper(),
            "source": RESULTS_CSV.name,
        }
        for row in rows
    }
    if len(evidence) != len(rows):
        raise RuntimeError("duplicate leaf in evidence CSV")

    hard = json.loads(HARD_LEAF_RESULT.read_text(encoding="utf-8"))["leaf_run"]
    leaf_name = hard["leaf"]
    if evidence[leaf_name]["leaf_cnf_sha256"] != hard["leaf_cnf_sha256"].upper():
        raise RuntimeError(f"hard-leaf hash disagreement for {leaf_name}")
    evidence[leaf_name] = {
        "status": hard["status"],
        "leaf_cnf_sha256": hard["leaf_cnf_sha256"].upper(),
        "source": HARD_LEAF_RESULT.name,
    }
    return evidence


@lru_cache(maxsize=1)
def build_result() -> dict:
    base_clauses = tuple(pilot.direct_clauses())
    if len(base_clauses) != BASE_CLAUSE_COUNT:
        raise RuntimeError(
            f"base clause count changed: {len(base_clauses)} != {BASE_CLAUSE_COUNT}"
        )
    if Counter(base_clauses) != Counter(pilot.simplify_full_direct()):
        raise RuntimeError("fixed-root reduction audit failed")

    left_records = list(pilot.helper.iter_records(pilot.helper.GEN35, 8))
    right_records = list(pilot.helper.iter_records(pilot.helper.GEN44, 16))
    if (len(left_records), len(right_records)) != (LEFT_RECORD_COUNT, RIGHT_RECORD_COUNT):
        raise RuntimeError("catalogue record count is not 27 x 2")

    left_units: list[tuple[int, ...]] = []
    for expected_index, (index, _parent_id, edges, _children) in enumerate(left_records):
        if index != expected_index:
            raise RuntimeError("gen358 record indices are not contiguous")
        units = tuple(pilot.direct_block_literals(edges, 8, 0))
        if len(set(map(abs, units))) != len(units):
            raise RuntimeError(f"duplicate gen358 unit variable at parent {index}")
        left_units.append(units)

    right_units: list[tuple[int, ...]] = []
    for expected_index, (index, _target_id, edges, _children) in enumerate(right_records):
        if index != expected_index:
            raise RuntimeError("gen4416 record indices are not contiguous")
        units = tuple(pilot.direct_block_literals(edges, 16, 8))
        if len(units) != 120 or len(set(map(abs, units))) != 120:
            raise RuntimeError(f"gen4416 target {index} is not a complete 120-edge cube")
        right_units.append(units)

    guarded_left = tuple(
        selector_guard(index, LEFT_SELECTOR_VARIABLES) + (unit,)
        for index, units in enumerate(left_units)
        for unit in units
    )
    guarded_right = tuple(
        selector_guard(index, RIGHT_SELECTOR_VARIABLES) + (unit,)
        for index, units in enumerate(right_units)
        for unit in units
    )
    invalid_left = tuple(
        selector_guard(code, LEFT_SELECTOR_VARIABLES) for code in INVALID_LEFT_CODES
    )
    master_clauses = base_clauses + guarded_left + guarded_right + invalid_left
    if len(master_clauses) != EXPECTED_MASTER_CLAUSE_COUNT:
        raise RuntimeError(
            f"master clause count changed: {len(master_clauses)} != "
            f"{EXPECTED_MASTER_CLAUSE_COUNT}"
        )
    validate_clauses(MASTER_VARIABLE_COUNT, master_clauses)

    evidence = read_leaf_evidence()
    cube_rows: list[dict] = []
    leaf_hashes: dict[str, str] = {}
    for left_index, (left_record, selected_left_units) in enumerate(
        zip(left_records, left_units, strict=True)
    ):
        for right_index, (right_record, selected_right_units) in enumerate(
            zip(right_records, right_units, strict=True)
        ):
            leaf_name = f"d8_l{left_index:02d}_r{right_index:02d}"
            cube = (
                selector_cube(left_index, LEFT_SELECTOR_VARIABLES)
                + selector_cube(right_index, RIGHT_SELECTOR_VARIABLES)
            )
            direct_units = selected_left_units + selected_right_units
            expected_leaf = base_clauses + tuple((unit,) for unit in direct_units)
            specialized = specialize_selectors(master_clauses, cube)
            if specialized != expected_leaf:
                raise RuntimeError(f"master specialization mismatch for {leaf_name}")
            if any(abs(literal) > EDGE_VARIABLE_COUNT for clause in specialized for literal in clause):
                raise RuntimeError(f"selector survived specialization for {leaf_name}")
            leaf_hash = sha256_bytes(dimacs_bytes(EDGE_VARIABLE_COUNT, expected_leaf))
            if leaf_name not in evidence:
                raise RuntimeError(f"missing direct-leaf evidence for {leaf_name}")
            if leaf_hash != evidence[leaf_name]["leaf_cnf_sha256"]:
                raise RuntimeError(
                    f"direct-leaf DIMACS hash mismatch for {leaf_name}: "
                    f"{leaf_hash} != {evidence[leaf_name]['leaf_cnf_sha256']}"
                )
            leaf_hashes[leaf_name] = leaf_hash
            cube_rows.append(
                {
                    "cover_index_one_based": len(cube_rows) + 1,
                    "cube_type": "valid_leaf",
                    "cube": list(cube),
                    "cube_line": "a " + " ".join(map(str, cube)) + " 0",
                    "leaf_certificate_index_one_based": len(cube_rows) + 1,
                    "evidence_source": evidence[leaf_name]["source"],
                    "evidence_status": evidence[leaf_name]["status"],
                    "gen358_parent_id": str(left_record[1]),
                    "gen4416_target_id": str(right_record[1]),
                    "leaf": leaf_name,
                    "left_record_zero_based": left_index,
                    "right_record_zero_based": right_index,
                    "specialized_clause_count": len(expected_leaf),
                    "specialized_leaf_cnf_sha256": leaf_hash,
                    "specialized_unit_count": len(direct_units),
                }
            )

    if len(cube_rows) != 54 or len(leaf_hashes) != 54:
        raise RuntimeError("did not construct exactly 54 distinct valid selector cubes")

    valid_cubes = tuple(tuple(row["cube"]) for row in cube_rows)
    invalid_cube_rows: list[dict] = []
    invalid_clause_start_one_based = len(master_clauses) - len(invalid_left) + 1
    for offset, (code, blocking_clause) in enumerate(
        zip(INVALID_LEFT_CODES, invalid_left, strict=True)
    ):
        cube = selector_cube(code, LEFT_SELECTOR_VARIABLES)
        cover_index = len(cube_rows) + offset + 1
        invalid_cube_rows.append(
            {
                "blocking_clause": list(blocking_clause),
                "blocking_clause_index_one_based": (
                    invalid_clause_start_one_based + offset
                ),
                "cover_index_one_based": cover_index,
                "cube": list(cube),
                "cube_line": "a " + " ".join(map(str, cube)) + " 0",
                "cube_type": "invalid_gen358_code",
                "gen358_invalid_code": code,
                "gen4416_target": "wildcard",
                "leaf_certificate_index_one_based": cover_index,
                "leaf_semantics": (
                    "trivial UNSAT: the selected invalid-code blocker "
                    "specializes to the empty clause"
                ),
            }
        )

    cover_rows = cube_rows + invalid_cube_rows
    cover_cubes = tuple(tuple(row["cube"]) for row in cover_rows)
    if len(cover_cubes) != 59 or len(set(cover_cubes)) != 59:
        raise RuntimeError("cover must contain 59 distinct cubes")
    cover_icnf = icnf_bytes(cover_cubes)
    if parse_icnf_bytes(cover_icnf) != cover_cubes:
        raise RuntimeError("generated cover.icnf does not round-trip")

    negated_cover_clauses = negated_cube_clauses(cover_cubes)
    negated_cover_cnf = dimacs_bytes(
        MASTER_VARIABLE_COUNT, negated_cover_clauses
    )

    coverage_counts: list[int] = []
    for left_code in range(1 << len(LEFT_SELECTOR_VARIABLES)):
        for right_code in range(1 << len(RIGHT_SELECTOR_VARIABLES)):
            full_assignment_cube = (
                selector_cube(left_code, LEFT_SELECTOR_VARIABLES)
                + selector_cube(right_code, RIGHT_SELECTOR_VARIABLES)
            )
            assignment = {
                abs(literal): literal > 0 for literal in full_assignment_cube
            }
            matches = [
                row for row in cover_rows
                if cube_matches_assignment(row["cube"], assignment)
            ]
            coverage_counts.append(len(matches))
            if len(matches) != 1:
                raise RuntimeError(
                    f"selector assignment ({left_code},{right_code}) "
                    f"matches {len(matches)} cover cubes"
                )
            expected_type = (
                "valid_leaf"
                if left_code < LEFT_RECORD_COUNT
                else "invalid_gen358_code"
            )
            if matches[0]["cube_type"] != expected_type:
                raise RuntimeError(
                    f"selector assignment ({left_code},{right_code}) "
                    f"matched {matches[0]['cube_type']} instead of {expected_type}"
                )
            negated_cnf_value = all(
                any(
                    assignment[abs(literal)] == (literal > 0)
                    for literal in clause
                )
                for clause in negated_cover_clauses
            )
            if negated_cnf_value:
                raise RuntimeError(
                    f"negated cover is true at selector assignment "
                    f"({left_code},{right_code})"
                )

    master_cnf = dimacs_bytes(MASTER_VARIABLE_COUNT, master_clauses)
    assumptions = icnf_bytes(valid_cubes)
    cube_manifest = {
        "schema_version": 2,
        "encoding": "little-endian binary selectors; listed literal means selected value",
        "master_cnf_sha256": sha256_bytes(master_cnf),
        "proof_order": (
            "indices 1..54 are valid leaves in lexicographic "
            "(left_record,right_record) order; indices 55..59 are invalid "
            "left codes 27..31 with wildcard right selector"
        ),
        "leaf_certificate_formula": {
            "definition": "Cover.Cube.leafCNF cube guarded_master",
            "clause_order": "cube unit clauses first, then guarded_master clauses",
            "warning": (
                "direct-leaf hashes audit selector specialization only; "
                "those CNFs are not byte-identical Cover leaf inputs"
            ),
        },
        "selector_variables": {
            "gen358_parent_bits": list(LEFT_SELECTOR_VARIABLES),
            "gen4416_target_bits": list(RIGHT_SELECTOR_VARIABLES),
        },
        "valid_leaf_assumptions_file": {
            "description": "54 valid full selector cubes only; not a complete cover",
            "name": "cubes.assumptions",
            "sha256": sha256_bytes(assumptions),
        },
        "cover_file": {
            "description": "complete 59-cube Cover.parseICnf input",
            "name": "cover.icnf",
            "sha256": sha256_bytes(cover_icnf),
        },
        "cubes": cover_rows,
    }
    cube_manifest_data = json_bytes(cube_manifest)
    lrat_files = sorted(LRAT_EVIDENCE.glob("*.lrat"))
    lrat_leaves = [path.stem for path in lrat_files]
    status_counts = Counter(row["evidence_status"] for row in cube_rows)
    metadata = {
        "schema_version": 2,
        "status": "MASTER_CNF_GENERATED_NOT_YET_SOLVED_OR_LRAT_CERTIFIED",
        "scope": (
            "compact target for the 27 x 2 degree-eight case split; "
            "solver statuses are evidence, not proof traces"
        ),
        "orientation": {
            "HOL_blue_1": "Lean red / DIMACS positive",
            "HOL_red_2": "Lean blue / DIMACS negative",
        },
        "selectors": {
            "edge_variables": [1, EDGE_VARIABLE_COUNT],
            "gen358_parent": {
                "variables": list(LEFT_SELECTOR_VARIABLES),
                "valid_codes": [0, LEFT_RECORD_COUNT - 1],
                "invalid_codes_blocked": list(INVALID_LEFT_CODES),
            },
            "gen4416_target": {
                "variables": list(RIGHT_SELECTOR_VARIABLES),
                "valid_codes": [0, RIGHT_RECORD_COUNT - 1],
                "invalid_codes_blocked": [],
            },
        },
        "cnf": {
            "variables": MASTER_VARIABLE_COUNT,
            "clauses": len(master_clauses),
            "sha256": sha256_bytes(master_cnf),
            "bytes": len(master_cnf),
            "clause_breakdown": {
                "fixed_root_base": len(base_clauses),
                "guarded_gen358_units": len(guarded_left),
                "guarded_gen4416_units": len(guarded_right),
                "invalid_gen358_codes": len(invalid_left),
            },
        },
        "cube_manifest": {
            "cover_cubes": len(cover_rows),
            "valid_leaf_cubes": len(cube_rows),
            "invalid_code_cubes": len(invalid_cube_rows),
            "proof_order": cube_manifest["proof_order"],
            "leaf_certificate_formula": cube_manifest["leaf_certificate_formula"],

            "sha256": sha256_bytes(cube_manifest_data),
            "cover_icnf_sha256": sha256_bytes(cover_icnf),
            "valid_leaf_assumptions_sha256": sha256_bytes(assumptions),
        },
        "negated_cover_cnf": {
            "variables": MASTER_VARIABLE_COUNT,
            "clauses": len(negated_cover_clauses),
            "bytes": len(negated_cover_cnf),
            "sha256": sha256_bytes(negated_cover_cnf),
            "matches_Cover_negCubesCNF_order": True,
            "selector_assignments_exhaustively_false": 64,
        },
        "coverage_audit": {
            "selector_assignments_checked": len(coverage_counts),
            "minimum_matching_cubes": min(coverage_counts),
            "maximum_matching_cubes": max(coverage_counts),
            "each_valid_assignment_matches_exactly_one_full_cube": True,
            "each_invalid_assignment_matches_exactly_one_left_only_cube": True,
            "parseICnf_round_trip": True,
        },
        "specialization_audit": {
            "all_54_clause_sequences_equal_direct_leaf": True,
            "all_54_dimacs_hashes_match_recorded_leaf_hashes": True,
            "evidence_status_counts": dict(sorted(status_counts.items())),
            "minimum_specialized_clauses": min(row["specialized_clause_count"] for row in cube_rows),
            "maximum_specialized_clauses": max(row["specialized_clause_count"] for row in cube_rows),
            "minimum_specialized_units": min(row["specialized_unit_count"] for row in cube_rows),
            "maximum_specialized_units": max(row["specialized_unit_count"] for row in cube_rows),
        },
        "proof_artifacts": {
            "cover_leaf_certificates_required": len(cover_rows),
            "cover_certificate_required": True,
            "lrat_files_present": len(lrat_files),
            "lrat_leaves": lrat_leaves,
            "missing_valid_direct_leaf_lrat_count": 54 - len(lrat_files),
            "invalid_code_leaf_lrat_present": 0,
            "warning": (
                "No cover LRAT, no 59 Cover leaf LRAT set, and no claim of "
                "53 additional valid direct-leaf LRAT traces."
            ),
        },
        "source_hashes": {
            "gen358": pilot.helper.sha256_file(pilot.helper.GEN35),
            "gen4416": pilot.helper.sha256_file(pilot.helper.GEN44),
            "results_c1000000_csv": sha256_file(RESULTS_CSV),
            "hard_leaf_result_json": sha256_file(HARD_LEAF_RESULT),
        },
    }
    metadata_data = json_bytes(metadata)
    return {
        "assumptions_bytes": assumptions,
        "base_clauses": base_clauses,
        "cover_cubes": cover_cubes,
        "cover_icnf_bytes": cover_icnf,
        "cover_rows": tuple(cover_rows),
        "cube_manifest": cube_manifest,
        "cube_manifest_bytes": cube_manifest_data,
        "invalid_left_clauses": invalid_left,
        "left_units": tuple(left_units),
        "master_clauses": master_clauses,
        "master_cnf_bytes": master_cnf,
        "metadata": metadata,
        "metadata_bytes": metadata_data,
        "negated_cover_clauses": negated_cover_clauses,
        "negated_cover_cnf_bytes": negated_cover_cnf,
        "right_units": tuple(right_units),
        "valid_leaf_rows": tuple(cube_rows),
    }


def artifact_bytes(result: dict) -> dict[str, bytes]:
    return {
        "guarded_master.cnf": result["master_cnf_bytes"],
        "cover.icnf": result["cover_icnf_bytes"],
        "cube_manifest.json": result["cube_manifest_bytes"],
        "cubes.assumptions": result["assumptions_bytes"],
        "metadata.json": result["metadata_bytes"],
        "negated_cover.cnf": result["negated_cover_cnf_bytes"],
    }


def generate(output: Path) -> dict:
    result = build_result()
    output.mkdir(parents=True, exist_ok=True)
    for name, data in artifact_bytes(result).items():
        (output / name).write_bytes(data)
    return verify(output, result)


def verify(output: Path, expected: dict | None = None) -> dict:
    result = expected or build_result()
    for name, data in artifact_bytes(result).items():
        path = output / name
        if not path.is_file():
            raise RuntimeError(f"missing generated artifact: {path}")
        if path.read_bytes() != data:
            raise RuntimeError(f"generated artifact is stale or modified: {path}")
    return {
        "status": "PASS",
        "output": str(output),
        "master_variables": result["metadata"]["cnf"]["variables"],
        "master_clauses": result["metadata"]["cnf"]["clauses"],
        "master_bytes": result["metadata"]["cnf"]["bytes"],
        "master_sha256": result["metadata"]["cnf"]["sha256"],
        "cover_cubes": len(result["cover_cubes"]),
        "valid_leaf_cubes": len(result["valid_leaf_rows"]),
        "lrat_files_present": result["metadata"]["proof_artifacts"]["lrat_files_present"],
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "command", choices=("audit", "generate", "verify"),
        help="audit in memory, write deterministic artifacts, or verify them",
    )
    result.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "audit":
            built = build_result()
            report = {
                "status": "PASS",
                "master_variables": built["metadata"]["cnf"]["variables"],
                "master_clauses": built["metadata"]["cnf"]["clauses"],
                "master_bytes": built["metadata"]["cnf"]["bytes"],
                "master_sha256": built["metadata"]["cnf"]["sha256"],
                "cover_cubes": len(built["cover_cubes"]),
                "valid_leaf_cubes": len(built["valid_leaf_rows"]),
                "proof_artifacts": built["metadata"]["proof_artifacts"],
            }
        elif args.command == "generate":
            report = generate(args.output.resolve())
        else:
            report = verify(args.output.resolve())
        print(json.dumps(report, indent=2, sort_keys=True))
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
