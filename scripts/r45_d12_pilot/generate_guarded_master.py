#!/usr/bin/env python3
"""Generate the solver-free guarded master for the red-degree-12 branch.

The deleted root has twelve red and twelve blue neighbours.  The common
fixed-root core is ``encode(24,4,5)`` together with no red triangle on the
red-neighbour block and no blue ``K4`` on the blue-neighbour block.  Four
little-endian selector variables choose one of the twelve certified
``R(3,5,12)`` catalogue representatives.  Codes 12,...,15 share the single
dyadic blocker ``not (bit2 and bit3)``.

This program does not invoke a SAT solver and does not claim UNSAT.  Its CLI
can only write or verify artifacts under an explicit ``S:`` path so the large
proof experiment cannot silently consume the system drive.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path, PureWindowsPath
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"
CATALOGUE_PATH = REPOSITORY / "r55" / "r35_12.g6"
CATALOGUE_CERTIFICATE_PATH = REPOSITORY / "r55" / "r35_extension_certificate.json"

NON_ROOT_ORDER = 24
ROOT_RED_DEGREE = 12
ROOT_BLUE_DEGREE = NON_ROOT_ORDER - ROOT_RED_DEGREE
EDGE_VARIABLE_COUNT = NON_ROOT_ORDER * (NON_ROOT_ORDER - 1) // 2
SELECTOR_VARIABLES = tuple(range(EDGE_VARIABLE_COUNT + 1, EDGE_VARIABLE_COUNT + 5))
MASTER_VARIABLE_COUNT = SELECTOR_VARIABLES[-1]
CATALOGUE_RECORD_COUNT = 12
SELECTOR_CODE_COUNT = 1 << len(SELECTOR_VARIABLES)

# Codes 12,...,15 are exactly the assignments with bits 2 and 3 both true.
INVALID_CODE_CUBE = (SELECTOR_VARIABLES[2], SELECTOR_VARIABLES[3])
INVALID_CODE_BLOCKER = tuple(-literal for literal in INVALID_CODE_CUBE)

EXPECTED_BASE_CLAUSE_COUNT = 53_845
EXPECTED_GUARDED_UNIT_COUNT = 792
EXPECTED_MASTER_CLAUSE_COUNT = 54_638
EXPECTED_COVER_CUBE_COUNT = 13

Clause = tuple[int, ...]


def load_ramsey_module():
    spec = importlib.util.spec_from_file_location(
        "r45_d12_local_ramsey", RAMSEY_PATH
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {RAMSEY_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ramsey = load_ramsey_module()


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


def edge_var(order: int, left: int, right: int) -> int:
    """One-based row-major upper-triangle DIMACS variable."""
    if not 0 <= left < right < order:
        raise ValueError(f"invalid edge ({left},{right}) in K_{order}")
    return left * (2 * order - left - 1) // 2 + (right - left)


def clique_clause(
    order: int, vertices: Sequence[int], *, positive: bool
) -> Clause:
    sign = 1 if positive else -1
    return tuple(
        sign * edge_var(order, left, right)
        for left, right in itertools.combinations(vertices, 2)
    )


def fixed_root_clauses(root_red_degree: int = ROOT_RED_DEGREE) -> tuple[Clause, ...]:
    """Reduced ``encode(25,4,5)`` for a root of the requested red degree."""
    if not 0 <= root_red_degree <= NON_ROOT_ORDER:
        raise ValueError("root red degree must lie in 0..24")
    clauses: list[Clause] = []
    clauses.extend(
        clique_clause(NON_ROOT_ORDER, vertices, positive=False)
        for vertices in itertools.combinations(range(NON_ROOT_ORDER), 4)
    )
    clauses.extend(
        clique_clause(NON_ROOT_ORDER, vertices, positive=True)
        for vertices in itertools.combinations(range(NON_ROOT_ORDER), 5)
    )
    clauses.extend(
        clique_clause(NON_ROOT_ORDER, vertices, positive=False)
        for vertices in itertools.combinations(range(root_red_degree), 3)
    )
    clauses.extend(
        clique_clause(NON_ROOT_ORDER, vertices, positive=True)
        for vertices in itertools.combinations(
            range(root_red_degree, NON_ROOT_ORDER), 4
        )
    )
    return tuple(clauses)


def independently_simplified_full_formula(
    root_red_degree: int = ROOT_RED_DEGREE,
) -> tuple[Clause, ...]:
    """Eliminate the root units directly from the full 25-vertex formula."""
    root_values = {
        vertex: vertex <= root_red_degree
        for vertex in range(1, NON_ROOT_ORDER + 1)
    }
    reduced: list[Clause] = []
    clause_streams = itertools.chain(
        (
            (vertices, False)
            for vertices in itertools.combinations(range(NON_ROOT_ORDER + 1), 4)
        ),
        (
            (vertices, True)
            for vertices in itertools.combinations(range(NON_ROOT_ORDER + 1), 5)
        ),
    )
    for vertices, positive in clause_streams:
        satisfied = False
        clause: list[int] = []
        for left, right in itertools.combinations(vertices, 2):
            if left == 0:
                if root_values[right] == positive:
                    satisfied = True
                    break
                continue
            clause.append(
                (1 if positive else -1)
                * edge_var(NON_ROOT_ORDER, left - 1, right - 1)
            )
        if not satisfied:
            reduced.append(tuple(clause))
    return tuple(reduced)


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


def dimacs_bytes(variable_count: int, clauses: Sequence[Clause]) -> bytes:
    validate_clauses(variable_count, clauses)
    lines = [f"p cnf {variable_count} {len(clauses)}\n"]
    lines.extend(" ".join(map(str, clause)) + " 0\n" for clause in clauses)
    return "".join(lines).encode("ascii")


def selector_cube(code: int, variables: Sequence[int] = SELECTOR_VARIABLES) -> Clause:
    if not 0 <= code < 1 << len(variables):
        raise ValueError(f"selector code {code} does not fit in {len(variables)} bits")
    return tuple(
        variable if (code >> bit_index) & 1 else -variable
        for bit_index, variable in enumerate(variables)
    )


def selector_guard(code: int, variables: Sequence[int] = SELECTOR_VARIABLES) -> Clause:
    """Clause false exactly on the selected complete little-endian code."""
    return tuple(-literal for literal in selector_cube(code, variables))


def icnf_bytes(cubes: Sequence[Clause]) -> bytes:
    return "".join(
        "a " + " ".join(map(str, cube)) + " 0\n" for cube in cubes
    ).encode("ascii")


def parse_icnf_bytes(data: bytes) -> tuple[Clause, ...]:
    cubes: list[Clause] = []
    for line_number, raw_line in enumerate(data.decode("ascii").splitlines(), 1):
        tokens = raw_line.strip().split()
        if not tokens:
            continue
        if tokens[0] != "a":
            raise RuntimeError(f"iCNF line {line_number} does not start with 'a'")
        try:
            values = tuple(int(token) for token in tokens[1:])
        except ValueError as exc:
            raise RuntimeError(f"non-integer iCNF token on line {line_number}") from exc
        if not values or values[-1] != 0 or values.count(0) != 1:
            raise RuntimeError(f"invalid iCNF terminator on line {line_number}")
        cubes.append(values[:-1])
    return tuple(cubes)


def cube_matches_assignment(cube: Sequence[int], assignment: dict[int, bool]) -> bool:
    return all(
        abs(literal) in assignment
        and assignment[abs(literal)] == (literal > 0)
        for literal in cube
    )


def specialize_selectors(clauses: Sequence[Clause], cube: Sequence[int]) -> tuple[Clause, ...]:
    assignment = {abs(literal): literal > 0 for literal in cube}
    if len(assignment) != len(cube) or set(assignment) != set(SELECTOR_VARIABLES):
        raise RuntimeError("selector cube must assign every selector exactly once")
    restricted: list[Clause] = []
    for clause in clauses:
        if any(
            abs(literal) in assignment
            and assignment[abs(literal)] == (literal > 0)
            for literal in clause
        ):
            continue
        reduced = tuple(
            literal for literal in clause if abs(literal) not in assignment
        )
        if not reduced:
            raise RuntimeError("selector cube falsifies a master clause")
        restricted.append(reduced)
    return tuple(restricted)


def _certificate_catalogue_entry() -> dict:
    certificate = json.loads(
        CATALOGUE_CERTIFICATE_PATH.read_text(encoding="utf-8")
    )
    entries = certificate.get("catalogues")
    if not isinstance(entries, list) or len(entries) <= ROOT_RED_DEGREE:
        raise RuntimeError("catalogue certificate does not reach order 12")
    entry = entries[ROOT_RED_DEGREE]
    if not isinstance(entry, dict):
        raise RuntimeError("malformed order-12 catalogue certificate entry")
    expected = {
        "order": ROOT_RED_DEGREE,
        "file": CATALOGUE_PATH.name,
        "graph_count": CATALOGUE_RECORD_COUNT,
    }
    if any(entry.get(key) != value for key, value in expected.items()):
        raise RuntimeError(f"unexpected order-12 catalogue metadata: {entry}")
    if str(entry.get("sha256", "")).upper() != sha256_file(CATALOGUE_PATH):
        raise RuntimeError("order-12 catalogue hash disagrees with its certificate")
    return entry


def load_catalogue() -> tuple[tuple[str, object], ...]:
    _certificate_catalogue_entry()
    records = tuple(
        line.strip()
        for line in CATALOGUE_PATH.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    if len(records) != CATALOGUE_RECORD_COUNT or len(set(records)) != len(records):
        raise RuntimeError("order-12 catalogue must contain 12 distinct records")
    decoded: list[tuple[str, object]] = []
    for index, record in enumerate(records):
        graph = ramsey.decode_graph6(record)
        if len(graph) != ROOT_RED_DEGREE:
            raise RuntimeError(f"catalogue graph {index} has order {len(graph)}")
        if ramsey.count_cliques(graph, 3) != 0:
            raise RuntimeError(f"catalogue graph {index} contains a red triangle")
        if ramsey.count_cliques(ramsey.complement_graph(graph), 5) != 0:
            raise RuntimeError(f"catalogue graph {index} contains a blue K5")
        decoded.append((record, graph))
    return tuple(decoded)


def graph_units(graph: object) -> Clause:
    if len(graph) != ROOT_RED_DEGREE:
        raise RuntimeError("catalogue graph has the wrong order")
    units = tuple(
        edge_var(NON_ROOT_ORDER, left, right)
        if ramsey.has_edge(graph, left, right)
        else -edge_var(NON_ROOT_ORDER, left, right)
        for left, right in itertools.combinations(range(ROOT_RED_DEGREE), 2)
    )
    if len(units) != 66 or len(set(map(abs, units))) != 66:
        raise RuntimeError("catalogue graph is not a complete 66-edge assignment")
    return units


@lru_cache(maxsize=1)
def build_result() -> dict:
    edge_mapping_checks = 0
    for order in (NON_ROOT_ORDER, NON_ROOT_ORDER + 1):
        for left, right in itertools.combinations(range(order), 2):
            if edge_var(order, left, right) != ramsey.edge_var(order, left, right):
                raise RuntimeError(
                    f"edge-variable mapping mismatch in K{order} at ({left},{right})"
                )
            edge_mapping_checks += 1

    base_clauses = fixed_root_clauses()
    if len(base_clauses) != EXPECTED_BASE_CLAUSE_COUNT:
        raise RuntimeError(
            f"base clause count changed: {len(base_clauses)} != "
            f"{EXPECTED_BASE_CLAUSE_COUNT}"
        )
    independently_reduced = independently_simplified_full_formula()
    if Counter(base_clauses) != Counter(independently_reduced):
        raise RuntimeError("fixed-root reduction audit failed")
    validate_clauses(EDGE_VARIABLE_COUNT, base_clauses)

    catalogue = load_catalogue()
    catalogue_units = tuple(graph_units(graph) for _record, graph in catalogue)
    guarded_units = tuple(
        selector_guard(index) + (unit,)
        for index, units in enumerate(catalogue_units)
        for unit in units
    )
    if len(guarded_units) != EXPECTED_GUARDED_UNIT_COUNT:
        raise RuntimeError("guarded catalogue unit count changed")

    master_clauses = base_clauses + guarded_units + (INVALID_CODE_BLOCKER,)
    if len(master_clauses) != EXPECTED_MASTER_CLAUSE_COUNT:
        raise RuntimeError("master clause count changed")
    validate_clauses(MASTER_VARIABLE_COUNT, master_clauses)

    valid_rows: list[dict] = []
    leaf_hashes: list[str] = []
    for index, ((record, graph), units) in enumerate(
        zip(catalogue, catalogue_units, strict=True)
    ):
        cube = selector_cube(index)
        expected_leaf = base_clauses + tuple((unit,) for unit in units)
        specialized = specialize_selectors(master_clauses, cube)
        if specialized != expected_leaf:
            raise RuntimeError(f"master specialization mismatch at catalogue {index}")
        leaf_hash = sha256_bytes(dimacs_bytes(EDGE_VARIABLE_COUNT, expected_leaf))
        leaf_hashes.append(leaf_hash)
        valid_rows.append(
            {
                "catalogue_index_zero_based": index,
                "catalogue_record": record,
                "catalogue_red_edges": sum(row.bit_count() for row in graph) // 2,
                "cover_index_one_based": index + 1,
                "cube": list(cube),
                "cube_line": "a " + " ".join(map(str, cube)) + " 0",
                "cube_type": "valid_r35_order12_type",
                "leaf": f"d12_t{index:02d}",
                "specialized_clause_count": len(expected_leaf),
                "specialized_leaf_cnf_sha256": leaf_hash,
                "specialized_unit_count": len(units),
            }
        )

    invalid_row = {
        "blocking_clause": list(INVALID_CODE_BLOCKER),
        "blocking_clause_index_one_based": len(master_clauses),
        "cover_index_one_based": CATALOGUE_RECORD_COUNT + 1,
        "cube": list(INVALID_CODE_CUBE),
        "cube_line": "a " + " ".join(map(str, INVALID_CODE_CUBE)) + " 0",
        "cube_type": "invalid_selector_codes_12_through_15",
        "invalid_selector_codes": list(range(CATALOGUE_RECORD_COUNT, SELECTOR_CODE_COUNT)),
        "leaf": "d12_invalid_12_15",
        "leaf_semantics": "trivial UNSAT: blocker is the negation of this partial cube",
    }
    cover_rows = tuple(valid_rows + [invalid_row])
    cover_cubes = tuple(tuple(row["cube"]) for row in cover_rows)
    if len(cover_cubes) != EXPECTED_COVER_CUBE_COUNT:
        raise RuntimeError("cover cube count changed")
    if len(set(cover_cubes)) != len(cover_cubes):
        raise RuntimeError("cover contains duplicate cubes")

    coverage_counts: list[int] = []
    for code in range(SELECTOR_CODE_COUNT):
        assignment = {
            abs(literal): literal > 0 for literal in selector_cube(code)
        }
        matches = [
            row for row in cover_rows
            if cube_matches_assignment(row["cube"], assignment)
        ]
        coverage_counts.append(len(matches))
        if len(matches) != 1:
            raise RuntimeError(f"selector code {code} matches {len(matches)} cubes")
        expected_type = (
            "valid_r35_order12_type"
            if code < CATALOGUE_RECORD_COUNT
            else "invalid_selector_codes_12_through_15"
        )
        if matches[0]["cube_type"] != expected_type:
            raise RuntimeError(f"selector code {code} matched the wrong cube type")

    cover_icnf = icnf_bytes(cover_cubes)
    if parse_icnf_bytes(cover_icnf) != cover_cubes:
        raise RuntimeError("cover iCNF round-trip failed")
    valid_assumptions = icnf_bytes(tuple(selector_cube(i) for i in range(12)))
    negated_cover_clauses = tuple(
        tuple(-literal for literal in cube) for cube in cover_cubes
    )

    base_cnf = dimacs_bytes(EDGE_VARIABLE_COUNT, base_clauses)
    master_cnf = dimacs_bytes(MASTER_VARIABLE_COUNT, master_clauses)
    negated_cover_cnf = dimacs_bytes(
        MASTER_VARIABLE_COUNT, negated_cover_clauses
    )
    leaf_hash_list_data = json_bytes(leaf_hashes)
    cube_manifest = {
        "schema_version": 1,
        "encoding": "little-endian selector; DIMACS true is a red edge",
        "master_cnf_sha256": sha256_bytes(master_cnf),
        "catalogue": {
            "file": CATALOGUE_PATH.name,
            "order": ROOT_RED_DEGREE,
            "records": CATALOGUE_RECORD_COUNT,
            "sha256": sha256_file(CATALOGUE_PATH),
        },
        "proof_order": (
            "indices 1..12 are catalogue types 0..11; index 13 is the "
            "partial cube covering selector codes 12..15"
        ),
        "selector_variables": list(SELECTOR_VARIABLES),
        "cover_file": {
            "name": "cover.icnf",
            "sha256": sha256_bytes(cover_icnf),
        },
        "valid_leaf_assumptions_file": {
            "name": "cubes.assumptions",
            "sha256": sha256_bytes(valid_assumptions),
        },
        "cubes": cover_rows,
    }
    cube_manifest_data = json_bytes(cube_manifest)
    metadata = {
        "schema_version": 1,
        "status": "GENERATED_NOT_SOLVED_OR_LRAT_CERTIFIED",
        "scope": "red-degree-12 root branch of encode(25,4,5)",
        "disk_policy": "CLI artifacts require an explicit S: path",
        "orientation": {
            "catalogue_edge": "Lean red / DIMACS positive",
            "catalogue_nonedge": "Lean blue / DIMACS negative",
        },
        "fixed_root": {
            "red_neighbours": [0, ROOT_RED_DEGREE - 1],
            "blue_neighbours": [ROOT_RED_DEGREE, NON_ROOT_ORDER - 1],
            "edge_mapping_checks": edge_mapping_checks,
            "reduction_clause_counter_equal": True,
        },
        "cnf": {
            "base_variables": EDGE_VARIABLE_COUNT,
            "variables": MASTER_VARIABLE_COUNT,
            "clauses": len(master_clauses),
            "sha256": sha256_bytes(master_cnf),
            "bytes": len(master_cnf),
            "clause_breakdown": {
                "global_no_red_K4": 10_626,
                "global_no_blue_K5": 42_504,
                "red_neighbour_no_red_K3": 220,
                "blue_neighbour_no_blue_K4": 495,
                "guarded_r35_order12_units": len(guarded_units),
                "invalid_dyadic_blockers": 1,
            },
        },
        "hashes": {
            "base_cnf_sha256": sha256_bytes(base_cnf),
            "cover_icnf_sha256": sha256_bytes(cover_icnf),
            "cube_manifest_sha256": sha256_bytes(cube_manifest_data),
            "leaf_hash_list_sha256": sha256_bytes(leaf_hash_list_data),
            "negated_cover_cnf_sha256": sha256_bytes(negated_cover_cnf),
            "valid_assumptions_sha256": sha256_bytes(valid_assumptions),
        },
        "catalogue": {
            "records": len(catalogue),
            "units_per_record": 66,
            "source_sha256": sha256_file(CATALOGUE_PATH),
            "certificate_sha256": sha256_file(CATALOGUE_CERTIFICATE_PATH),
        },
        "cover": {
            "cubes": len(cover_cubes),
            "valid_full_cubes": len(valid_rows),
            "invalid_partial_cubes": 1,
            "selector_assignments_checked": len(coverage_counts),
            "minimum_matching_cubes": min(coverage_counts),
            "maximum_matching_cubes": max(coverage_counts),
        },
        "specialization_audit": {
            "all_12_clause_sequences_equal_direct_leaf": True,
            "specialized_clauses": EXPECTED_BASE_CLAUSE_COUNT + 66,
            "specialized_units": 66,
            "leaf_cnf_sha256": leaf_hashes,
        },
        "proof_artifacts": {
            "leaf_lrat_required": EXPECTED_COVER_CUBE_COUNT,
            "cover_lrat_required": True,
            "present": 0,
            "warning": "No SAT status or LRAT proof is claimed by this generator.",
        },
    }
    metadata_data = json_bytes(metadata)
    return {
        "assumptions_bytes": valid_assumptions,
        "base_clauses": base_clauses,
        "base_cnf_bytes": base_cnf,
        "catalogue": catalogue,
        "catalogue_units": catalogue_units,
        "cover_cubes": cover_cubes,
        "cover_icnf_bytes": cover_icnf,
        "cover_rows": cover_rows,
        "cube_manifest": cube_manifest,
        "cube_manifest_bytes": cube_manifest_data,
        "invalid_blocker": INVALID_CODE_BLOCKER,
        "leaf_hash_list_bytes": leaf_hash_list_data,
        "master_clauses": master_clauses,
        "master_cnf_bytes": master_cnf,
        "metadata": metadata,
        "metadata_bytes": metadata_data,
        "negated_cover_clauses": negated_cover_clauses,
        "negated_cover_cnf_bytes": negated_cover_cnf,
        "valid_leaf_rows": tuple(valid_rows),
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


def require_explicit_ssd_path(path: Path) -> Path:
    """Reject every CLI artifact path that is not explicitly rooted on S:."""
    windows_path = PureWindowsPath(str(path))
    if windows_path.drive.upper() != "S:" or not windows_path.is_absolute():
        raise ValueError(
            f"artifact path must be explicit and rooted on S:, received {path}"
        )
    return path


def generate(output: Path) -> dict:
    output = require_explicit_ssd_path(output)
    if output.exists() and any(output.iterdir()):
        raise RuntimeError(f"refusing to overwrite non-empty output directory: {output}")
    output.mkdir(parents=True, exist_ok=True)
    result = build_result()
    for name, data in artifact_bytes(result).items():
        with (output / name).open("xb") as stream:
            stream.write(data)
    return verify(output, result)


def verify(output: Path, expected: dict | None = None) -> dict:
    output = require_explicit_ssd_path(output)
    result = expected or build_result()
    artifacts = artifact_bytes(result)
    for name, expected_data in artifacts.items():
        path = output / name
        if not path.is_file():
            raise RuntimeError(f"missing generated artifact: {path}")
        actual = path.read_bytes()
        if actual != expected_data:
            raise RuntimeError(
                f"artifact mismatch for {name}: {sha256_bytes(actual)} != "
                f"{sha256_bytes(expected_data)}"
            )
    return {
        "status": "PASS",
        "output": str(output),
        "master_variables": MASTER_VARIABLE_COUNT,
        "master_clauses": EXPECTED_MASTER_CLAUSE_COUNT,
        "master_sha256": sha256_bytes(result["master_cnf_bytes"]),
        "cover_cubes": EXPECTED_COVER_CUBE_COUNT,
        "valid_leaf_cubes": CATALOGUE_RECORD_COUNT,
        "warning": "generated and audited only; no UNSAT or LRAT claim",
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate_command = commands.add_parser("generate")
    generate_command.add_argument("--output", type=Path, required=True)
    generate_command.set_defaults(func=lambda args: generate(args.output))
    verify_command = commands.add_parser("verify")
    verify_command.add_argument("--directory", type=Path, required=True)
    verify_command.set_defaults(func=lambda args: verify(args.directory))
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        report = args.func(args)
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
