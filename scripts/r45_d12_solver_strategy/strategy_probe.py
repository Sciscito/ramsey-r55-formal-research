#!/usr/bin/env python3
"""Measured search experiments for the R(4,5,25) red-degree-12 leaves.

The script deliberately writes only to an explicit ``S:`` path.  It can add
two kinds of *equisatisfiable* search restrictions which are not clauses of
the current certified CNF:

* lexicographically sort the twelve A-to-B cross-edge columns, using the full
  permutation symmetry of the B block;
* choose a rooted R(4,4,12) split in B and fix its two R(3,4) catalogue
  representatives.

Those restrictions are useful solver probes, not LRAT certificates for the
unrestricted input.  A later formal relabelling/cover theorem is required
before their UNSAT results can close the original branch.

The optional degree bounds are logical consequences of R(3,5) <= 14 and
R(4,4) <= 18, but likewise need an explicit checked bridge before a proof of
the strengthened CNF can be reused for the original CNF.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path, PureWindowsPath
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"

ORDER = 24
A = tuple(range(12))
B = tuple(range(12, 24))
EDGE_VARIABLE_COUNT = 276

Clause = tuple[int, ...]
Graph = tuple[int, ...]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ramsey = load_module("r45_d12_strategy_ramsey", RAMSEY_PATH)


def require_ssd(path: Path) -> Path:
    if PureWindowsPath(str(path)).drive.upper() != "S:":
        raise ValueError(f"output must be explicitly rooted on S:, got {path}")
    return path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def parse_cnf(path: Path) -> tuple[int, list[Clause]]:
    variables: int | None = None
    expected: int | None = None
    clauses: list[Clause] = []
    with path.open("r", encoding="ascii") as stream:
        for line_number, line in enumerate(stream, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith("c"):
                continue
            fields = stripped.split()
            if fields[0] == "p":
                if fields[:2] != ["p", "cnf"] or len(fields) != 4:
                    raise ValueError(f"bad header on line {line_number}")
                variables, expected = int(fields[2]), int(fields[3])
                continue
            values = tuple(int(field) for field in fields)
            if not values or values[-1] != 0 or values.count(0) != 1:
                raise ValueError(f"bad clause on line {line_number}")
            clauses.append(values[:-1])
    if variables is None or expected is None:
        raise ValueError("missing DIMACS header")
    if len(clauses) != expected:
        raise ValueError(f"header says {expected} clauses, parsed {len(clauses)}")
    if any(not clause for clause in clauses):
        raise ValueError("input unexpectedly contains an empty clause")
    if any(abs(lit) > variables for clause in clauses for lit in clause):
        raise ValueError("input literal exceeds header")
    return variables, clauses


def write_cnf(path: Path, variables: int, clauses: Sequence[Clause]) -> None:
    path = require_ssd(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".partial")
    with temporary.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"p cnf {variables} {len(clauses)}\n")
        for clause in clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    if path.exists():
        if sha256(path) == sha256(temporary):
            temporary.unlink()
            return
        raise FileExistsError(f"refusing to overwrite differing file {path}")
    temporary.replace(path)


def catalogue(order: int) -> tuple[Graph, ...]:
    path = REPOSITORY / "r55" / f"r35_{order}.g6"
    records = tuple(line.strip() for line in path.read_text(encoding="ascii").splitlines() if line.strip())
    return tuple(ramsey.decode_graph6(record) for record in records)


def is_r34_free(graph: Graph) -> bool:
    return (
        ramsey.count_cliques(graph, 3) == 0
        and ramsey.count_cliques(ramsey.complement_graph(graph), 4) == 0
    )


def r34_catalogue(order: int) -> tuple[Graph, ...]:
    return tuple(graph for graph in catalogue(order) if is_r34_free(graph))


def graph_units(vertices: Sequence[int], graph: Graph, *, complement: bool = False) -> tuple[Clause, ...]:
    if len(vertices) != len(graph):
        raise ValueError("vertex block and graph have different orders")
    units: list[Clause] = []
    for source_left, source_right in itertools.combinations(range(len(vertices)), 2):
        edge = ramsey.has_edge(graph, source_left, source_right)
        if complement:
            edge = not edge
        variable = ramsey.edge_var(ORDER, vertices[source_left], vertices[source_right])
        units.append((variable if edge else -variable,))
    return tuple(units)


def add_lex_cross(builder) -> None:
    """Sort B by its A-neighbourhood bit vector (False before True)."""
    rows = tuple(
        tuple(ramsey.edge_var(ORDER, a, b) for a in A)
        for b in B
    )
    for left, right in zip(rows, rows[1:]):
        builder.add_lex_leq(left, right)


def add_global_degree_bounds(builder) -> None:
    """Make the already-proved global 7..13 red degree bounds explicit."""
    for vertex in range(ORDER):
        incident = tuple(
            ramsey.edge_var(ORDER, vertex, other)
            for other in range(ORDER)
            if other != vertex
        )
        if vertex in A:
            # The deleted root contributes one red edge: 6 <= sum <= 12.
            builder.add_at_most(incident, 12)
            builder.add_at_most(tuple(-lit for lit in incident), 17)
        else:
            # The deleted root contributes one blue edge: 7 <= sum <= 13.
            builder.add_at_most(incident, 13)
            builder.add_at_most(tuple(-lit for lit in incident), 16)


def add_b_local_degree_bounds(builder) -> None:
    """In an R(4,4,12) graph each internal degree lies in 3..8."""
    for vertex in B:
        incident = tuple(
            ramsey.edge_var(ORDER, vertex, other)
            for other in B
            if other != vertex
        )
        builder.add_at_most(incident, 8)
        builder.add_at_most(tuple(-lit for lit in incident), 8)


def rooted_b_units(degree: int, left_index: int, anti_index: int) -> tuple[Clause, ...]:
    if degree not in range(3, 9):
        raise ValueError("B-root degree must lie in 3..8")
    root = B[0]
    left = B[1 : 1 + degree]
    anti = B[1 + degree :]
    left_catalogue = r34_catalogue(len(left))
    anti_catalogue = r34_catalogue(len(anti))
    if not 0 <= left_index < len(left_catalogue):
        raise ValueError(f"left index outside 0..{len(left_catalogue) - 1}")
    if not 0 <= anti_index < len(anti_catalogue):
        raise ValueError(f"anti index outside 0..{len(anti_catalogue) - 1}")
    units: list[Clause] = []
    units.extend((ramsey.edge_var(ORDER, root, vertex),) for vertex in left)
    units.extend((-ramsey.edge_var(ORDER, root, vertex),) for vertex in anti)
    units.extend(graph_units(left, left_catalogue[left_index]))
    # The anti representative describes the complement on blue neighbours.
    units.extend(graph_units(anti, anti_catalogue[anti_index], complement=True))
    return tuple(units)


def independent_sets(graph: Graph, size: int) -> tuple[tuple[int, ...], ...]:
    result: list[tuple[int, ...]] = []
    for vertices in itertools.combinations(range(len(graph)), size):
        if all(not ramsey.has_edge(graph, left, right) for left, right in itertools.combinations(vertices, 2)):
            result.append(vertices)
    return tuple(result)


def structure_report() -> dict[str, object]:
    counts = {order: len(r34_catalogue(order)) for order in range(3, 9)}
    rooted_leaves = {
        degree: counts[degree] * counts[11 - degree]
        for degree in range(3, 9)
    }
    a_rows: list[dict[str, object]] = []
    for index, graph in enumerate(catalogue(12)):
        independent4 = independent_sets(graph, 4)
        admissible = 0
        for mask in range(1 << 12):
            # A red-neighbour mask for one B vertex must hit every blue K4 in A.
            if all(any((mask >> vertex) & 1 for vertex in block) for block in independent4):
                admissible += 1
        a_rows.append(
            {
                "index": index,
                "red_edges": ramsey.graph_edge_count(graph),
                "degree_sequence": sorted(row.bit_count() for row in graph),
                "blue_K4s": len(independent4),
                "admissible_cross_rows_of_4096": admissible,
            }
        )
    return {
        "r34_catalogue_counts": counts,
        "rooted_B_leaf_counts_by_degree": rooted_leaves,
        "rooted_B_total_labelled_cover_leaves": sum(rooted_leaves.values()),
        "A_catalogue_cross_row_stats": a_rows,
    }


def strengthen(args: argparse.Namespace) -> None:
    variables, clauses = parse_cnf(args.input)
    if variables != EDGE_VARIABLE_COUNT:
        raise ValueError(f"expected {EDGE_VARIABLE_COUNT} variables, got {variables}")
    original_clause_count = len(clauses)
    builder = ramsey.CnfBuilder(variables + 1)
    modes = set(args.mode.split("+"))
    known = {"lex-cross", "degree-bounds", "b-degree-bounds", "rooted-b"}
    if not modes or modes - known:
        raise ValueError(f"unknown mode component(s): {sorted(modes - known)}")
    if "lex-cross" in modes:
        add_lex_cross(builder)
    if "degree-bounds" in modes:
        add_global_degree_bounds(builder)
    if "b-degree-bounds" in modes:
        add_b_local_degree_bounds(builder)
    if "rooted-b" in modes:
        clauses.extend(rooted_b_units(args.b_degree, args.left_index, args.anti_index))
    clauses.extend(builder.clauses)
    variables = builder.next_variable - 1
    write_cnf(args.output, variables, clauses)
    print(json.dumps({
        "input": str(args.input),
        "input_sha256": sha256(args.input),
        "output": str(args.output),
        "output_sha256": sha256(args.output),
        "mode": args.mode,
        "variables": variables,
        "original_clauses": original_clause_count,
        "added_clauses": len(clauses) - original_clause_count,
        "clauses": len(clauses),
        "proof_scope_warning": "equisatisfiability/degree bridge required; not an LRAT proof of the original CNF",
    }, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("structure")
    strengthen_parser = subparsers.add_parser("strengthen")
    strengthen_parser.add_argument("--input", type=Path, required=True)
    strengthen_parser.add_argument("--output", type=Path, required=True)
    strengthen_parser.add_argument("--mode", required=True)
    strengthen_parser.add_argument("--b-degree", type=int, default=3)
    strengthen_parser.add_argument("--left-index", type=int, default=0)
    strengthen_parser.add_argument("--anti-index", type=int, default=0)
    args = parser.parse_args()
    if args.command == "structure":
        print(json.dumps(structure_report(), indent=2, sort_keys=True))
    else:
        strengthen(args)


if __name__ == "__main__":
    main()
