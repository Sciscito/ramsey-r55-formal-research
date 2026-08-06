#!/usr/bin/env python3
"""Bounded SAT pilot for the 54 Barakeel degree-eight parent pairs.

This deliberately lives under ``work/scratch``.  It does not establish the
completeness of the imported HOL4 covers.  It only:

* independently rechecks the two small cover files and their child graphs;
* proves by exhaustive clause comparison that the 24-vertex formula used here
  is the simplification of the fixed-root 25-vertex Ramsey formula;
* emits the 27 x 2 parent cubes; and
* runs CaDiCaL with explicit per-leaf conflict and wall-clock limits.

Colour convention:

* HOL4 colour 1 = blue, colour 2 = red;
* DIMACS positive = red, negative = blue;
* hence the global non-root formula is ``encode(24, 5, 4)`` in the local Lean
  convention (no red K5 and no blue K4).
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import itertools
import json
import os
import re
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict
from pathlib import Path
from typing import Iterable, Iterator, Sequence


HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
AUDIT_DIR = HERE
GEN35 = HERE / "data" / "gen358"
GEN44 = HERE / "data" / "gen4416"
RAMSEY_PY = WORK / "r55" / "ramsey.py"


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load Python module from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


cover = load_module("barakeel_cover_checker", AUDIT_DIR / "check_barakeel_covers.py")
local_ramsey = load_module("local_ramsey_encoder", RAMSEY_PY)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def edge_var(order: int, left: int, right: int) -> int:
    """One-based DIMACS row-major upper-triangle variable."""
    if not 0 <= left < right < order:
        raise ValueError(f"invalid edge ({left},{right}) in K_{order}")
    return left * (2 * order - left - 1) // 2 + (right - left)


def clique_clause(order: int, vertices: Sequence[int], positive: bool) -> tuple[int, ...]:
    sign = 1 if positive else -1
    return tuple(sign * edge_var(order, i, j) for i, j in itertools.combinations(vertices, 2))


def ramsey_clauses(order: int, red_size: int, blue_size: int) -> Iterator[tuple[int, ...]]:
    for vertices in itertools.combinations(range(order), red_size):
        yield clique_clause(order, vertices, positive=False)
    for vertices in itertools.combinations(range(order), blue_size):
        yield clique_clause(order, vertices, positive=True)


def reduced_fixed_root_clauses() -> list[tuple[int, ...]]:
    """K25 fixed-root semantics expressed only on the 24 non-root vertices.

    Vertices 0..7 are the eight blue neighbours of the deleted root and
    vertices 8..23 its sixteen red neighbours.
    """
    clauses = list(ramsey_clauses(24, red_size=5, blue_size=4))
    # A blue K3 here plus the root would be a forbidden blue K4.
    for vertices in itertools.combinations(range(8), 3):
        clauses.append(clique_clause(24, vertices, positive=True))
    # A red K4 here plus the root would be a forbidden red K5.
    for vertices in itertools.combinations(range(8, 24), 4):
        clauses.append(clique_clause(24, vertices, positive=False))
    return clauses


def simplify_full_fixed_root() -> list[tuple[int, ...]]:
    """Independently simplify ``encode(25,5,4)`` under the root units."""
    root_values = {vertex: (vertex >= 9) for vertex in range(1, 25)}
    reduced: list[tuple[int, ...]] = []
    for vertices, positive in itertools.chain(
        ((vs, False) for vs in itertools.combinations(range(25), 5)),
        ((vs, True) for vs in itertools.combinations(range(25), 4)),
    ):
        satisfied = False
        clause: list[int] = []
        for left, right in itertools.combinations(vertices, 2):
            if left == 0:
                value = root_values[right]
                if value == positive:
                    satisfied = True
                    break
                continue
            sign = 1 if positive else -1
            clause.append(sign * edge_var(24, left - 1, right - 1))
        if not satisfied:
            reduced.append(tuple(clause))
    return reduced


def has_clique(edges: Sequence[int], order: int, size: int, colour: int) -> bool:
    index = {pair: i for i, pair in enumerate(cover.edge_pairs(order))}
    for vertices in itertools.combinations(range(order), size):
        if all(edges[index[(i, j)]] == colour for i, j in itertools.combinations(vertices, 2)):
            return True
    return False


def iter_records(path: Path, order: int):
    with path.open("rb") as stream:
        for record_index, raw_line in enumerate(stream):
            fields = raw_line.strip().decode("ascii").split()
            parent_id = int(fields[0], 10)
            parent_edges = cover.decode_edges(parent_id, order, f"{path}:{record_index + 1}:parent")
            yield record_index, parent_id, parent_edges, fields[1:]


def audit_child_ramsey_semantics(path: Path, order: int, blue_size: int, red_size: int) -> int:
    checked = 0
    for record_index, _parent_id, _parent_edges, tokens in iter_records(path, order):
        for child_number, token in enumerate(tokens, 1):
            child_id, _permutation = cover.parse_child_token(
                token, order, f"{path}:{record_index + 1}:child#{child_number}"
            )
            edges = cover.decode_edges(child_id, order, f"{path}:child:{child_id}")
            if has_clique(edges, order, blue_size, colour=1):
                raise RuntimeError(f"{path}: child {child_id} contains a blue K{blue_size}")
            if has_clique(edges, order, red_size, colour=2):
                raise RuntimeError(f"{path}: child {child_id} contains a red K{red_size}")
            checked += 1
    return checked


def block_literals(edges: Sequence[int], local_order: int, offset: int) -> list[int]:
    literals: list[int] = []
    for colour, (local_left, local_right) in zip(edges, cover.edge_pairs(local_order)):
        if colour == 0:
            continue
        variable = edge_var(24, local_left + offset, local_right + offset)
        if colour == 1:
            literals.append(-variable)
        elif colour == 2:
            literals.append(variable)
        else:
            raise RuntimeError(f"unexpected HOL4 colour {colour}")
    return sorted(literals, key=abs)


def clause_falsified_by_units(clause: Sequence[int], units: set[int]) -> bool:
    return all(-literal in units for literal in clause)


def audit_and_generate() -> dict:
    HERE.mkdir(parents=True, exist_ok=True)
    stats35 = cover.check_cover(GEN35)
    stats44 = cover.check_cover(GEN44)
    if (stats35.records, stats44.records) != (27, 2):
        raise RuntimeError(f"unexpected parent counts {(stats35.records, stats44.records)}")

    # Validate the local Python indexing against this script for every edge.
    mapping_mismatches = []
    for order in (24, 25):
        for left, right in itertools.combinations(range(order), 2):
            ours = edge_var(order, left, right)
            theirs = local_ramsey.edge_var(order, left, right)
            if ours != theirs:
                mapping_mismatches.append((order, left, right, ours, theirs))
    if mapping_mismatches:
        raise RuntimeError(f"edge-variable mapping mismatch: {mapping_mismatches[:3]}")

    expected = reduced_fixed_root_clauses()
    independently_reduced = simplify_full_fixed_root()
    if Counter(expected) != Counter(independently_reduced):
        missing = Counter(expected) - Counter(independently_reduced)
        extra = Counter(independently_reduced) - Counter(expected)
        raise RuntimeError(
            f"fixed-root reduction mismatch: {sum(missing.values())} missing, "
            f"{sum(extra.values())} extra"
        )

    child35 = audit_child_ramsey_semantics(GEN35, 8, blue_size=3, red_size=5)
    child44 = audit_child_ramsey_semantics(GEN44, 16, blue_size=4, red_size=4)

    base_path = HERE / "fixed_root_d8_base.cnf"
    with base_path.open("w", encoding="ascii", newline="\n") as output:
        output.write(f"p cnf {24 * 23 // 2} {len(expected)}\n")
        for clause in expected:
            output.write(" ".join(map(str, clause)) + " 0\n")

    parents35 = list(iter_records(GEN35, 8))
    parents44 = list(iter_records(GEN44, 16))
    leaves = []
    for left_index, left_id, left_edges, _ in parents35:
        for right_index, right_id, right_edges, _ in parents44:
            units = block_literals(left_edges, 8, 0) + block_literals(right_edges, 16, 8)
            if len({abs(lit) for lit in units}) != len(units):
                raise RuntimeError(f"duplicate or contradictory unit in leaf {left_index},{right_index}")
            unit_set = set(units)
            immediately_falsified = sum(
                clause_falsified_by_units(clause, unit_set) for clause in expected
            )
            cube_line = "a " + " ".join(map(str, units)) + " 0\n"
            leaves.append(
                {
                    "leaf": f"d8_l{left_index:02d}_r{right_index:02d}",
                    "left_record_zero_based": left_index,
                    "right_record_zero_based": right_index,
                    "gen358_parent_id": str(left_id),
                    "gen4416_parent_id": str(right_id),
                    "fixed_literals": len(units),
                    "left_parent_holes": left_edges.count(0),
                    "right_parent_holes": right_edges.count(0),
                    "immediately_falsified_base_clauses": immediately_falsified,
                    "cube": units,
                    "cube_line_sha256": sha256_bytes(cube_line.encode("ascii")),
                }
            )
    if len(leaves) != 54:
        raise RuntimeError(f"expected 54 leaves, generated {len(leaves)}")

    cubes_path = HERE / "cubes.jsonl"
    with cubes_path.open("w", encoding="utf-8", newline="\n") as output:
        for leaf in leaves:
            output.write(json.dumps(leaf, sort_keys=True) + "\n")

    audit = {
        "status": "PASS",
        "scope_warning": (
            "This checks file structure, child Ramsey-freeness, encoding semantics, "
            "and bounded SAT leaves; it does not re-prove HOL4 cover completeness."
        ),
        "colour_mapping": {
            "HOL4_1": "blue = DIMACS false/negative",
            "HOL4_2": "red = DIMACS true/positive",
            "local_Lean_formula": "encode(25,5,4) fixed at root; reduced to 24 non-root vertices",
        },
        "cover_stats": [asdict(stats35), asdict(stats44)],
        "child_semantics": {
            "gen358_children_checked_no_blue_K3_no_red_K5": child35,
            "gen4416_children_checked_no_blue_K4_no_red_K4": child44,
        },
        "edge_mapping_pairs_checked": 24 * 23 // 2 + 25 * 24 // 2,
        "fixed_root_clause_comparison": {
            "full_formula": "encode(25,5,4) with root edges 1..8 blue and 9..24 red",
            "reduced_formula": (
                "encode(24,5,4) + no-blue-K3(left 8) + no-red-K4(right 16)"
            ),
            "full_clauses_before_units": 65780,
            "reduced_clauses": len(expected),
            "counter_equality": True,
            "breakdown": {
                "global_no_red_K5": 42504,
                "global_no_blue_K4": 10626,
                "left_no_blue_K3": 56,
                "right_no_red_K4": 1820,
            },
        },
        "base_cnf": str(base_path),
        "base_cnf_sha256": sha256_file(base_path),
        "base_variables": 276,
        "base_clauses": len(expected),
        "cubes": str(cubes_path),
        "cubes_sha256": sha256_file(cubes_path),
        "leaves": len(leaves),
    }
    audit_path = HERE / "audit.json"
    audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return audit


def read_cubes() -> list[dict]:
    path = HERE / "cubes.jsonl"
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def parse_solver_output(output: str, returncode: int, timed_out: bool) -> tuple[str, int | None, float | None]:
    if timed_out:
        status = "TIMEOUT"
    elif re.search(r"^s UNSATISFIABLE\s*$", output, re.MULTILINE) or returncode == 20:
        status = "UNSAT"
    elif re.search(r"^s SATISFIABLE\s*$", output, re.MULTILINE) or returncode == 10:
        status = "SAT"
    else:
        status = "UNKNOWN"
    conflict_matches = re.findall(r"^c\s+conflicts:\s*([0-9]+)", output, re.MULTILINE)
    time_matches = re.findall(
        r"^c\s+(?:total process time since initialization|process-time):\s*([0-9.]+)",
        output,
        re.MULTILINE,
    )
    conflicts = int(conflict_matches[-1]) if conflict_matches else None
    solver_seconds = float(time_matches[-1]) if time_matches else None
    return status, conflicts, solver_seconds


def solve_one(
    solver: Path,
    base_body: str,
    base_clause_count: int,
    leaf: dict,
    conflict_limit: int,
    timeout_seconds: float,
    run_dir: Path,
    keep_cnfs: bool,
) -> dict:
    leaf_path = run_dir / f"{leaf['leaf']}.cnf"
    units = leaf["cube"]
    with leaf_path.open("w", encoding="ascii", newline="\n") as output:
        output.write(f"p cnf 276 {base_clause_count + len(units)}\n")
        output.write(base_body)
        for literal in units:
            output.write(f"{literal} 0\n")
    leaf_hash = sha256_file(leaf_path)
    command = [
        str(solver),
        "--stats",
        "--no-witness",
        "--no-colors",
        "--unsat",
        "-c",
        str(conflict_limit),
        str(leaf_path),
    ]
    started = time.perf_counter()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_seconds,
            check=False,
        )
        output_text = completed.stdout
        returncode = completed.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        partial = exc.stdout or ""
        output_text = partial.decode("utf-8", "replace") if isinstance(partial, bytes) else partial
        returncode = -1
    wall_seconds = time.perf_counter() - started
    status, conflicts, solver_seconds = parse_solver_output(output_text, returncode, timed_out)
    log_path = run_dir / f"{leaf['leaf']}.log"
    log_path.write_text(output_text, encoding="utf-8")
    if not keep_cnfs:
        leaf_path.unlink(missing_ok=True)
    return {
        **{key: value for key, value in leaf.items() if key != "cube"},
        "status": status,
        "returncode": returncode,
        "conflict_limit": conflict_limit,
        "conflicts": conflicts,
        "timeout_seconds": timeout_seconds,
        "wall_seconds": wall_seconds,
        "solver_seconds": solver_seconds,
        "leaf_cnf_sha256": leaf_hash,
        "command": command,
        "log": str(log_path),
    }


def solve(args: argparse.Namespace) -> dict:
    audit = audit_and_generate()
    solver = args.solver.resolve()
    if not solver.is_file():
        raise RuntimeError(f"solver not found: {solver}")
    version = subprocess.run(
        [str(solver), "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()
    base_lines = (HERE / "fixed_root_d8_base.cnf").read_text(encoding="ascii").splitlines(True)
    base_body = "".join(base_lines[1:])
    cubes = read_cubes()
    if args.only:
        wanted = set(args.only)
        cubes = [cube for cube in cubes if cube["leaf"] in wanted]
        missing = wanted - {cube["leaf"] for cube in cubes}
        if missing:
            raise RuntimeError(f"unknown leaf names: {sorted(missing)}")

    run_name = f"c{args.conflicts}_t{int(args.timeout)}_j{args.jobs}"
    run_dir = HERE / "runs" / run_name
    run_dir.mkdir(parents=True, exist_ok=True)
    results = []
    started = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {
            pool.submit(
                solve_one,
                solver,
                base_body,
                audit["base_clauses"],
                leaf,
                args.conflicts,
                args.timeout,
                run_dir,
                args.keep_cnfs,
            ): leaf["leaf"]
            for leaf in cubes
        }
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            print(
                f"{result['leaf']}: {result['status']} "
                f"conflicts={result['conflicts']} wall={result['wall_seconds']:.3f}s",
                flush=True,
            )
    elapsed = time.perf_counter() - started
    results.sort(key=lambda item: item["leaf"])
    counts = Counter(item["status"] for item in results)
    summary = {
        "status_counts": dict(sorted(counts.items())),
        "solver": str(solver),
        "solver_version": version,
        "jobs": args.jobs,
        "conflict_limit_per_leaf": args.conflicts,
        "timeout_seconds_per_leaf": args.timeout,
        "total_wall_seconds": elapsed,
        "leaves_run": len(results),
        "results": results,
    }
    json_path = run_dir / "results.json"
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    csv_path = run_dir / "results.csv"
    fields = [
        "leaf",
        "status",
        "conflicts",
        "wall_seconds",
        "solver_seconds",
        "fixed_literals",
        "left_parent_holes",
        "right_parent_holes",
        "gen358_parent_id",
        "gen4416_parent_id",
        "leaf_cnf_sha256",
    ]
    with csv_path.open("w", encoding="utf-8", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(results)
    print(json.dumps({key: value for key, value in summary.items() if key != "results"}, indent=2))
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    generate = subparsers.add_parser("generate", help="audit inputs and emit base/cubes")
    generate.set_defaults(func=lambda _args: print(json.dumps(audit_and_generate(), indent=2)))
    run = subparsers.add_parser("solve", help="run bounded CaDiCaL leaves")
    run.add_argument("--solver", type=Path, required=True)
    run.add_argument("--conflicts", type=int, default=200_000)
    run.add_argument("--timeout", type=float, default=60.0)
    run.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    run.add_argument("--keep-cnfs", action="store_true")
    run.add_argument("--only", nargs="*", help="optional exact leaf names")
    run.set_defaults(func=solve)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        args.func(args)
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
