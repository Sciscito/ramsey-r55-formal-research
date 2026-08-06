#!/usr/bin/env python3
"""Direct-Lean orientation of the bounded 54-leaf degree-eight pilot.

This is the authoritative runner for this scratch experiment.  It maps HOL4
blue to Lean red, so it connects directly to the local ``encode(25,4,5)``
theorem with a root of red degree eight.  Before emitting any leaf it checks
that both the fixed-root formula and every parent literal are exact Boolean
complements of the original HOL4 orientation.

This is a bounded SAT experiment, not a proof of cover completeness.
"""

from __future__ import annotations

import argparse
import csv
import importlib.util
import itertools
import json
import os
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Iterator, Sequence


HERE = Path(__file__).resolve().parent
OUT = HERE / "direct_lean_orientation"
LEGACY_PATH = HERE / "run_pilot.py"


def load_legacy():
    spec = importlib.util.spec_from_file_location("r45_d8_pilot_helpers", LEGACY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {LEGACY_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


helper = load_legacy()


def direct_clauses() -> list[tuple[int, ...]]:
    """Reduced fixed-root ``encode(25,4,5)`` on the 24 non-root vertices."""
    clauses = list(helper.ramsey_clauses(24, red_size=4, blue_size=5))
    for vertices in itertools.combinations(range(8), 3):
        clauses.append(helper.clique_clause(24, vertices, positive=False))
    for vertices in itertools.combinations(range(8, 24), 4):
        clauses.append(helper.clique_clause(24, vertices, positive=True))
    return clauses


def simplify_full_direct() -> list[tuple[int, ...]]:
    """Independently eliminate the fixed root from ``encode(25,4,5)``."""
    root_value = {vertex: vertex <= 8 for vertex in range(1, 25)}
    reduced: list[tuple[int, ...]] = []
    streams = itertools.chain(
        ((vertices, False) for vertices in itertools.combinations(range(25), 4)),
        ((vertices, True) for vertices in itertools.combinations(range(25), 5)),
    )
    for vertices, positive in streams:
        satisfied = False
        clause: list[int] = []
        for left, right in itertools.combinations(vertices, 2):
            if left == 0:
                if root_value[right] == positive:
                    satisfied = True
                    break
                continue
            sign = 1 if positive else -1
            clause.append(sign * helper.edge_var(24, left - 1, right - 1))
        if not satisfied:
            reduced.append(tuple(clause))
    return reduced


def direct_block_literals(edges: Sequence[int], order: int, offset: int) -> list[int]:
    """HOL blue(1)->Lean true; HOL red(2)->Lean false."""
    literals: list[int] = []
    for colour, (left, right) in zip(edges, helper.cover.edge_pairs(order)):
        if colour == 0:
            continue
        variable = helper.edge_var(24, left + offset, right + offset)
        if colour == 1:
            literals.append(variable)
        elif colour == 2:
            literals.append(-variable)
        else:
            raise RuntimeError(f"unexpected HOL4 colour {colour}")
    return sorted(literals, key=abs)


def audit_and_generate() -> dict:
    OUT.mkdir(parents=True, exist_ok=True)
    stats35 = helper.cover.check_cover(helper.GEN35)
    stats44 = helper.cover.check_cover(helper.GEN44)
    if (stats35.records, stats44.records) != (27, 2):
        raise RuntimeError("cover record counts are not 27 x 2")

    expected = direct_clauses()
    if Counter(expected) != Counter(simplify_full_direct()):
        raise RuntimeError("direct reduced formula differs from fixed-root encode(25,4,5)")

    hol = helper.reduced_fixed_root_clauses()
    complemented_hol = [tuple(-literal for literal in clause) for clause in hol]
    if Counter(expected) != Counter(complemented_hol):
        raise RuntimeError("direct formula is not the clause-wise complement of HOL orientation")

    # Check the variable formula against the local Python/Lean bridge on every edge.
    mapping_checks = 0
    for order in (24, 25):
        for left, right in itertools.combinations(range(order), 2):
            if helper.edge_var(order, left, right) != helper.local_ramsey.edge_var(order, left, right):
                raise RuntimeError(f"edge mapping mismatch at K{order} ({left},{right})")
            mapping_checks += 1

    child35 = helper.audit_child_ramsey_semantics(helper.GEN35, 8, 3, 5)
    child44 = helper.audit_child_ramsey_semantics(helper.GEN44, 16, 4, 4)
    left_records = list(helper.iter_records(helper.GEN35, 8))
    right_records = list(helper.iter_records(helper.GEN44, 16))

    base = OUT / "fixed_root_d8_encode_24_4_5.cnf"
    with base.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"p cnf 276 {len(expected)}\n")
        for clause in expected:
            stream.write(" ".join(map(str, clause)) + " 0\n")

    leaves: list[dict] = []
    for li, left_id, left_edges, _left_children in left_records:
        for ri, right_id, right_edges, _right_children in right_records:
            direct = direct_block_literals(left_edges, 8, 0)
            direct += direct_block_literals(right_edges, 16, 8)
            unswapped = helper.block_literals(left_edges, 8, 0)
            unswapped += helper.block_literals(right_edges, 16, 8)
            if direct != [-literal for literal in unswapped]:
                raise RuntimeError(f"cube complement mismatch at ({li},{ri})")
            if len({abs(literal) for literal in direct}) != len(direct):
                raise RuntimeError(f"duplicate cube variable at ({li},{ri})")
            unit_set = set(direct)
            leaves.append(
                {
                    "leaf": f"d8_l{li:02d}_r{ri:02d}",
                    "left_record_zero_based": li,
                    "right_record_zero_based": ri,
                    "gen358_parent_id": str(left_id),
                    "gen4416_parent_id": str(right_id),
                    "fixed_literals": len(direct),
                    "left_parent_holes": left_edges.count(0),
                    "right_parent_holes": right_edges.count(0),
                    "immediately_falsified_base_clauses": sum(
                        helper.clause_falsified_by_units(clause, unit_set)
                        for clause in expected
                    ),
                    "cube": direct,
                }
            )
    if len(leaves) != 54:
        raise RuntimeError(f"generated {len(leaves)} leaves instead of 54")
    cubes = OUT / "cubes.jsonl"
    with cubes.open("w", encoding="utf-8", newline="\n") as stream:
        for leaf in leaves:
            stream.write(json.dumps(leaf, sort_keys=True) + "\n")

    audit = {
        "status": "PASS",
        "scope": "bounded SAT pilot; no independent proof of HOL4 cover completeness",
        "orientation": {
            "HOL_blue_1": "Lean red / DIMACS positive",
            "HOL_red_2": "Lean blue / DIMACS negative",
            "formula": "encode(24,4,5) + no-red-K3(left8) + no-blue-K4(right16)",
            "full_fixed_root": "encode(25,4,5), root red to vertices 1..8 and blue to 9..24",
        },
        "checks": {
            "fixed_root_reduction_clause_counter_equal": True,
            "HOL_orientation_literal_complement_clause_counter_equal": True,
            "all_54_cubes_literal_complements": True,
            "edge_mapping_checks": mapping_checks,
            "gen358_children_no_HOL_blue_K3_no_HOL_red_K5": child35,
            "gen4416_children_no_monochromatic_K4": child44,
        },
        "cover_hashes": {
            "gen358": helper.sha256_file(helper.GEN35),
            "gen4416": helper.sha256_file(helper.GEN44),
        },
        "base": str(base),
        "base_sha256": helper.sha256_file(base),
        "base_variables": 276,
        "base_clauses": len(expected),
        "base_breakdown": {
            "global_no_red_K4": 10626,
            "global_no_blue_K5": 42504,
            "left_no_red_K3": 56,
            "right_no_blue_K4": 1820,
        },
        "cubes": str(cubes),
        "cubes_sha256": helper.sha256_file(cubes),
        "leaves": len(leaves),
    }
    (OUT / "audit.json").write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return audit


def load_leaves() -> list[dict]:
    return [
        json.loads(line)
        for line in (OUT / "cubes.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]


def run(args: argparse.Namespace) -> dict:
    audit = audit_and_generate()
    solver = args.solver.resolve()
    if not solver.is_file():
        raise RuntimeError(f"solver not found: {solver}")
    version = subprocess.run(
        [str(solver), "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()
    base_lines = Path(audit["base"]).read_text(encoding="ascii").splitlines(True)
    base_body = "".join(base_lines[1:])
    leaves = load_leaves()
    if args.smoke:
        leaves = leaves[:1]
    run_name = (
        f"{'smoke_' if args.smoke else ''}c{args.conflicts}_t{int(args.timeout)}_j{args.jobs}"
    )
    run_dir = OUT / "runs" / run_name
    run_dir.mkdir(parents=True, exist_ok=True)
    results: list[dict] = []
    started = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {
            pool.submit(
                helper.solve_one,
                solver,
                base_body,
                audit["base_clauses"],
                leaf,
                args.conflicts,
                args.timeout,
                run_dir,
                args.keep_cnfs,
            ): leaf["leaf"]
            for leaf in leaves
        }
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            print(
                f"{result['leaf']}: {result['status']} conflicts={result['conflicts']} "
                f"wall={result['wall_seconds']:.3f}s",
                flush=True,
            )
    results.sort(key=lambda result: result["leaf"])
    summary = {
        "solver": str(solver),
        "solver_version": version,
        "conflict_limit_per_leaf": args.conflicts,
        "timeout_seconds_per_leaf": args.timeout,
        "jobs": args.jobs,
        "leaves_run": len(results),
        "status_counts": dict(sorted(Counter(r["status"] for r in results).items())),
        "total_wall_seconds": time.perf_counter() - started,
        "results": results,
    }
    (run_dir / "results.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    fields = [
        "leaf", "status", "conflicts", "wall_seconds", "solver_seconds",
        "fixed_literals", "left_parent_holes", "right_parent_holes",
        "gen358_parent_id", "gen4416_parent_id", "leaf_cnf_sha256",
    ]
    with (run_dir / "results.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(results)
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=2))
    return summary


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("generate")
    generate.set_defaults(func=lambda _args: print(json.dumps(audit_and_generate(), indent=2)))
    for name, smoke in (("smoke", True), ("solve", False)):
        command = commands.add_parser(name)
        command.add_argument("--solver", type=Path, required=True)
        command.add_argument("--conflicts", type=int, default=200_000)
        command.add_argument("--timeout", type=float, default=60.0)
        command.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
        command.add_argument("--keep-cnfs", action="store_true")
        command.set_defaults(func=run, smoke=smoke)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        args.func(args)
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
