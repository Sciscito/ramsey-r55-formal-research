#!/usr/bin/env python3
"""Run one named direct-orientation leaf with explicit CaDiCaL limits."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
PILOT = HERE / "run_direct_pilot.py"


def load_pilot():
    spec = importlib.util.spec_from_file_location("direct_pilot", PILOT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {PILOT}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("leaf")
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--conflicts", type=int, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--keep-cnf", action="store_true")
    args = parser.parse_args()
    pilot = load_pilot()
    audit = pilot.audit_and_generate()
    matches = [leaf for leaf in pilot.load_leaves() if leaf["leaf"] == args.leaf]
    if len(matches) != 1:
        parser.error(f"unknown or duplicated leaf {args.leaf!r}")
    base_lines = Path(audit["base"]).read_text(encoding="ascii").splitlines(True)
    run_dir = (
        pilot.OUT / "runs" /
        f"single_{args.leaf}_c{args.conflicts}_t{int(args.timeout)}"
    )
    run_dir.mkdir(parents=True, exist_ok=True)
    result = pilot.helper.solve_one(
        args.solver.resolve(),
        "".join(base_lines[1:]),
        audit["base_clauses"],
        matches[0],
        args.conflicts,
        args.timeout,
        run_dir,
        args.keep_cnf,
    )
    output = {"leaf_run": result}
    (run_dir / "results.json").write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
