#!/usr/bin/env python3
"""Bounded conditioned-cover experiments for the degree-twelve branch.

The fixed type-A leaf is strengthened by one partial ``gen4412`` parent on
the twelve B vertices.  This is initially a proof-free search experiment.
All CNFs, logs, JSON reports, and optional LRAT files are required to live
below an explicit absolute ``S:`` path.

Colour and edge conventions are deliberately explicit. The CLI requires one
of two orientations: ``raw`` maps HOL blue 1 to DIMACS negative and HOL red 2
to DIMACS positive; ``complemented`` maps HOL 1 to positive and HOL 2 to
negative. The core-24 artifacts were discovered in the complemented
orientation. It can be composed either by interpreting catalogue colour 1 as
simple-graph adjacency in a direct R(4,4) classification theorem, or by an
explicit complement transport from the physical HOL colour names. One of
those bridges remains a formal obligation.

In both orientations, ``gen4412`` is decoded in the upper-triangle order used
by ``graph.sml``; a hole contributes no unit; and local B vertex ``i`` maps to
global non-root vertex ``12 + i`` in K_24.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import random
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path, PureWindowsPath
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
COVER_CHECKER_PATH = REPOSITORY / "scripts" / "r45_d8_pilot" / "check_barakeel_covers.py"
RAMSEY_PATH = REPOSITORY / "r55" / "ramsey.py"

ORDER = 24
B_OFFSET = 12
B_ORDER = 12
BASE_VARIABLES = 276
EXPECTED_BASE_CLAUSES = 53_911
ORIENTATIONS = ("raw", "complemented")

Clause = tuple[int, ...]


class ProbeError(RuntimeError):
    """Raised when an input or solver result is unsuitable for the probe."""


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ProbeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


cover = load_module("r45_d12_conditioned_cover_checker", COVER_CHECKER_PATH)
ramsey = load_module("r45_d12_conditioned_ramsey", RAMSEY_PATH)


def require_absolute_ssd(path: Path) -> Path:
    windows = PureWindowsPath(str(path))
    if windows.drive.upper() != "S:" or not windows.is_absolute():
        raise ValueError(f"path must be an explicit absolute S: path, got {path}")
    return path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_new_bytes(path: Path, data: bytes) -> None:
    require_absolute_ssd(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".partial")
    temporary.write_bytes(data)
    if path.exists():
        if sha256_file(path) == sha256_file(temporary):
            temporary.unlink()
            return
        temporary.unlink()
        raise FileExistsError(f"refusing to overwrite differing file {path}")
    temporary.replace(path)


def parse_parent_specification(specification: str) -> tuple[int, ...]:
    selected: set[int] = set()
    for item in specification.split(","):
        item = item.strip()
        if not item:
            continue
        if "-" in item:
            first_text, last_text = item.split("-", 1)
            first, last = int(first_text), int(last_text)
            if first < 1 or last < first:
                raise ValueError(f"invalid parent range {item!r}")
            selected.update(range(first, last + 1))
        else:
            index = int(item)
            if index < 1:
                raise ValueError("parent indices are one-based and positive")
            selected.add(index)
    if not selected:
        raise ValueError("empty parent selection")
    return tuple(sorted(selected))


@dataclass(frozen=True)
class ParentRecord:
    index: int
    encoded: int
    colours: tuple[int, ...]
    child_count: int

    @property
    def holes(self) -> int:
        return self.colours.count(0)


def read_parent(path: Path, one_based_index: int) -> ParentRecord:
    """Read and structurally audit one official gen4412 record."""
    if one_based_index < 1:
        raise ValueError("parent index must be positive")
    with path.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            if line_number != one_based_index:
                continue
            try:
                fields = raw_line.strip().decode("ascii").split()
            except UnicodeDecodeError as exc:
                raise ProbeError(f"{path}:{line_number}: non-ASCII record") from exc
            if len(fields) < 2:
                raise ProbeError(f"{path}:{line_number}: parent has no children")
            encoded = int(fields[0], 10)
            colours = tuple(
                cover.decode_edges(encoded, B_ORDER, f"{path}:{line_number}:parent")
            )
            pairs = cover.edge_pairs(B_ORDER)
            pair_index = [[-1] * B_ORDER for _ in range(B_ORDER)]
            for edge_index, (left, right) in enumerate(pairs):
                pair_index[left][right] = edge_index
            # Checking every listed child catches wrong ternary digit order and
            # wrong interpretation of the stored canonicalisation permutation.
            for child_number, token in enumerate(fields[1:], 1):
                context = f"{path}:{line_number}:child#{child_number}"
                child_id, permutation = cover.parse_child_token(
                    token, B_ORDER, context
                )
                child_colours = cover.decode_edges(child_id, B_ORDER, context)
                if 0 in child_colours:
                    raise ProbeError(f"{context}: child unexpectedly has a hole")
                cover.check_parent_child_agreement(
                    list(colours), child_colours, permutation, pairs, pair_index, context
                )
            return ParentRecord(
                index=one_based_index,
                encoded=encoded,
                colours=colours,
                child_count=len(fields) - 1,
            )
    raise ProbeError(f"{path}: no parent record {one_based_index}")


def parent_units(colours: Sequence[int], orientation: str) -> tuple[int, ...]:
    if len(colours) != B_ORDER * (B_ORDER - 1) // 2:
        raise ValueError("a gen4412 parent must have 66 ternary edge colours")
    units: list[int] = []
    for colour, (local_left, local_right) in zip(
        colours, cover.edge_pairs(B_ORDER), strict=True
    ):
        if colour == 0:
            continue
        variable = ramsey.edge_var(
            ORDER, B_OFFSET + local_left, B_OFFSET + local_right
        )
        if orientation not in ORIENTATIONS:
            raise ValueError(f"unknown catalogue orientation {orientation!r}")
        if colour == 1:
            units.append(variable if orientation == "complemented" else -variable)
        elif colour == 2:
            units.append(-variable if orientation == "complemented" else variable)
        else:
            raise ProbeError(f"unexpected HOL colour {colour}")
    if len(set(map(abs, units))) != len(units):
        raise ProbeError("parent units contain a repeated DIMACS variable")
    if any(not 211 <= abs(literal) <= 276 for literal in units):
        raise ProbeError("a parent unit escaped the B-B edge interval 211..276")
    return tuple(sorted(units, key=abs))


def cnf_header(path: Path) -> tuple[int, int]:
    found: tuple[int, int] | None = None
    with path.open("r", encoding="ascii") as stream:
        for line_number, line in enumerate(stream, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith("c"):
                continue
            fields = stripped.split()
            if fields[0] == "p":
                if found is not None or fields[:2] != ["p", "cnf"] or len(fields) != 4:
                    raise ProbeError(f"invalid DIMACS header at {path}:{line_number}")
                found = (int(fields[2]), int(fields[3]))
                continue
            if found is None:
                raise ProbeError(f"clause before DIMACS header at {path}:{line_number}")
    if found is None:
        raise ProbeError(f"missing DIMACS header in {path}")
    return found


def conditioned_cnf_bytes(source: Path, units: Sequence[int]) -> bytes:
    variables, clauses = cnf_header(source)
    if (variables, clauses) != (BASE_VARIABLES, EXPECTED_BASE_CLAUSES):
        raise ProbeError(
            f"expected the frozen d12 leaf header "
            f"{BASE_VARIABLES}/{EXPECTED_BASE_CLAUSES}, got {variables}/{clauses}"
        )
    if len(set(map(abs, units))) != len(units):
        raise ProbeError("conditioned cube repeats a variable")
    if any(literal == 0 or abs(literal) > variables for literal in units):
        raise ProbeError("conditioned cube contains an invalid literal")
    source_data = source.read_bytes()
    replacement = f"p cnf {variables} {clauses + len(units)}\n".encode("ascii")
    rendered, replacements = re.subn(
        rb"(?m)^p cnf [0-9]+ [0-9]+\r?$", replacement.rstrip(b"\n"), source_data
    )
    if replacements != 1:
        raise ProbeError(f"expected one DIMACS header replacement, got {replacements}")
    if not rendered.endswith(b"\n"):
        rendered += b"\n"
    rendered += b"".join(f"{literal} 0\n".encode("ascii") for literal in units)
    return rendered


def write_conditioned_cnf(source: Path, target: Path, units: Sequence[int]) -> None:
    write_new_bytes(target, conditioned_cnf_bytes(source, units))


def parse_solver_output(output: str, returncode: int | None) -> tuple[str, int | None, float | None]:
    if returncode == 20 or re.search(r"^s UNSATISFIABLE\s*$", output, re.MULTILINE):
        status = "UNSAT"
    elif returncode == 10 or re.search(r"^s SATISFIABLE\s*$", output, re.MULTILINE):
        status = "SAT"
    else:
        status = "UNKNOWN"
    conflicts = re.findall(r"^c conflicts:\s+([0-9]+)", output, re.MULTILINE)
    seconds = re.findall(
        r"^c total process time since initialization:\s+([0-9.]+)",
        output,
        re.MULTILINE,
    )
    return (
        status,
        int(conflicts[-1]) if conflicts else None,
        float(seconds[-1]) if seconds else None,
    )


def solve(
    solver: Path,
    cnf: Path,
    *,
    conflict_limit: int,
    timeout_seconds: float,
    proof: Path | None = None,
    log: Path | None = None,
) -> dict[str, object]:
    if conflict_limit < 1 or timeout_seconds <= 0:
        raise ValueError("solver limits must be positive")
    if proof is not None:
        require_absolute_ssd(proof)
    if log is not None:
        require_absolute_ssd(log)
    command = [str(solver)]
    if proof is None:
        command.extend(["--unsat", "--walk=false", "-n"])
    else:
        command.extend(["--lrat", "--no-binary", "--unsat", "--walk=false"])
    command.extend(["-c", str(conflict_limit), str(cnf)])
    proof_partial: Path | None = None
    if proof is not None:
        proof.parent.mkdir(parents=True, exist_ok=True)
        proof_partial = proof.with_name(proof.name + ".partial")
        if proof.exists() or proof_partial.exists():
            raise FileExistsError(f"refusing to overwrite proof path {proof}")
        command.append(str(proof_partial))
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
        output = completed.stdout
        returncode: int | None = completed.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        raw_output = exc.stdout or ""
        output = raw_output if isinstance(raw_output, str) else raw_output.decode("utf-8", "replace")
        returncode = None
    wall_seconds = time.perf_counter() - started
    status, conflicts, solver_seconds = parse_solver_output(output, returncode)
    if timed_out:
        status = "TIMEOUT"
    if log is not None:
        write_new_bytes(log, output.encode("utf-8"))
    proof_result: dict[str, object] | None = None
    if proof_partial is not None:
        if status == "UNSAT" and proof_partial.is_file() and proof_partial.stat().st_size > 0:
            proof_partial.replace(proof)
            proof_result = {
                "path": str(proof),
                "bytes": proof.stat().st_size,
                "sha256": sha256_file(proof),
            }
        elif proof_partial.exists():
            proof_partial.unlink()
    return {
        "status": status,
        "conflicts": conflicts,
        "wall_seconds": round(wall_seconds, 3),
        "solver_seconds": solver_seconds,
        "returncode": returncode,
        "command_flags": command[1:-1] if proof is None else command[1:-2],
        "proof": proof_result,
    }


def parent_manifest(
    record: ParentRecord, units: Sequence[int], orientation: str
) -> dict[str, object]:
    return {
        "parent_index_one_based": record.index,
        "parent_encoded": str(record.encoded),
        "parent_children_checked": record.child_count,
        "parent_holes": record.holes,
        "fixed_B_units": len(units),
        "catalogue_orientation": orientation,
        "colour_convention": {
            "HOL_1_blue": (
                "DIMACS positive / complemented to red"
                if orientation == "complemented" else "DIMACS negative / raw blue"
            ),
            "HOL_2_red": (
                "DIMACS negative / complemented to blue"
                if orientation == "complemented" else "DIMACS positive / raw red"
            ),
            "HOL_0": "hole / no unit",
        },
        "edge_convention": "upper triangle lexicographic; local B i maps to global 12+i",
        "composition_note": (
            "use direct colour-1-as-adjacency R44 classification or explicit complement transport"
            if orientation == "complemented" else "physical HOL blue/red interpretation"
        ),
    }


def command_benchmark(args: argparse.Namespace) -> None:
    output = require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "benchmark.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    rows: list[dict[str, object]] = []
    for index in parse_parent_specification(args.parents):
        record = read_parent(args.cover, index)
        units = parent_units(record.colours, args.orientation)
        cnf = output / f"parent_{index:05d}.cnf"
        write_conditioned_cnf(args.input, cnf, units)
        result = solve(
            args.solver,
            cnf,
            conflict_limit=args.conflicts,
            timeout_seconds=args.timeout,
            log=output / f"parent_{index:05d}.log",
        )
        rows.append(
            {
                **parent_manifest(record, units, args.orientation),
                "cnf": {
                    "path": str(cnf),
                    "bytes": cnf.stat().st_size,
                    "sha256": sha256_file(cnf),
                    "clauses": EXPECTED_BASE_CLAUSES + len(units),
                },
                "solver": result,
            }
        )
        print(
            f"parent {index}: holes={record.holes}, units={len(units)}, "
            f"status={result['status']}, conflicts={result['conflicts']}, "
            f"wall={result['wall_seconds']}s",
            flush=True,
        )
    report = {
        "schema_version": 1,
        "status": "PROOF_FREE_CONDITIONED_SEARCH_PROBE",
        "scope": "d12 catalogue type A=0, selected official gen4412 parents on B",
        "warning": "selected labelled parents do not yet constitute a complete B cover",
        "input": {
            "path": str(args.input),
            "sha256": sha256_file(args.input),
        },
        "cover": {"path": str(args.cover), "sha256": sha256_file(args.cover)},
        "solver": str(args.solver),
        "conflict_limit": args.conflicts,
        "timeout_seconds": args.timeout,
        "rows": rows,
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps({
        "report": str(report_path),
        "status_counts": {
            status: sum(row["solver"]["status"] == status for row in rows)
            for status in ("UNSAT", "SAT", "UNKNOWN", "TIMEOUT")
        },
    }, indent=2, sort_keys=True))


def greedy_order(units: Sequence[int], mode: str) -> tuple[int, ...]:
    if mode == "ascending":
        return tuple(sorted(units, key=abs))
    if mode == "descending":
        return tuple(sorted(units, key=abs, reverse=True))
    if mode == "positive-first":
        return tuple(sorted(units, key=lambda literal: (literal < 0, abs(literal))))
    if mode == "negative-first":
        return tuple(sorted(units, key=lambda literal: (literal > 0, abs(literal))))
    raise ValueError(f"unknown greedy order {mode!r}")


def command_minimize(args: argparse.Namespace) -> None:
    output = require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "minimization.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    record = read_parent(args.cover, args.parent)
    complete_parent_units = parent_units(record.colours, args.orientation)
    original_units = (
        parse_units_file(args.start_units)
        if args.start_units is not None
        else complete_parent_units
    )
    if not set(original_units).issubset(set(complete_parent_units)):
        raise ProbeError("starting units are not a subset of the selected parent")
    retained = list(original_units)
    candidate_path = output / "candidate.cnf"

    def run_candidate(units: Sequence[int]) -> dict[str, object]:
        # This single scratch file intentionally turns over on S:, never C:.
        data = conditioned_cnf_bytes(args.input, units)
        temporary = candidate_path.with_name(candidate_path.name + ".partial")
        temporary.write_bytes(data)
        temporary.replace(candidate_path)
        return solve(
            args.solver,
            candidate_path,
            conflict_limit=args.conflicts,
            timeout_seconds=args.timeout,
        )

    baseline = run_candidate(retained)
    if baseline["status"] != "UNSAT":
        raise ProbeError(
            f"starting cube did not prove UNSAT under the requested limits: {baseline}"
        )
    attempts: list[dict[str, object]] = []
    for attempt, literal in enumerate(greedy_order(original_units, args.order), 1):
        if literal not in retained:
            continue
        trial = tuple(unit for unit in retained if unit != literal)
        result = run_candidate(trial)
        removed = result["status"] == "UNSAT"
        if removed:
            retained.remove(literal)
        row = {
            "attempt": attempt,
            "literal": literal,
            "removed": removed,
            "retained_after": len(retained),
            "solver": result,
        }
        attempts.append(row)
        print(
            f"attempt {attempt}/{len(original_units)} literal={literal}: "
            f"{result['status']} -> {'remove' if removed else 'keep'}; "
            f"retained={len(retained)}; wall={result['wall_seconds']}s",
            flush=True,
        )
    final_cnf = output / "minimal_conditioned.cnf"
    write_conditioned_cnf(args.input, final_cnf, retained)
    final_check = solve(
        args.solver,
        final_cnf,
        conflict_limit=args.final_conflicts,
        timeout_seconds=args.final_timeout,
        log=output / "minimal_conditioned.log",
    )
    if final_check["status"] != "UNSAT":
        raise ProbeError(f"final retained cube failed independent UNSAT check: {final_check}")
    units_path = output / "minimal_conditioned.units"
    write_new_bytes(
        units_path,
        (" ".join(map(str, retained)) + " 0\n").encode("ascii"),
    )
    report = {
        "schema_version": 1,
        "status": "BOUNDED_GREEDY_UNSAT_CUBE_DISCOVERED_NO_LRAT",
        "scope": "d12 catalogue type A=0 conditioned by one weakened gen4412 parent",
        "warning": "one UNSAT cube is not a complete cover; solver status is not a checked proof",
        "input": {"path": str(args.input), "sha256": sha256_file(args.input)},
        "cover": {"path": str(args.cover), "sha256": sha256_file(args.cover)},
        "parent": parent_manifest(record, complete_parent_units, args.orientation),
        "start_units_file": (
            {"path": str(args.start_units), "sha256": sha256_file(args.start_units)}
            if args.start_units is not None else None
        ),
        "greedy_order": args.order,
        "search_limits": {"conflicts": args.conflicts, "timeout_seconds": args.timeout},
        "baseline": baseline,
        "attempts": attempts,
        "original_unit_count": len(original_units),
        "retained_unit_count": len(retained),
        "removed_unit_count": len(original_units) - len(retained),
        "retained_units": retained,
        "final_check": final_check,
        "final_cnf": {
            "path": str(final_cnf),
            "bytes": final_cnf.stat().st_size,
            "sha256": sha256_file(final_cnf),
            "clauses": EXPECTED_BASE_CLAUSES + len(retained),
        },
        "units_file": {"path": str(units_path), "sha256": sha256_file(units_path)},
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps({
        "report": str(report_path),
        "original_units": len(original_units),
        "retained_units": len(retained),
        "removed_units": len(original_units) - len(retained),
        "final_status": final_check["status"],
        "final_conflicts": final_check["conflicts"],
        "final_cnf_sha256": sha256_file(final_cnf),
    }, indent=2, sort_keys=True))


def parse_units_file(path: Path) -> tuple[int, ...]:
    fields = path.read_text(encoding="ascii").split()
    values = tuple(int(field) for field in fields)
    if not values or values[-1] != 0 or values.count(0) != 1:
        raise ProbeError(f"malformed unit cube {path}")
    return values[:-1]


def extract_initial_unit_core(
    proof: Path,
    *,
    base_clause_count: int,
    units: Sequence[int],
) -> tuple[tuple[int, ...], dict[str, int]]:
    """Backward-trace an LRAT proof and return referenced appended units.

    Every absolute hint token is treated as a dependency. This is
    conservative for both RUP and RAT hint segments. The extracted set is
    subsequently re-solved, so this parser is a discovery accelerator and is
    not part of the trusted proof chain.
    """
    first_unit_id = base_clause_count + 1
    last_unit_id = base_clause_count + len(units)
    dependencies: dict[int, tuple[int, ...]] = {}
    addition_lines = 0
    deletion_lines = 0
    final_empty_id: int | None = None
    maximum_id = last_unit_id
    with proof.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            fields = raw_line.split()
            if not fields:
                continue
            try:
                clause_id = int(fields[0], 10)
            except ValueError as exc:
                raise ProbeError(f"{proof}:{line_number}: invalid clause ID") from exc
            maximum_id = max(maximum_id, clause_id)
            if len(fields) >= 2 and fields[1] == b"d":
                deletion_lines += 1
                continue
            try:
                first_zero = fields.index(b"0", 1)
            except ValueError as exc:
                raise ProbeError(
                    f"{proof}:{line_number}: addition has no clause terminator"
                ) from exc
            if first_zero == len(fields) - 1:
                raise ProbeError(f"{proof}:{line_number}: addition has no hint terminator")
            if fields[-1] != b"0":
                raise ProbeError(f"{proof}:{line_number}: addition has trailing data")
            try:
                hints = tuple(
                    abs(int(field, 10))
                    for field in fields[first_zero + 1 : -1]
                    if field != b"0"
                )
            except ValueError as exc:
                raise ProbeError(f"{proof}:{line_number}: non-integer LRAT hint") from exc
            dependencies[clause_id] = hints
            addition_lines += 1
            if first_zero == 1:
                final_empty_id = clause_id
    if final_empty_id is None:
        raise ProbeError(f"{proof}: no derived empty clause")

    needed_derived: set[int] = set()
    used_unit_ids: set[int] = set()
    stack = [final_empty_id]
    while stack:
        clause_id = stack.pop()
        if first_unit_id <= clause_id <= last_unit_id:
            used_unit_ids.add(clause_id)
            continue
        if clause_id <= base_clause_count or clause_id in needed_derived:
            continue
        needed_derived.add(clause_id)
        if clause_id not in dependencies:
            raise ProbeError(
                f"{proof}: reachable derived clause {clause_id} has no addition line"
            )
        stack.extend(dependencies[clause_id])
    core = tuple(
        literal
        for offset, literal in enumerate(units)
        if first_unit_id + offset in used_unit_ids
    )
    return core, {
        "addition_lines": addition_lines,
        "deletion_lines": deletion_lines,
        "maximum_clause_id": maximum_id,
        "final_empty_clause_id": final_empty_id,
        "reachable_derived_clauses": len(needed_derived),
        "referenced_appended_units": len(core),
    }


def command_core(args: argparse.Namespace) -> None:
    output = require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "core.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    record = read_parent(args.cover, args.parent)
    units = parent_units(record.colours, args.orientation)
    full_cnf = output / "full_parent.cnf"
    write_conditioned_cnf(args.input, full_cnf, units)
    full_result = solve(
        args.solver,
        full_cnf,
        conflict_limit=args.conflicts,
        timeout_seconds=args.timeout,
        proof=output / "full_parent.lrat",
        log=output / "full_parent.log",
    )
    if full_result["proof"] is None:
        raise ProbeError(f"full parent did not produce an UNSAT LRAT: {full_result}")
    proof_path = output / "full_parent.lrat"
    core, extraction = extract_initial_unit_core(
        proof_path,
        base_clause_count=EXPECTED_BASE_CLAUSES,
        units=units,
    )
    core_cnf = output / "core.cnf"
    write_conditioned_cnf(args.input, core_cnf, core)
    core_check = solve(
        args.solver,
        core_cnf,
        conflict_limit=args.core_conflicts,
        timeout_seconds=args.core_timeout,
        log=output / "core.log",
    )
    if core_check["status"] != "UNSAT":
        raise ProbeError(f"extracted core failed the independent UNSAT check: {core_check}")
    core_units = output / "core.units"
    write_new_bytes(core_units, (" ".join(map(str, core)) + " 0\n").encode("ascii"))
    report = {
        "schema_version": 1,
        "status": "LRAT_DEPENDENCY_CORE_RECONFIRMED_UNSAT",
        "warning": (
            "the full-parent LRAT is not yet replayed; the extracted core is a "
            "discovery result until its own LRAT is generated and checked"
        ),
        "input": {"path": str(args.input), "sha256": sha256_file(args.input)},
        "cover": {"path": str(args.cover), "sha256": sha256_file(args.cover)},
        "parent": parent_manifest(record, units, args.orientation),
        "full_parent": {
            "cnf_sha256": sha256_file(full_cnf),
            "solver": full_result,
        },
        "extraction": extraction,
        "original_units": list(units),
        "core_units": list(core),
        "removed_units": len(units) - len(core),
        "core_check": core_check,
        "core_cnf": {
            "path": str(core_cnf),
            "bytes": core_cnf.stat().st_size,
            "sha256": sha256_file(core_cnf),
            "clauses": EXPECTED_BASE_CLAUSES + len(core),
        },
        "core_units_file": {"path": str(core_units), "sha256": sha256_file(core_units)},
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps({
        "report": str(report_path),
        "full_units": len(units),
        "core_units": len(core),
        "removed_units": len(units) - len(core),
        "core_status": core_check["status"],
        "core_conflicts": core_check["conflicts"],
        "full_proof_bytes": proof_path.stat().st_size,
        "full_proof_sha256": sha256_file(proof_path),
        "core_cnf_sha256": sha256_file(core_cnf),
    }, indent=2, sort_keys=True))

def command_prove(args: argparse.Namespace) -> None:
    output = require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "proof.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    units = parse_units_file(args.units)
    cnf = output / "conditioned.cnf"
    write_conditioned_cnf(args.input, cnf, units)
    proof = output / "conditioned.lrat"
    log = output / "conditioned.log"
    result = solve(
        args.solver,
        cnf,
        conflict_limit=args.conflicts,
        timeout_seconds=args.timeout,
        proof=proof,
        log=log,
    )
    status = "UNSAT_WITH_UNCHECKED_LRAT" if result["proof"] is not None else "NO_LRAT"
    report = {
        "schema_version": 1,
        "status": status,
        "warning": "LRAT still requires replay against this exact CNF",
        "input": {"path": str(args.input), "sha256": sha256_file(args.input)},
        "units": list(units),
        "cnf": {
            "path": str(cnf),
            "bytes": cnf.stat().st_size,
            "sha256": sha256_file(cnf),
            "clauses": EXPECTED_BASE_CLAUSES + len(units),
        },
        "solver": result,
        "log": {"path": str(log), "sha256": sha256_file(log)},
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps(report, indent=2, sort_keys=True))


def core_requirements(units: Sequence[int], orientation: str) -> tuple[int, ...]:
    """Return 66 HOL colours under an explicit raw/complemented mapping."""
    if orientation not in ORIENTATIONS:
        raise ValueError(f"unknown catalogue orientation {orientation!r}")
    requirements = [0] * 66
    for literal in units:
        index = abs(literal) - 211
        if not 0 <= index < 66:
            raise ProbeError(f"core literal {literal} is not a B-B edge")
        if requirements[index] != 0:
            raise ProbeError(f"core repeats B-B edge variable {abs(literal)}")
        positive_colour = 1 if orientation == "complemented" else 2
        negative_colour = 2 if orientation == "complemented" else 1
        requirements[index] = positive_colour if literal > 0 else negative_colour
    return tuple(requirements)


def colours_extend_requirements(
    colours: Sequence[int], requirements: Sequence[int]
) -> bool:
    return all(required == 0 or colour == required for colour, required in zip(
        colours, requirements, strict=True
    ))


def child_orientation_extends_requirements(
    child_colours: Sequence[int],
    permutation: Sequence[int],
    requirements: Sequence[int],
) -> bool:
    inverse = [0] * B_ORDER
    for normal_vertex, original_vertex in enumerate(permutation):
        inverse[original_vertex] = normal_vertex
    pair_index = [[-1] * B_ORDER for _ in range(B_ORDER)]
    for index, (left, right) in enumerate(cover.edge_pairs(B_ORDER)):
        pair_index[left][right] = index
    for required, (left, right) in zip(
        requirements, cover.edge_pairs(B_ORDER), strict=True
    ):
        if required == 0:
            continue
        normal_left, normal_right = inverse[left], inverse[right]
        if normal_left > normal_right:
            normal_left, normal_right = normal_right, normal_left
        if child_colours[pair_index[normal_left][normal_right]] != required:
            return False
    return True


def has_permuted_extension(
    child_colours: Sequence[int], requirements: Sequence[int]
) -> bool:
    """Decide whether some permutation of a complete child extends the core."""
    pairs = cover.edge_pairs(B_ORDER)
    pair_index = [[-1] * B_ORDER for _ in range(B_ORDER)]
    required_matrix = [[0] * B_ORDER for _ in range(B_ORDER)]
    target_matrix = [[0] * B_ORDER for _ in range(B_ORDER)]
    for index, (left, right) in enumerate(pairs):
        pair_index[left][right] = index
        required_matrix[left][right] = required_matrix[right][left] = requirements[index]
        target_matrix[left][right] = target_matrix[right][left] = child_colours[index]

    target_colour1_degrees = [
        sum(target_matrix[vertex][other] == 1 for other in range(B_ORDER))
        for vertex in range(B_ORDER)
    ]
    domains: list[tuple[int, ...]] = []
    for pattern_vertex in range(B_ORDER):
        required_colour1 = sum(
            required_matrix[pattern_vertex][other] == 1 for other in range(B_ORDER)
        )
        required_colour2 = sum(
            required_matrix[pattern_vertex][other] == 2 for other in range(B_ORDER)
        )
        domains.append(tuple(
            target_vertex
            for target_vertex, colour1_degree in enumerate(target_colour1_degrees)
            if required_colour1
            <= colour1_degree
            <= B_ORDER - 1 - required_colour2
        ))
        if not domains[-1]:
            return False

    assignment = [-1] * B_ORDER

    def candidates(pattern_vertex: int, used_mask: int) -> tuple[int, ...]:
        result: list[int] = []
        for target_vertex in domains[pattern_vertex]:
            if (used_mask >> target_vertex) & 1:
                continue
            compatible = True
            for other_pattern, other_target in enumerate(assignment):
                if other_target < 0:
                    continue
                required = required_matrix[pattern_vertex][other_pattern]
                if required != 0 and target_matrix[target_vertex][other_target] != required:
                    compatible = False
                    break
            if compatible:
                result.append(target_vertex)
        return tuple(result)

    def search(used_mask: int, assigned_count: int) -> bool:
        if assigned_count == B_ORDER:
            return True
        best_vertex = -1
        best_candidates: tuple[int, ...] | None = None
        for pattern_vertex in range(B_ORDER):
            if assignment[pattern_vertex] >= 0:
                continue
            available = candidates(pattern_vertex, used_mask)
            if not available:
                return False
            if best_candidates is None or len(available) < len(best_candidates):
                best_vertex = pattern_vertex
                best_candidates = available
        assert best_candidates is not None
        for target_vertex in best_candidates:
            assignment[best_vertex] = target_vertex
            if search(used_mask | (1 << target_vertex), assigned_count + 1):
                return True
            assignment[best_vertex] = -1
        return False

    return search(0, 0)


def command_scope(args: argparse.Namespace) -> None:
    if args.record_step < 1 or args.max_children < 0 or args.children_per_record < 0:
        raise ValueError("scope sampling limits must be nonnegative and record step positive")
    output = require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "scope.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    units = parse_units_file(args.units)
    requirements = core_requirements(units, args.orientation)
    direct_parent_indices: list[int] = []
    recorded_matches = 0
    permuted_matches = 0
    completion_count = 0
    records = 0
    parents_with_recorded_matches: set[int] = set()
    parents_with_permuted_matches: set[int] = set()
    started = time.perf_counter()
    with args.cover.open("rb") as stream:
        for record_index, raw_line in enumerate(stream, 1):
            fields = raw_line.strip().decode("ascii").split()
            parent_colours = cover.decode_edges(
                int(fields[0], 10), B_ORDER, f"{args.cover}:{record_index}:parent"
            )
            if colours_extend_requirements(parent_colours, requirements):
                direct_parent_indices.append(record_index)
            records += 1
            selected_children = fields[1:]
            if (record_index - 1) % args.record_step != 0:
                selected_children = []
            elif args.children_per_record:
                selected_children = selected_children[: args.children_per_record]
            for child_number, token in enumerate(selected_children, 1):
                if args.max_children and completion_count >= args.max_children:
                    break
                context = f"{args.cover}:{record_index}:child#{child_number}"
                child_id, permutation = cover.parse_child_token(token, B_ORDER, context)
                child_colours = cover.decode_edges(child_id, B_ORDER, context)
                if child_orientation_extends_requirements(
                    child_colours, permutation, requirements
                ):
                    recorded_matches += 1
                    parents_with_recorded_matches.add(record_index)
                if args.check_permutations and has_permuted_extension(
                    child_colours, requirements
                ):
                    permuted_matches += 1
                    parents_with_permuted_matches.add(record_index)
                completion_count += 1
    elapsed = time.perf_counter() - started
    report = {
        "schema_version": 1,
        "status": "CONDITIONED_CORE_SCOPE_MEASURED",
        "warning": (
            "a sampled completion count is not a completeness result"
            if args.max_children else
            "scope of this one cube only; a global cover and Lean bridge remain required"
        ),
        "cover": {"path": str(args.cover), "sha256": sha256_file(args.cover)},
        "core_units_file": {"path": str(args.units), "sha256": sha256_file(args.units)},
        "core_unit_count": len(units),
        "core_holes": 66 - len(units),
        "catalogue_orientation": args.orientation,
        "orientation_warning": (
            "HOL-label inversion: require direct catalogue-adjacency interpretation or complement transport"
            if args.orientation == "complemented" else "raw HOL blue/red orientation"
        ),
        "records_scanned": records,
        "direct_parent_implication": {
            "count": len(direct_parent_indices),
            "indices_one_based": direct_parent_indices,
        },
        "completion_scan": {
            "limit": args.max_children or None,
            "record_step": args.record_step,
            "children_per_record": args.children_per_record or None,
            "count": completion_count,
            "recorded_parent_orientation_matches": recorded_matches,
            "recorded_parent_orientation_parent_count": len(parents_with_recorded_matches),
            "arbitrary_permutation_checked": args.check_permutations,
            "arbitrary_permutation_matches": permuted_matches if args.check_permutations else None,
            "arbitrary_permutation_parent_count": (
                len(parents_with_permuted_matches) if args.check_permutations else None
            ),
        },
        "wall_seconds": round(elapsed, 3),
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps(report, indent=2, sort_keys=True))

def wilson_interval(successes: int, trials: int, z: float = 1.959963984540054) -> tuple[float, float]:
    if trials <= 0 or not 0 <= successes <= trials:
        raise ValueError("Wilson interval needs 0 <= successes <= positive trials")
    proportion = successes / trials
    denominator = 1.0 + z * z / trials
    center = (proportion + z * z / (2.0 * trials)) / denominator
    radius = (
        z
        * math.sqrt(
            proportion * (1.0 - proportion) / trials
            + z * z / (4.0 * trials * trials)
        )
        / denominator
    )
    return max(0.0, center - radius), min(1.0, center + radius)


def command_estimate(args: argparse.Namespace) -> None:
    if args.sample_size < 1:
        raise ValueError("sample size must be positive")
    output = require_absolute_ssd(args.output)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "estimate.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    units = parse_units_file(args.units)
    requirements = core_requirements(units, args.orientation)
    rng = random.Random(args.seed)
    reservoir: list[tuple[int, int, int, str]] = []
    population = 0
    records = 0
    direct_parent_indices: list[int] = []
    started = time.perf_counter()
    with args.cover.open("rb") as stream:
        for record_index, raw_line in enumerate(stream, 1):
            fields = raw_line.strip().decode("ascii").split()
            parent_colours = cover.decode_edges(
                int(fields[0], 10), B_ORDER, f"{args.cover}:{record_index}:parent"
            )
            if colours_extend_requirements(parent_colours, requirements):
                direct_parent_indices.append(record_index)
            records += 1
            for child_number, token in enumerate(fields[1:], 1):
                population += 1
                item = (population, record_index, child_number, token)
                if len(reservoir) < args.sample_size:
                    reservoir.append(item)
                else:
                    replacement = rng.randrange(population)
                    if replacement < args.sample_size:
                        reservoir[replacement] = item
    if len(reservoir) != min(args.sample_size, population):
        raise ProbeError("reservoir sampler returned the wrong sample size")
    reservoir.sort(key=lambda row: row[0])
    recorded_matches: list[int] = []
    permuted_matches: list[int] = []
    for global_index, record_index, child_number, token in reservoir:
        context = f"{args.cover}:{record_index}:child#{child_number}"
        child_id, permutation = cover.parse_child_token(token, B_ORDER, context)
        child_colours = cover.decode_edges(child_id, B_ORDER, context)
        if child_orientation_extends_requirements(
            child_colours, permutation, requirements
        ):
            recorded_matches.append(global_index)
        if has_permuted_extension(child_colours, requirements):
            permuted_matches.append(global_index)
    trials = len(reservoir)
    successes = len(permuted_matches)
    lower, upper = wilson_interval(successes, trials)
    proportion = successes / trials
    sampled_indices = [row[0] for row in reservoir]
    sample_digest = hashlib.sha256(json_bytes(sampled_indices)).hexdigest().upper()
    elapsed = time.perf_counter() - started
    report = {
        "schema_version": 1,
        "status": "DETERMINISTIC_UNIFORM_RESERVOIR_SCOPE_ESTIMATE",
        "warning": (
            "this is a statistical estimate, not a cover or a proof; it assumes "
            "the separately audited official child list is the target population"
        ),
        "cover": {"path": str(args.cover), "sha256": sha256_file(args.cover)},
        "core_units_file": {"path": str(args.units), "sha256": sha256_file(args.units)},
        "core_unit_count": len(units),
        "core_holes": 66 - len(units),
        "catalogue_orientation": args.orientation,
        "orientation_warning": (
            "HOL-label inversion: require direct catalogue-adjacency interpretation or complement transport"
            if args.orientation == "complemented" else "raw HOL blue/red orientation"
        ),
        "records_scanned": records,
        "population_child_instances": population,
        "direct_parent_implication": {
            "count": len(direct_parent_indices),
            "indices_one_based": direct_parent_indices,
        },
        "sampling": {
            "method": "Algorithm R reservoir sample without replacement",
            "prng": "Python random.Random (Mersenne Twister), deterministic",
            "seed": args.seed,
            "requested_size": args.sample_size,
            "actual_size": trials,
            "selected_global_indices_sha256": sample_digest,
            "selected_global_indices_one_based": sampled_indices,
        },
        "recorded_parent_orientation": {
            "matches": len(recorded_matches),
            "sample_proportion": len(recorded_matches) / trials,
        },
        "arbitrary_vertex_permutation": {
            "checker": "exact backtracking bijection over all 12 vertices",
            "matches": successes,
            "sample_proportion": proportion,
            "wilson_95_interval": [lower, upper],
            "estimated_population_matches": round(proportion * population),
            "wilson_95_population_interval": [
                math.floor(lower * population),
                math.ceil(upper * population),
            ],
            "matching_sample_global_indices": permuted_matches,
        },
        "interval_note": (
            "Wilson interval is descriptive sampling uncertainty only; finite "
            "population correction is omitted and no formal guarantee is claimed"
        ),
        "wall_seconds": round(elapsed, 3),
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps({
        "report": str(report_path),
        "population": population,
        "sample_size": trials,
        "permuted_matches": successes,
        "sample_proportion": proportion,
        "wilson_95_interval": [lower, upper],
        "estimated_population_matches": round(proportion * population),
        "wall_seconds": round(elapsed, 3),
    }, indent=2, sort_keys=True))

def command_replay(args: argparse.Namespace) -> None:
    output = require_absolute_ssd(args.output)
    cnf = require_absolute_ssd(args.cnf)
    proof = require_absolute_ssd(args.lrat)
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "replay.json"
    if report_path.exists():
        raise FileExistsError(f"refusing to overwrite {report_path}")
    lean_path = output / "Replay.lean"
    cnf_lean = str(cnf).replace("\\", "/")
    proof_lean = str(proof).replace("\\", "/")
    source = (
        "import LRATCatcher.ReflectTrim\n\n"
        "namespace LRATCatcher.Tests.R45D12ConditionedCoreReplay\n\n"
        "lrat_reflect_trim d12_type0_core24_unsat\n"
        f"  \"{cnf_lean}\"\n"
        f"  \"{proof_lean}\"\n\n"
        "#print axioms d12_type0_core24_unsat\n\n"
        "end LRATCatcher.Tests.R45D12ConditionedCoreReplay\n"
    ).encode("utf-8")
    write_new_bytes(lean_path, source)
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            [str(args.lake), "env", "lean", str(lean_path)],
            cwd=REPOSITORY / "vendor" / "lrat-catcher",
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=args.timeout,
            check=False,
        )
        log_text = completed.stdout
        returncode: int | None = completed.returncode
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        raw = exc.stdout or ""
        log_text = raw if isinstance(raw, str) else raw.decode("utf-8", "replace")
        returncode = None
        timed_out = True
    wall_seconds = time.perf_counter() - started
    log_path = output / "replay.log"
    write_new_bytes(log_path, log_text.encode("utf-8"))
    replayed = returncode == 0 and not timed_out
    report = {
        "schema_version": 1,
        "status": "LEAN_LRAT_REPLAY_SUCCEEDED" if replayed else "LEAN_LRAT_REPLAY_FAILED",
        "theorem": "LRATCatcher.Tests.R45D12ConditionedCoreReplay.d12_type0_core24_unsat",
        "cnf": {"path": str(cnf), "sha256": sha256_file(cnf)},
        "lrat": {
            "path": str(proof),
            "bytes": proof.stat().st_size,
            "sha256": sha256_file(proof),
        },
        "lean_source": {"path": str(lean_path), "sha256": sha256_file(lean_path)},
        "log": {"path": str(log_path), "sha256": sha256_file(log_path)},
        "returncode": returncode,
        "timed_out": timed_out,
        "wall_seconds": round(wall_seconds, 3),
    }
    write_new_bytes(report_path, json_bytes(report))
    print(json.dumps(report, indent=2, sort_keys=True))
    if not replayed:
        raise ProbeError(f"Lean LRAT replay failed; see {log_path}")

def main() -> None:
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)

    def common(command: argparse.ArgumentParser) -> None:
        command.add_argument("--input", type=Path, required=True)
        command.add_argument("--cover", type=Path, required=True)
        command.add_argument("--solver", type=Path, required=True)
        command.add_argument("--output", type=Path, required=True)
        command.add_argument("--conflicts", type=int, required=True)
        command.add_argument("--timeout", type=float, required=True)
        command.add_argument("--orientation", choices=ORIENTATIONS, required=True)

    benchmark = commands.add_parser("benchmark")
    common(benchmark)
    benchmark.add_argument("--parents", required=True)
    benchmark.set_defaults(func=command_benchmark)

    minimize = commands.add_parser("minimize")
    common(minimize)
    minimize.add_argument("--parent", type=int, required=True)
    minimize.add_argument("--start-units", type=Path)
    minimize.add_argument(
        "--order",
        choices=("ascending", "descending", "positive-first", "negative-first"),
        default="ascending",
    )
    minimize.add_argument("--final-conflicts", type=int, required=True)
    minimize.add_argument("--final-timeout", type=float, required=True)
    minimize.set_defaults(func=command_minimize)

    core = commands.add_parser("core")
    common(core)
    core.add_argument("--parent", type=int, required=True)
    core.add_argument("--core-conflicts", type=int, required=True)
    core.add_argument("--core-timeout", type=float, required=True)
    core.set_defaults(func=command_core)
    prove = commands.add_parser("prove")
    prove.add_argument("--input", type=Path, required=True)
    prove.add_argument("--units", type=Path, required=True)
    prove.add_argument("--solver", type=Path, required=True)
    prove.add_argument("--output", type=Path, required=True)
    prove.add_argument("--conflicts", type=int, required=True)
    prove.add_argument("--timeout", type=float, required=True)
    prove.set_defaults(func=command_prove)

    scope = commands.add_parser("scope")
    scope.add_argument("--cover", type=Path, required=True)
    scope.add_argument("--units", type=Path, required=True)
    scope.add_argument("--output", type=Path, required=True)
    scope.add_argument("--max-children", type=int, default=0)
    scope.add_argument("--record-step", type=int, default=1)
    scope.add_argument("--children-per-record", type=int, default=0)
    scope.add_argument("--check-permutations", action="store_true")
    scope.add_argument("--orientation", choices=ORIENTATIONS, required=True)
    scope.set_defaults(func=command_scope)
    estimate = commands.add_parser("estimate")
    estimate.add_argument("--cover", type=Path, required=True)
    estimate.add_argument("--units", type=Path, required=True)
    estimate.add_argument("--output", type=Path, required=True)
    estimate.add_argument("--sample-size", type=int, required=True)
    estimate.add_argument("--seed", type=int, required=True)
    estimate.add_argument("--orientation", choices=ORIENTATIONS, required=True)
    estimate.set_defaults(func=command_estimate)
    replay = commands.add_parser("replay")
    replay.add_argument("--cnf", type=Path, required=True)
    replay.add_argument("--lrat", type=Path, required=True)
    replay.add_argument("--lake", type=Path, required=True)
    replay.add_argument("--output", type=Path, required=True)
    replay.add_argument("--timeout", type=float, required=True)
    replay.set_defaults(func=command_replay)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
