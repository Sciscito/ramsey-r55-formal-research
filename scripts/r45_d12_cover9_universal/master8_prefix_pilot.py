#!/usr/bin/env python3
"""Build or fingerprint a single prefix-master formula for cover6 degree 8.

``Master8`` is the frozen degree-eight source formula followed by the eleven
canonical root units, eight second-centre prefix clauses, and (for the exact
variant) three already-proved arithmetic bounds.  The bounded variant has
exactly the same 13 total assignments to variables 12..21 as the historical
two-centre case split.

The default commands write nothing and invoke no solver.  Explicit generation
is restricted to a new file below an absolute S: directory and refuses to
replace anything.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from collections import Counter
from pathlib import Path
from typing import BinaryIO, Iterable, Iterator, Sequence

from . import exact_replay_cover6_d8 as replay


VARIABLES = replay.GLOBAL_VARIABLES
LEFT_VARIABLES = tuple(replay.global_edge(1, vertex) for vertex in range(2, 9))
RIGHT_VARIABLES = tuple(replay.global_edge(1, vertex) for vertex in range(9, 12))

ROOT_UNITS: tuple[replay.Clause, ...] = tuple(
    ((variable if variable <= replay.DEGREE else -variable),)
    for variable in range(1, 12)
)
PREFIX_CLAUSES: tuple[replay.Clause, ...] = tuple(
    (left, -right) for left, right in zip(LEFT_VARIABLES, LEFT_VARIABLES[1:])
) + tuple(
    (left, -right) for left, right in zip(RIGHT_VARIABLES, RIGHT_VARIABLES[1:])
)

# Under prefix monotonicity:
#   -15       means p <= 3;
#   13 v 19  means p >= 2 or q >= 1;
#   12 v 20  means p >= 1 or q >= 2.
# The last two clauses are jointly equivalent to p + q >= 2.
BOUND_CLAUSES: tuple[replay.Clause, ...] = ((-15,), (13, 19), (12, 20))

VARIANT_PREFIX = "prefix32"
VARIANT_BOUNDED = "bounded13"
VARIANTS = (VARIANT_PREFIX, VARIANT_BOUNDED)

BOUNDED_EXPECTED_BYTES = 189_298_375
BOUNDED_EXPECTED_SHA256 = (
    "3E725132C29E1CAA9D5FD5EA0AD67D8A5A80E61A1241768D36A910DD23FD329D"
)


class Master8Error(ValueError):
    """Raised when the exact master partition or byte stream changes."""


def variant_extra_clauses(variant: str) -> tuple[replay.Clause, ...]:
    if variant == VARIANT_PREFIX:
        return ROOT_UNITS + PREFIX_CLAUSES
    if variant == VARIANT_BOUNDED:
        return ROOT_UNITS + PREFIX_CLAUSES + BOUND_CLAUSES
    raise ValueError(f"unknown Master8 variant: {variant}")


def second_assignment_tuple(p: int, q: int) -> tuple[bool, ...]:
    assignment = replay.second_assignment(p, q)
    return tuple(assignment[variable] for variable in range(12, 22))


def clause_satisfied(clause: Sequence[int], assignment: dict[int, bool]) -> bool:
    return any(assignment[abs(literal)] == (literal > 0) for literal in clause)


def satisfies(clauses: Iterable[replay.Clause], assignment: dict[int, bool]) -> bool:
    return all(clause_satisfied(clause, assignment) for clause in clauses)


def assignments(clauses: Sequence[replay.Clause]) -> tuple[dict[int, bool], ...]:
    result = []
    for values in itertools.product((False, True), repeat=10):
        assignment = dict(zip(range(12, 22), values))
        if satisfies(clauses, assignment):
            result.append(assignment)
    return tuple(result)


def assignment_pair(assignment: dict[int, bool]) -> tuple[int, int]:
    return (
        sum(assignment[variable] for variable in LEFT_VARIABLES),
        sum(assignment[variable] for variable in RIGHT_VARIABLES),
    )


def is_prefix(values: Sequence[bool]) -> bool:
    return all(not right or left for left, right in zip(values, values[1:]))


def audit_partition() -> dict[str, object]:
    if tuple(replay.global_edge(0, vertex) for vertex in range(1, 12)) != tuple(
        range(1, 12)
    ):
        raise Master8Error("root-edge DIMACS variables changed")
    if LEFT_VARIABLES != tuple(range(12, 19)):
        raise Master8Error(f"left second-centre variables changed: {LEFT_VARIABLES}")
    if RIGHT_VARIABLES != tuple(range(19, 22)):
        raise Master8Error(f"right second-centre variables changed: {RIGHT_VARIABLES}")
    if len(PREFIX_CLAUSES) != 8 or len(ROOT_UNITS) != 11 or len(BOUND_CLAUSES) != 3:
        raise Master8Error("Master8 extra-clause dimensions changed")

    prefix_models = assignments(PREFIX_CLAUSES)
    if any(
        not is_prefix(tuple(model[variable] for variable in LEFT_VARIABLES))
        or not is_prefix(tuple(model[variable] for variable in RIGHT_VARIABLES))
        for model in prefix_models
    ):
        raise Master8Error("prefix clause polarity admits a non-prefix assignment")
    prefix_pairs = {assignment_pair(model) for model in prefix_models}
    expected_prefix_pairs = {(p, q) for p in range(8) for q in range(4)}
    if len(prefix_models) != 32 or prefix_pairs != expected_prefix_pairs:
        raise Master8Error("eight prefix clauses do not encode all 32 prefix pairs")

    # Check the intended arithmetic meaning on every one of the 32 prefix
    # assignments, rather than only on the thirteen survivors.  This catches
    # either a literal-polarity error or an accidental weakening/strengthening
    # of the bounds.
    for model in prefix_models:
        p, q = assignment_pair(model)
        if clause_satisfied(BOUND_CLAUSES[0], model) != (p <= 3):
            raise Master8Error("p<=3 unit polarity changed")
        if satisfies(BOUND_CLAUSES[1:], model) != (2 <= p + q):
            raise Master8Error("p+q>=2 clauses changed")

    bounded_models = assignments(PREFIX_CLAUSES + BOUND_CLAUSES)
    bounded_pairs = tuple(sorted(assignment_pair(model) for model in bounded_models))
    if len(bounded_models) != len(replay.CASES):
        raise Master8Error("bounded master does not have thirteen assignments")
    if set(bounded_pairs) != set(replay.CASES) or len(set(bounded_pairs)) != len(bounded_pairs):
        raise Master8Error("bounded master differs from the exact thirteen cases")
    for model in bounded_models:
        p, q = assignment_pair(model)
        expected = replay.second_assignment(p, q)
        if any(model[variable] != expected[variable] for variable in range(12, 22)):
            raise Master8Error(f"bounded model is not the canonical assignment p={p},q={q}")
    for p, q in replay.CASES:
        units = replay.exact_units(p, q)
        if tuple((literal,) for literal in units[:11]) != ROOT_UNITS:
            raise Master8Error("root unit polarity differs from the 13 residual branches")
        expected_second = second_assignment_tuple(p, q)
        if tuple(literal > 0 for literal in units[11:]) != expected_second:
            raise Master8Error("second-centre unit polarity differs from a branch")

    return {
        "status": "PASS",
        "root_units": [clause[0] for clause in ROOT_UNITS],
        "left_variables": list(LEFT_VARIABLES),
        "right_variables": list(RIGHT_VARIABLES),
        "prefix_clauses": [list(clause) for clause in PREFIX_CLAUSES],
        "bound_clauses": [list(clause) for clause in BOUND_CLAUSES],
        "prefix_only_assignments": len(prefix_models),
        "prefix_only_pairs": [list(pair) for pair in sorted(prefix_pairs)],
        "bounded_assignments": len(bounded_models),
        "bounded_pairs": [list(pair) for pair in bounded_pairs],
        "exactly_historical_thirteen_cases": True,
        "scope": "finite ten-variable partition only; no F8, SAT, LRAT, or Lean claim",
    }


def master_clauses(variant: str) -> Iterator[replay.Clause]:
    yield from replay.expected_source_clauses()
    yield from variant_extra_clauses(variant)


def formula_name(variant: str) -> str:
    return f"cover6_closed_master_d8_{variant}.cnf"


def clause_count(variant: str) -> int:
    return replay.SOURCE_CLAUSES + len(variant_extra_clauses(variant))


def stream_formula(
    clauses: Iterable[replay.Clause], count: int, stream: BinaryIO | None = None
) -> dict[str, object]:
    digest = hashlib.sha256()
    size = 0
    written = 0
    widths: Counter[int] = Counter()

    def emit(data: bytes) -> None:
        nonlocal size
        if stream is not None:
            stream.write(data)
        digest.update(data)
        size += len(data)

    emit(f"p cnf {VARIABLES} {count}\n".encode("ascii"))
    for clause in clauses:
        emit(replay.clause_line(clause))
        widths[len(clause)] += 1
        written += 1
    if written != count:
        raise Master8Error(f"streamed clause count mismatch: {written} != {count}")
    return {
        "variables": VARIABLES,
        "clauses": written,
        "bytes": size,
        "sha256": digest.hexdigest().upper(),
        "widths": {str(width): amount for width, amount in sorted(widths.items())},
    }


def fingerprint(variant: str) -> dict[str, object]:
    partition = audit_partition()
    metadata = stream_formula(master_clauses(variant), clause_count(variant))
    if variant == VARIANT_BOUNDED:
        if metadata["bytes"] != BOUNDED_EXPECTED_BYTES:
            raise Master8Error("bounded Master8 byte count differs from tracked pilot")
        if metadata["sha256"] != BOUNDED_EXPECTED_SHA256:
            raise Master8Error("bounded Master8 SHA-256 differs from tracked pilot")
    return {
        "status": "PASS",
        "variant": variant,
        "formula": {"name": formula_name(variant), **metadata},
        "source": {
            "clauses": replay.SOURCE_CLAUSES,
            "sha256": replay.SOURCE_SHA256,
            "reconstructed_without_reading_frozen_S_artifact": True,
        },
        "extra_clauses": len(variant_extra_clauses(variant)),
        "partition": {
            "prefix_only_assignments": partition["prefix_only_assignments"],
            "bounded_assignments": partition["bounded_assignments"],
            "exactly_historical_thirteen_cases": (
                variant == VARIANT_BOUNDED
                and partition["exactly_historical_thirteen_cases"]
            ),
        },
        "scope": "deterministic CNF fingerprint only; no solver, LRAT, or Lean claim",
    }


def generate(directory: Path, variant: str) -> dict[str, object]:
    directory = replay.require_ssd(directory)
    directory.mkdir(parents=True, exist_ok=True)
    target = directory / formula_name(variant)
    if target.exists():
        raise FileExistsError(f"refusing to replace Master8 artifact: {target}")
    partial = directory / f"{target.name}.{os.getpid()}.partial"
    try:
        with partial.open("xb", buffering=8 * 1024 * 1024) as stream:
            metadata = stream_formula(
                master_clauses(variant), clause_count(variant), stream
            )
        if variant == VARIANT_BOUNDED:
            if metadata["bytes"] != BOUNDED_EXPECTED_BYTES:
                raise Master8Error("bounded Master8 byte count differs from tracked pilot")
            if metadata["sha256"] != BOUNDED_EXPECTED_SHA256:
                raise Master8Error("bounded Master8 SHA-256 differs from tracked pilot")
        os.replace(partial, target)
    finally:
        if partial.exists():
            partial.unlink()
    return {
        "status": "GENERATED_WITHOUT_SOLVER",
        "variant": variant,
        "formula": {"name": target.name, **metadata},
        "partition": audit_partition(),
    }


def verify(directory: Path, variant: str) -> dict[str, object]:
    directory = replay.require_ssd(directory)
    path = directory / formula_name(variant)
    result = replay.compare_formula(
        path,
        master_clauses(variant),
        clause_count(variant),
        expected_bytes=(BOUNDED_EXPECTED_BYTES if variant == VARIANT_BOUNDED else None),
        expected_sha256=(
            BOUNDED_EXPECTED_SHA256 if variant == VARIANT_BOUNDED else None
        ),
    )
    return {
        "status": "PASS",
        "variant": variant,
        "formula": {"name": path.name, **result},
        "partition": audit_partition(),
        "scope": "standalone byte comparison only; no solver or proof claim",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", nargs="?", default="preflight",
        choices=("preflight", "fingerprint", "generate", "verify"),
    )
    parser.add_argument("--variant", choices=VARIANTS, default=VARIANT_BOUNDED)
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = audit_partition()
    elif args.command == "fingerprint":
        result = fingerprint(args.variant)
    else:
        if args.directory is None:
            parser.error("generate/verify require --directory")
        result = (
            generate(args.directory, args.variant)
            if args.command == "generate"
            else verify(args.directory, args.variant)
        )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
