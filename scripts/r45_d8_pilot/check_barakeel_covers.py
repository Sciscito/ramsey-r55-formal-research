#!/usr/bin/env python3
"""Independent structural checker for Barakeel/HOL4 ``gen*`` cover files.

This checker deliberately proves only properties visible in a cover file:

* the text grammar is well formed;
* every encoded matrix has the declared order and a valid base-3 sentinel;
* every suffix is a genuine vertex permutation;
* every child is a fully coloured graph;
* every non-hole edge of its parent agrees with the child after undoing the
  stored canonicalisation permutation;
* child identifiers are not duplicated within a file.

It does *not* prove that the child identifiers are all Ramsey-free graphs, or
that they exhaust that mathematical universe.  Those are separate catalogue
and completeness obligations in the original HOL4 development.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


NAME_RE = re.compile(r"^gen(?P<family>35|44)(?P<order>[0-9]+)$")


class CoverError(ValueError):
    """Raised when a cover record violates the documented format."""


@dataclass
class CoverStats:
    path: str
    sha256: str
    byte_size: int
    family: str
    order: int
    records: int
    instances: int
    unique_child_ids: int
    duplicate_child_ids: int
    parent_holes_min: int
    parent_holes_max: int
    parent_holes_total: int
    instances_per_record_min: int
    instances_per_record_max: int
    maximum_line_bytes: int


def edge_pairs(order: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(order) for j in range(i + 1, order)]


def decode_edges(encoded: int, order: int, context: str) -> list[int]:
    """Invert graph.sml ``zip_mat`` for the upper-triangular edge sequence."""
    edge_count = order * (order - 1) // 2
    value = encoded
    digits_reversed: list[int] = []
    for _ in range(edge_count):
        value, digit = divmod(value, 3)
        digits_reversed.append(digit)
    if value != 1:
        raise CoverError(
            f"{context}: invalid base-3 sentinel or matrix order "
            f"(remaining prefix is {value}, expected 1)"
        )
    return list(reversed(digits_reversed))


def parse_child_token(token: str, order: int, context: str) -> tuple[int, list[int]]:
    fields = token.split("_")
    if len(fields) != order + 1:
        raise CoverError(
            f"{context}: child token has {len(fields) - 1} permutation entries, "
            f"expected {order}"
        )
    try:
        child_id = int(fields[0], 10)
        permutation = [int(field, 10) for field in fields[1:]]
    except ValueError as exc:
        raise CoverError(f"{context}: non-decimal field") from exc
    if sorted(permutation) != list(range(order)):
        raise CoverError(f"{context}: suffix is not a permutation of 0..{order - 1}")
    return child_id, permutation


def check_parent_child_agreement(
    parent_edges: list[int],
    child_edges: list[int],
    permutation: list[int],
    pairs: list[tuple[int, int]],
    pair_index: list[list[int]],
    context: str,
) -> None:
    """Check parent edges in the pre-canonical child orientation.

    ``normalize_nauty_wperm`` stores ``perm`` with
    ``normal[a,b] = original[perm[a],perm[b]]``.  Thus the colour of original
    edge ``(i,j)`` is read at normal edge ``(invperm[i],invperm[j])``.
    """
    order = len(permutation)
    inverse = [0] * order
    for normal_vertex, original_vertex in enumerate(permutation):
        inverse[original_vertex] = normal_vertex

    for edge_no, (i, j) in enumerate(pairs):
        parent_colour = parent_edges[edge_no]
        if parent_colour == 0:
            continue
        ni, nj = inverse[i], inverse[j]
        if ni > nj:
            ni, nj = nj, ni
        child_colour = child_edges[pair_index[ni][nj]]
        if child_colour != parent_colour:
            raise CoverError(
                f"{context}: parent edge ({i},{j}) has colour {parent_colour}, "
                f"but the unpermuted child has colour {child_colour}"
            )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def check_cover(path: Path) -> CoverStats:
    match = NAME_RE.fullmatch(path.name)
    if match is None:
        raise CoverError(f"{path}: expected filename gen35N or gen44N")
    family = match.group("family")
    order = int(match.group("order"), 10)
    pairs = edge_pairs(order)
    pair_index = [[-1] * order for _ in range(order)]
    for index, (i, j) in enumerate(pairs):
        pair_index[i][j] = index

    records = 0
    instances = 0
    duplicate_child_ids = 0
    child_ids: set[int] = set()
    parent_holes_min: int | None = None
    parent_holes_max = 0
    parent_holes_total = 0
    instances_per_record_min: int | None = None
    instances_per_record_max = 0
    maximum_line_bytes = 0

    # Binary mode makes line-size accounting exact and accepts arbitrarily long
    # records without imposing a CSV-style field limit.
    with path.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            maximum_line_bytes = max(maximum_line_bytes, len(raw_line))
            stripped = raw_line.strip()
            if not stripped:
                raise CoverError(f"{path}:{line_number}: empty record")
            try:
                fields = stripped.decode("ascii").split()
            except UnicodeDecodeError as exc:
                raise CoverError(f"{path}:{line_number}: non-ASCII byte") from exc
            if len(fields) < 2:
                raise CoverError(f"{path}:{line_number}: record has no child instance")
            try:
                parent_id = int(fields[0], 10)
            except ValueError as exc:
                raise CoverError(f"{path}:{line_number}: invalid parent integer") from exc

            parent_edges = decode_edges(parent_id, order, f"{path}:{line_number}:parent")
            parent_holes = parent_edges.count(0)
            parent_holes_min = (
                parent_holes
                if parent_holes_min is None
                else min(parent_holes_min, parent_holes)
            )
            parent_holes_max = max(parent_holes_max, parent_holes)
            parent_holes_total += parent_holes

            record_instances = len(fields) - 1
            instances_per_record_min = (
                record_instances
                if instances_per_record_min is None
                else min(instances_per_record_min, record_instances)
            )
            instances_per_record_max = max(instances_per_record_max, record_instances)

            for child_number, token in enumerate(fields[1:], 1):
                context = f"{path}:{line_number}:child#{child_number}"
                child_id, permutation = parse_child_token(token, order, context)
                child_edges = decode_edges(child_id, order, context)
                if 0 in child_edges:
                    raise CoverError(f"{context}: child graph contains a hole (colour 0)")
                check_parent_child_agreement(
                    parent_edges,
                    child_edges,
                    permutation,
                    pairs,
                    pair_index,
                    context,
                )
                if child_id in child_ids:
                    duplicate_child_ids += 1
                else:
                    child_ids.add(child_id)

            records += 1
            instances += record_instances

    if records == 0:
        raise CoverError(f"{path}: empty cover file")

    return CoverStats(
        path=str(path.resolve()),
        sha256=sha256_file(path),
        byte_size=path.stat().st_size,
        family=family,
        order=order,
        records=records,
        instances=instances,
        unique_child_ids=len(child_ids),
        duplicate_child_ids=duplicate_child_ids,
        parent_holes_min=parent_holes_min if parent_holes_min is not None else 0,
        parent_holes_max=parent_holes_max,
        parent_holes_total=parent_holes_total,
        instances_per_record_min=(
            instances_per_record_min if instances_per_record_min is not None else 0
        ),
        instances_per_record_max=instances_per_record_max,
        maximum_line_bytes=maximum_line_bytes,
    )


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("covers", nargs="+", type=Path)
    args = parser.parse_args(argv)
    try:
        results = [asdict(check_cover(path)) for path in args.covers]
    except (CoverError, OSError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(results, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
