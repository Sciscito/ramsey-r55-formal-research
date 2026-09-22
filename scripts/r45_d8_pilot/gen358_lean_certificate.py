#!/usr/bin/env python3
"""Generate the independently checked Lean data for the ``gen358`` cover.

The 27 Barakeel parents list 179 fully coloured children.  This generator
matches each child to the unique representative in the already certified
``R(3,5,8)`` catalogue and records every permutation needed by the Lean
checker.  Nauty is not used: the small isomorphisms are found by the local
refinement/backtracking routine and are checked again in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from dataclasses import dataclass
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
R55 = REPO / "r55"
GEN358 = HERE / "data" / "gen358"
CATALOGUE = R55 / "r35_8.g6"
LEAN_DATA = (
    REPO
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R45DegreeEightCoverData.lean"
)

sys.path.insert(0, str(R55))
import catalog_certificate  # noqa: E402
import ramsey  # noqa: E402


def _load_cover_checker():
    path = HERE / "check_barakeel_covers.py"
    spec = importlib.util.spec_from_file_location("gen358_cover_checker", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


cover = _load_cover_checker()


@dataclass(frozen=True)
class Gen358Witness:
    parent: int
    child_id: int
    parent_permutation: tuple[int, ...]
    catalogue_permutation: tuple[int, ...]
    direct_permutation: tuple[int, ...]


def _read_catalogue() -> list[ramsey.Graph]:
    records = [line for line in CATALOGUE.read_text(encoding="ascii").splitlines() if line]
    return [ramsey.decode_graph6(record) for record in records]


def _child_graph(child_id: int) -> ramsey.Graph:
    """Map HOL4 colour 1 to adjacency ``true`` in the Lean catalogue."""

    rows = [0] * 8
    colours = cover.decode_edges(child_id, 8, f"child {child_id}")
    for colour, (left, right) in zip(colours, cover.edge_pairs(8), strict=True):
        if colour == 1:
            rows[left] |= 1 << right
            rows[right] |= 1 << left
        elif colour != 2:
            raise RuntimeError(f"child {child_id} contains hole/colour {colour}")
    return tuple(rows)


def _direct_permutation(
    parent_permutation: tuple[int, ...],
    catalogue_permutation: tuple[int, ...],
) -> tuple[int, ...]:
    """Compose original-parent -> child-normal -> Lean-catalogue labels."""

    inverse = [0] * 8
    for normal_vertex, original_vertex in enumerate(parent_permutation):
        inverse[original_vertex] = normal_vertex
    return tuple(catalogue_permutation[inverse[vertex]] for vertex in range(8))


def _parent_agrees_with_catalogue(
    parent_id: int,
    target: ramsey.Graph,
    permutation: tuple[int, ...],
) -> bool:
    parent = cover.decode_edges(parent_id, 8, f"parent {parent_id}")
    for colour, (left, right) in zip(parent, cover.edge_pairs(8), strict=True):
        if colour == 0:
            continue
        edge = (target[permutation[left]] >> permutation[right]) & 1
        if edge != (colour == 1):
            return False
    return True


def build_certificate() -> tuple[list[int], list[Gen358Witness]]:
    stats = cover.check_cover(GEN358)
    if (stats.records, stats.instances, stats.unique_child_ids) != (27, 179, 179):
        raise RuntimeError(f"unexpected gen358 shape: {stats}")

    catalogue = _read_catalogue()
    if len(catalogue) != 179:
        raise RuntimeError(f"expected 179 catalogue graphs, found {len(catalogue)}")

    targets_by_invariant: dict[tuple[object, ...], list[int]] = {}
    for target_index, target in enumerate(catalogue):
        targets_by_invariant.setdefault(
            catalog_certificate.graph_invariant(target), []
        ).append(target_index)

    parents: list[int] = []
    witnesses_by_target: dict[int, Gen358Witness] = {}
    for parent_index, raw_line in enumerate(GEN358.read_text(encoding="ascii").splitlines()):
        fields = raw_line.split()
        parent_id = int(fields[0], 10)
        parents.append(parent_id)
        for child_number, token in enumerate(fields[1:], 1):
            child_id, parent_permutation_list = cover.parse_child_token(
                token, 8, f"{GEN358}:{parent_index + 1}:child#{child_number}"
            )
            parent_permutation = tuple(parent_permutation_list)
            child = _child_graph(child_id)
            candidates = targets_by_invariant.get(
                catalog_certificate.graph_invariant(child), []
            )
            matches: list[tuple[int, tuple[int, ...]]] = []
            for target_index in candidates:
                permutation = catalog_certificate.find_isomorphism(
                    child, catalogue[target_index]
                )
                if permutation is not None:
                    matches.append((target_index, permutation))
            if len(matches) != 1:
                raise RuntimeError(
                    f"child {child_id} has {len(matches)} catalogue matches"
                )
            target_index, catalogue_permutation = matches[0]
            direct_permutation = _direct_permutation(
                parent_permutation, catalogue_permutation
            )
            if not _parent_agrees_with_catalogue(
                parent_id, catalogue[target_index], direct_permutation
            ):
                raise RuntimeError(
                    f"composed permutation fails for parent {parent_index}, "
                    f"child {child_id}, target {target_index}"
                )
            witness = Gen358Witness(
                parent=parent_index,
                child_id=child_id,
                parent_permutation=parent_permutation,
                catalogue_permutation=catalogue_permutation,
                direct_permutation=direct_permutation,
            )
            if target_index in witnesses_by_target:
                raise RuntimeError(f"duplicate catalogue target {target_index}")
            witnesses_by_target[target_index] = witness

    expected_targets = set(range(len(catalogue)))
    if set(witnesses_by_target) != expected_targets:
        missing = sorted(expected_targets - set(witnesses_by_target))
        raise RuntimeError(f"catalogue targets are not exhaustive; missing {missing}")
    return parents, [witnesses_by_target[index] for index in range(len(catalogue))]


def _lean_list(values: tuple[int, ...] | list[int]) -> str:
    return "[" + ",".join(map(str, values)) + "]"


def render_lean_data() -> str:
    parents, witnesses = build_certificate()
    lines = [
        "/- This file is generated by gen358_lean_certificate.py.",
        f"   gen358 SHA-256: {cover.sha256_file(GEN358)}",
        f"   r35_8.g6 SHA-256: {cover.sha256_file(CATALOGUE)} -/",
        "namespace LRATCatcher.Tests.R45DegreeEightCover",
        "",
        "structure Gen358Witness where",
        "  parent : Nat",
        "  childId : Nat",
        "  parentPermutation : List Nat",
        "  cataloguePermutation : List Nat",
        "  directPermutation : List Nat",
        "deriving DecidableEq, Repr",
        "",
        f"def gen358ParentIds : List Nat := {_lean_list(parents)}",
        "",
        "def gen358Witnesses : List Gen358Witness := [",
    ]
    for index, witness in enumerate(witnesses):
        suffix = "," if index + 1 < len(witnesses) else ""
        lines.extend(
            [
                f"  {{ parent := {witness.parent}, childId := {witness.child_id}",
                f"    parentPermutation := {_lean_list(witness.parent_permutation)}",
                f"    cataloguePermutation := {_lean_list(witness.catalogue_permutation)}",
                f"    directPermutation := {_lean_list(witness.direct_permutation)} }}{suffix}",
            ]
        )
    lines.extend(["]", "", "end LRATCatcher.Tests.R45DegreeEightCover", ""])
    return "\n".join(lines)


def _summary(rendered: str) -> dict[str, object]:
    parents, witnesses = build_certificate()
    return {
        "catalogue_sha256": cover.sha256_file(CATALOGUE),
        "catalogue_graphs": len(witnesses),
        "cover_sha256": cover.sha256_file(GEN358),
        "lean_data_sha256": hashlib.sha256(rendered.encode("utf-8")).hexdigest().upper(),
        "parents": len(parents),
        "witnesses": len(witnesses),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("write", help="regenerate the checked-in Lean data")
    commands.add_parser("verify", help="verify invariants and checked-in data")
    args = parser.parse_args()

    rendered = render_lean_data()
    if args.command == "write":
        LEAN_DATA.write_bytes(rendered.encode("utf-8"))
    else:
        actual = LEAN_DATA.read_text(encoding="utf-8")
        if actual.replace("\r\n", "\n") != rendered:
            raise SystemExit(f"generated Lean data is stale: {LEAN_DATA}")
    print(json.dumps(_summary(rendered), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
