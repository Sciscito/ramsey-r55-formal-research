"""Generate and independently verify extension certificates for R(3,5,n).

The catalogue at order ``n`` is exhaustive up to isomorphism if every valid
one-vertex extension of every representative at order ``n-1`` is isomorphic
to a listed representative.  Starting with the unique empty graph, induction
then covers every labelled graph with no triangle and no independent set of
size five.

The certificate never asks the verifier to solve graph isomorphism: every
valid extension records an explicit vertex permutation.  The verifier
enumerates all masks itself and checks those permutations edge by edge.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Iterable, Sequence

from ramsey import Graph, complement_graph, count_cliques, decode_graph6, validate_graph


SCHEMA_VERSION = 1


def is_r35_free(graph: Graph) -> bool:
    """Whether ``graph`` contains neither K3 nor an independent 5-set."""

    return count_cliques(graph, 3) == 0 and count_cliques(
        complement_graph(graph), 5
    ) == 0


def extend_graph(graph: Graph, neighbor_mask: int) -> Graph:
    """Add one last vertex with the specified old-vertex neighbourhood."""

    validate_graph(graph)
    n = len(graph)
    if not (0 <= neighbor_mask < 1 << n):
        raise ValueError(f"extension mask must lie in 0..{(1 << n) - 1}")
    rows = list(graph) + [0]
    for vertex in range(n):
        if (neighbor_mask >> vertex) & 1:
            rows[vertex] |= 1 << n
            rows[n] |= 1 << vertex
    return tuple(rows)


def graph_invariant(graph: Graph) -> tuple[object, ...]:
    """A cheap isomorphism invariant used only to index candidate targets."""

    validate_graph(graph)
    degrees = tuple(row.bit_count() for row in graph)
    local = tuple(
        sorted(
            (
                degrees[vertex],
                tuple(
                    sorted(
                        degrees[neighbor]
                        for neighbor in range(len(graph))
                        if (graph[vertex] >> neighbor) & 1
                    )
                ),
            )
            for vertex in range(len(graph))
        )
    )
    return tuple(sorted(degrees)), local


def is_isomorphism(source: Graph, target: Graph, permutation: Sequence[int]) -> bool:
    """Check explicitly that ``permutation`` maps ``source`` to ``target``."""

    if len(source) != len(target) or len(permutation) != len(source):
        return False
    n = len(source)
    if sorted(permutation) != list(range(n)):
        return False
    return all(
        ((source[left] >> right) & 1)
        == ((target[permutation[left]] >> permutation[right]) & 1)
        for left in range(n)
        for right in range(left + 1, n)
    )


def _joint_refinement(source: Graph, target: Graph) -> tuple[list[int], list[int]] | None:
    """Return comparable stable color classes, or ``None`` on a mismatch."""

    source_colors = [row.bit_count() for row in source]
    target_colors = [row.bit_count() for row in target]
    n = len(source)
    for _ in range(n):
        source_signatures = [
            (
                source_colors[vertex],
                tuple(
                    sorted(
                        source_colors[neighbor]
                        for neighbor in range(n)
                        if (source[vertex] >> neighbor) & 1
                    )
                ),
            )
            for vertex in range(n)
        ]
        target_signatures = [
            (
                target_colors[vertex],
                tuple(
                    sorted(
                        target_colors[neighbor]
                        for neighbor in range(n)
                        if (target[vertex] >> neighbor) & 1
                    )
                ),
            )
            for vertex in range(n)
        ]
        palette = {
            signature: color
            for color, signature in enumerate(
                sorted(set(source_signatures + target_signatures))
            )
        }
        refined_source = [palette[signature] for signature in source_signatures]
        refined_target = [palette[signature] for signature in target_signatures]
        if sorted(refined_source) != sorted(refined_target):
            return None
        if refined_source == source_colors and refined_target == target_colors:
            return refined_source, refined_target
        source_colors, target_colors = refined_source, refined_target
    return source_colors, target_colors


def find_isomorphism(source: Graph, target: Graph) -> tuple[int, ...] | None:
    """Find one explicit isomorphism by refinement and small backtracking."""

    validate_graph(source)
    validate_graph(target)
    if len(source) != len(target) or graph_invariant(source) != graph_invariant(target):
        return None
    refined = _joint_refinement(source, target)
    if refined is None:
        return None
    source_colors, target_colors = refined
    n = len(source)
    color_classes = {
        color: tuple(
            vertex for vertex, vertex_color in enumerate(target_colors)
            if vertex_color == color
        )
        for color in set(target_colors)
    }
    mapping = [-1] * n

    def search(mapped_count: int, used_targets: int) -> tuple[int, ...] | None:
        if mapped_count == n:
            result = tuple(mapping)
            return result if is_isomorphism(source, target, result) else None

        best_vertex: int | None = None
        best_candidates: list[int] | None = None
        for vertex in range(n):
            if mapping[vertex] >= 0:
                continue
            candidates = []
            for candidate in color_classes[source_colors[vertex]]:
                if (used_targets >> candidate) & 1:
                    continue
                if all(
                    ((source[vertex] >> other) & 1)
                    == ((target[candidate] >> mapping[other]) & 1)
                    for other in range(n)
                    if mapping[other] >= 0
                ):
                    candidates.append(candidate)
            if not candidates:
                return None
            if best_candidates is None or len(candidates) < len(best_candidates):
                best_vertex = vertex
                best_candidates = candidates

        assert best_vertex is not None and best_candidates is not None
        for candidate in best_candidates:
            mapping[best_vertex] = candidate
            result = search(mapped_count + 1, used_targets | (1 << candidate))
            if result is not None:
                return result
            mapping[best_vertex] = -1
        return None

    return search(0, 0)


def _read_catalogue(path: Path, expected_order: int) -> list[Graph]:
    records = [
        line.strip()
        for line in path.read_text(encoding="ascii").splitlines()
        if line.strip()
    ]
    graphs = [decode_graph6(record) for record in records]
    for index, graph in enumerate(graphs):
        if len(graph) != expected_order:
            raise ValueError(f"{path}: graph {index} has order {len(graph)}")
        if not is_r35_free(graph):
            raise ValueError(f"{path}: graph {index} is not R(3,5)-free")
    return graphs


def _catalogue_metadata(path: Path, order: int, count: int) -> dict[str, object]:
    return {
        "order": order,
        "file": path.name,
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "graph_count": count,
    }


def generate_certificate(directory: Path, max_order: int) -> dict[str, object]:
    if not (0 <= max_order <= 16):
        raise ValueError("max_order must lie in 0..16")
    catalogues: list[list[Graph]] = []
    metadata: list[dict[str, object]] = []
    for order in range(max_order + 1):
        path = directory / f"r35_{order}.g6"
        graphs = _read_catalogue(path, order)
        catalogues.append(graphs)
        metadata.append(_catalogue_metadata(path, order, len(graphs)))

    transitions: list[dict[str, object]] = []
    for order in range(1, max_order + 1):
        targets = catalogues[order]
        buckets: dict[tuple[object, ...], list[tuple[int, Graph]]] = {}
        for target_index, target in enumerate(targets):
            buckets.setdefault(graph_invariant(target), []).append(
                (target_index, target)
            )

        records: list[list[object]] = []
        for parent_index, parent in enumerate(catalogues[order - 1]):
            for neighbor_mask in range(1 << (order - 1)):
                extension = extend_graph(parent, neighbor_mask)
                if not is_r35_free(extension):
                    continue
                match: tuple[int, tuple[int, ...]] | None = None
                for target_index, target in buckets.get(
                    graph_invariant(extension), ()
                ):
                    permutation = find_isomorphism(extension, target)
                    if permutation is not None:
                        match = target_index, permutation
                        break
                if match is None:
                    raise ValueError(
                        f"catalogue order {order} misses extension "
                        f"parent={parent_index}, mask={neighbor_mask}"
                    )
                target_index, permutation = match
                records.append(
                    [parent_index, neighbor_mask, target_index, list(permutation)]
                )
        transitions.append(
            {
                "order": order,
                "valid_extension_count": len(records),
                "records": records,
            }
        )

    return {
        "schema_version": SCHEMA_VERSION,
        "property": "no K3 and no independent set of size 5",
        "max_order": max_order,
        "catalogues": metadata,
        "transitions": transitions,
    }


def _require_int(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{label} must be an integer")
    return value


def verify_certificate(
    certificate: dict[str, object], directory: Path
) -> dict[str, int]:
    if certificate.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("unsupported certificate schema")
    max_order = _require_int(certificate.get("max_order"), "max_order")
    raw_metadata = certificate.get("catalogues")
    raw_transitions = certificate.get("transitions")
    if not isinstance(raw_metadata, list) or len(raw_metadata) != max_order + 1:
        raise ValueError("catalogue metadata has the wrong length")
    if not isinstance(raw_transitions, list) or len(raw_transitions) != max_order:
        raise ValueError("transition list has the wrong length")

    catalogues: list[list[Graph]] = []
    for order, raw_entry in enumerate(raw_metadata):
        if not isinstance(raw_entry, dict) or raw_entry.get("order") != order:
            raise ValueError(f"bad catalogue metadata at order {order}")
        filename = raw_entry.get("file")
        if filename != f"r35_{order}.g6":
            raise ValueError(f"unexpected catalogue filename at order {order}")
        path = directory / filename
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if raw_entry.get("sha256") != digest:
            raise ValueError(f"catalogue hash mismatch at order {order}")
        graphs = _read_catalogue(path, order)
        if raw_entry.get("graph_count") != len(graphs):
            raise ValueError(f"catalogue count mismatch at order {order}")
        catalogues.append(graphs)

    verified_extensions = 0
    for order, raw_transition in enumerate(raw_transitions, start=1):
        if not isinstance(raw_transition, dict) or raw_transition.get("order") != order:
            raise ValueError(f"bad transition metadata at order {order}")
        records = raw_transition.get("records")
        if not isinstance(records, list):
            raise ValueError(f"transition records at order {order} must be a list")
        record_index = 0
        for parent_index, parent in enumerate(catalogues[order - 1]):
            for neighbor_mask in range(1 << (order - 1)):
                extension = extend_graph(parent, neighbor_mask)
                if not is_r35_free(extension):
                    continue
                if record_index >= len(records):
                    raise ValueError(f"missing valid extension at order {order}")
                record = records[record_index]
                if not isinstance(record, list) or len(record) != 4:
                    raise ValueError(
                        f"malformed extension record {record_index} at order {order}"
                    )
                recorded_parent = _require_int(record[0], "parent index")
                recorded_mask = _require_int(record[1], "neighbor mask")
                target_index = _require_int(record[2], "target index")
                permutation = record[3]
                if (recorded_parent, recorded_mask) != (
                    parent_index,
                    neighbor_mask,
                ):
                    raise ValueError(
                        f"out-of-order extension record {record_index} at order {order}"
                    )
                if not (0 <= target_index < len(catalogues[order])):
                    raise ValueError(f"bad target index at order {order}")
                if not isinstance(permutation, list) or not all(
                    isinstance(value, int) and not isinstance(value, bool)
                    for value in permutation
                ):
                    raise ValueError(f"bad permutation at order {order}")
                if not is_isomorphism(
                    extension, catalogues[order][target_index], permutation
                ):
                    raise ValueError(
                        f"invalid isomorphism at order {order}, "
                        f"parent={parent_index}, mask={neighbor_mask}"
                    )
                record_index += 1
                verified_extensions += 1
        if record_index != len(records):
            raise ValueError(f"extra extension records at order {order}")
        if raw_transition.get("valid_extension_count") != record_index:
            raise ValueError(f"extension count mismatch at order {order}")

    return {
        "max_order": max_order,
        "catalogue_graphs": sum(map(len, catalogues)),
        "valid_extensions": verified_extensions,
    }


def _write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, separators=(",", ":")) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def _lean_nat_list(values: Sequence[int]) -> str:
    return "[" + ",".join(map(str, values)) + "]"


def write_lean_data(
    path: Path, certificate: dict[str, object], directory: Path
) -> None:
    """Write deterministic Lean literals for the checked catalogues/certificate."""

    verify_certificate(certificate, directory)
    max_order = _require_int(certificate.get("max_order"), "max_order")
    catalogues = [
        _read_catalogue(directory / f"r35_{order}.g6", order)
        for order in range(max_order + 1)
    ]
    transitions = certificate["transitions"]
    assert isinstance(transitions, list)

    with path.open("w", encoding="utf-8", newline="\n") as output:
        output.write("/- This file is generated by catalog_certificate.py. -/\n")
        output.write("set_option maxRecDepth 1000000\n")
        output.write("set_option maxHeartbeats 0\n\n")
        output.write("namespace LRATCatcher.Tests.R35\n\n")
        output.write("abbrev Graph := List Nat\n\n")
        output.write("structure ExtensionWitness where\n")
        output.write("  parent : Nat\n")
        output.write("  mask : Nat\n")
        output.write("  target : Nat\n")
        output.write("  permutation : List Nat\n")
        output.write("deriving DecidableEq, Repr\n\n")
        output.write("def catalogues : List (List Graph) := [\n")
        for order, graphs in enumerate(catalogues):
            suffix = "," if order < len(catalogues) - 1 else ""
            rendered = ",".join(_lean_nat_list(graph) for graph in graphs)
            output.write(f"  [{rendered}]{suffix}\n")
        output.write("]\n\n")
        output.write("def extensionWitnesses : List (List ExtensionWitness) := [\n")
        for transition_index, transition in enumerate(transitions):
            assert isinstance(transition, dict)
            records = transition["records"]
            assert isinstance(records, list)
            output.write("  [\n")
            for record_index, record in enumerate(records):
                assert isinstance(record, list) and len(record) == 4
                parent, mask, target, permutation = record
                assert isinstance(permutation, list)
                suffix = "," if record_index < len(records) - 1 else ""
                output.write(
                    "    { parent := "
                    f"{parent}, mask := {mask}, target := {target}, "
                    f"permutation := {_lean_nat_list(permutation)} }}{suffix}\n"
                )
            suffix = "," if transition_index < len(transitions) - 1 else ""
            output.write(f"  ]{suffix}\n")
        output.write("]\n\n")
        output.write("end LRATCatcher.Tests.R35\n")


def _cmd_generate(args: argparse.Namespace) -> None:
    certificate = generate_certificate(args.directory, args.max_order)
    _write_json(args.output, certificate)
    summary = verify_certificate(certificate, args.directory)
    print(json.dumps(summary, sort_keys=True))


def _cmd_verify(args: argparse.Namespace) -> None:
    certificate = json.loads(args.certificate.read_text(encoding="utf-8"))
    if not isinstance(certificate, dict):
        raise ValueError("certificate root must be an object")
    print(json.dumps(verify_certificate(certificate, args.directory), sort_keys=True))


def _cmd_write_lean_data(args: argparse.Namespace) -> None:
    certificate = json.loads(args.certificate.read_text(encoding="utf-8"))
    if not isinstance(certificate, dict):
        raise ValueError("certificate root must be an object")
    write_lean_data(args.output, certificate, args.directory)
    print(f"wrote Lean catalogue data to {args.output}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("generate")
    generate.add_argument("directory", type=Path)
    generate.add_argument("max_order", type=int)
    generate.add_argument("output", type=Path)
    generate.set_defaults(func=_cmd_generate)
    verify = commands.add_parser("verify")
    verify.add_argument("directory", type=Path)
    verify.add_argument("certificate", type=Path)
    verify.set_defaults(func=_cmd_verify)
    lean_data = commands.add_parser("write-lean-data")
    lean_data.add_argument("directory", type=Path)
    lean_data.add_argument("certificate", type=Path)
    lean_data.add_argument("output", type=Path)
    lean_data.set_defaults(func=_cmd_write_lean_data)
    return parser


def main(argv: Iterable[str] | None = None) -> None:
    args = build_parser().parse_args(argv)
    args.func(args)


if __name__ == "__main__":
    main()
