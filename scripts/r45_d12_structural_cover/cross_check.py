#!/usr/bin/env python3
"""Independent sparse-graph oracle for the native R(4,4,12) scanner."""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
from pathlib import Path
from typing import Sequence

from . import structural_cover


def encode_graph6(graph: Sequence[int]) -> str:
    order = len(graph)
    if order >= 63:
        raise ValueError("short graph6 header required")
    bits = [
        (graph[left] >> right) & 1
        for right in range(1, order)
        for left in range(right)
    ]
    bits.extend([0] * ((-len(bits)) % 6))
    return chr(63 + order) + "".join(
        chr(63 + sum(bits[offset + bit] << (5 - bit) for bit in range(6)))
        for offset in range(0, len(bits), 6)
    )


def relabelled_mask(graph: Sequence[int], permutation: Sequence[int]) -> int:
    result = 0
    bit = 0
    for right in range(1, len(permutation)):
        for left in range(right):
            if (graph[permutation[left]] >> permutation[right]) & 1:
                result |= 1 << bit
            bit += 1
    return result


def induced_mask(graph: Sequence[int], vertices: Sequence[int]) -> int:
    result = 0
    bit = 0
    for right in range(1, len(vertices)):
        for left in range(right):
            if (graph[vertices[left]] >> vertices[right]) & 1:
                result |= 1 << bit
            bit += 1
    return result


def embed_graph(graph: Sequence[int], order: int, vertices: Sequence[int]) -> tuple[int, ...]:
    if len(graph) != len(vertices):
        raise ValueError("embedding size mismatch")
    result = [0] * order
    for left in range(len(vertices)):
        for right in range(left + 1, len(vertices)):
            if (graph[left] >> right) & 1:
                u, v = vertices[left], vertices[right]
                result[u] |= 1 << v
                result[v] |= 1 << u
    return tuple(result)


def run(scanner: Path, source_directory: Path, output_directory: Path) -> dict[str, object]:
    output_directory = structural_cover.ensure_ssd(output_directory)
    output_directory.mkdir(parents=True, exist_ok=True)
    pool = structural_cover.dense_pool(source_directory)
    chosen = (pool[0], pool[1], pool[46], pool[47])
    candidate_path = output_directory / "cross_candidates.tsv"
    candidate_path.write_text(
        "".join(f"{item.order}\t{item.graph6}\n" for item in chosen),
        encoding="ascii",
        newline="\n",
    )
    candidate_graphs = tuple(
        structural_cover.ramsey.decode_graph6(item.graph6) for item in chosen
    )
    synthetic = [
        embed_graph(candidate_graphs[0], 12, (0, 2, 4, 6, 8, 10, 11)),
        embed_graph(candidate_graphs[2], 12, (0, 1, 3, 4, 6, 7, 9, 11)),
    ]
    sparse = [0] * 12
    for left in range(12):
        for right in range(left + 1, 12):
            if ((left * 17 + right * 29 + left * right) % 7) < 3:
                sparse[left] |= 1 << right
                sparse[right] |= 1 << left
    synthetic.append(tuple(sparse))
    graph_path = output_directory / "cross_order12.g6"
    graph_path.write_text(
        "".join(encode_graph6(graph) + "\n" for graph in synthetic),
        encoding="ascii",
        newline="\n",
    )
    incidence_path = output_directory / "cross_incidence.bin"
    completed = subprocess.run(
        [
            str(scanner),
            "--candidates", str(candidate_path),
            "--r44-12", str(graph_path),
            "--output", str(incidence_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    incidence = structural_cover.read_incidence(incidence_path)
    closures = tuple(
        {
            relabelled_mask(graph, permutation)
            for permutation in itertools.permutations(range(len(graph)))
        }
        for graph in candidate_graphs
    )
    expected = [0] * len(chosen)
    for graph_index, graph in enumerate(synthetic):
        for candidate_index, item in enumerate(chosen):
            if any(
                induced_mask(graph, vertices) in closures[candidate_index]
                for vertices in itertools.combinations(range(12), item.order)
            ):
                expected[candidate_index] |= 1 << graph_index
    if tuple(expected) != incidence.covers:
        raise AssertionError(
            f"native/Python incidence mismatch: {incidence.covers} != {tuple(expected)}"
        )
    report = {
        "schema_version": 1,
        "status": "PASS",
        "method": "native BMI2 incidence equals exhaustive pure-Python permutation oracle",
        "synthetic_graphs": len(synthetic),
        "candidates": len(chosen),
        "candidate_sha256": structural_cover.sha256(candidate_path),
        "input_sha256": structural_cover.sha256(graph_path),
        "incidence_sha256": structural_cover.sha256(incidence_path),
        "native_stdout": completed.stdout.strip().splitlines(),
        "padding_bits_zero": True,
    }
    (output_directory / "cross_check.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scanner", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.scanner, args.source, args.output), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
