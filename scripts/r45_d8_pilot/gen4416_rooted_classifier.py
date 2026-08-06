#!/usr/bin/env python3
"""Build and verify a rooted SAT prototype for the ``gen4416`` right cover.

This experiment classifies the 56 cross edges of a rooted ``R(4,4,16)``
graph.  A degree-seven root splits the other vertices into its seven
neighbours ``L`` and eight non-neighbours ``A``.  The graph on ``L`` and the
*complement* of the graph on ``A`` are both ``R(3,4)`` graphs.  Their
certified-catalogue representatives leave only 27 selector pairs.

The generated CNF selects one pair, enforces all mixed K4/independent-K4
constraints, and then blocks the 64 cross masks obtained from the two
``gen4416`` graphs under every relevant local isomorphism.  UNSAT therefore
certifies the finite, rooted cross-mask classification, conditional on the
catalogue reduction represented by the selectors.  The generator also keeps
one deterministic global isomorphism for every allowed mask and emits the
small Lean data module used to check the two target graphs.

Only repository inputs are used.  ``build`` never overwrites a differing
artifact; ``verify`` reconstructs every byte, including the Lean cover data,
and checks the mathematical invariants independently of stored metadata.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import os
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence


SCHEMA_VERSION = 1
HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
R55 = REPOSITORY / "r55"
GEN4416 = HERE / "data" / "gen4416"
R35_7 = R55 / "r35_7.g6"
R35_8 = R55 / "r35_8.g6"
DEFAULT_OUTPUT = HERE / "gen4416_rooted_classification"
LEAN_COVER_DATA = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44RootedGen4416CoverData.lean"
)

ALLOWED_TABLE_NAME = "allowed_models.txt"
CNF_NAME = "guarded_counterexample.cnf"
METADATA_NAME = "metadata.json"
LRAT_NAME = "guarded_counterexample.lrat"
SOLVER_LOG_NAME = "solver.log"
PROOF_METADATA_NAME = "proof_metadata.json"

LEFT_CATALOGUE_INDICES = (46, 53, 58, 63, 65, 66, 68, 69, 70)
ANTI_CATALOGUE_INDICES = (90, 163, 176)
EXPECTED_INPUT_HASHES = {
    "gen4416": "D342D951433311239BA7AB5C0EEF809A7588B41C0E8A472E8930BD77D5489C6C",
    "r35_7.g6": "DB838EEDFFE06069481E392FB6635C616A38A3C42BD130BA945B51B9B47A7AC2",
    "r35_8.g6": "6832892B9953C2DBB34A2BD9C9E4B3E1C38BAD272993925C46A65F21F1D0F807",
}

CROSS_VARIABLE_COUNT = 7 * 8
SELECTOR_COUNT = len(LEFT_CATALOGUE_INDICES) * len(ANTI_CATALOGUE_INDICES)
VARIABLE_COUNT = CROSS_VARIABLE_COUNT + SELECTOR_COUNT


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load Python module from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


ramsey = load_module("gen4416_rooted_ramsey", R55 / "ramsey.py")
cover = load_module(
    "gen4416_rooted_cover_checker", HERE / "check_barakeel_covers.py"
)
Graph = tuple[int, ...]


class ClassificationError(ValueError):
    """Raised when an input or generated artifact violates the schema."""


@dataclass(frozen=True, order=True)
class AllowedModel:
    left_selector: int
    anti_selector: int
    mask: int


@dataclass(frozen=True)
class RootAudit:
    graph_index: int
    graph_id: int
    root: int
    left_selector: int
    anti_selector: int
    left_isomorphisms: int
    anti_isomorphisms: int
    isomorphism_products: int
    distinct_masks: int


@dataclass(frozen=True, order=True)
class ModelCoverWitness:
    model: AllowedModel
    graph_index: int
    permutation: tuple[int, ...]


@dataclass(frozen=True)
class BuildResult:
    allowed_models: tuple[AllowedModel, ...]
    cover_witnesses: tuple[ModelCoverWitness, ...]
    self_complement_permutations: tuple[tuple[int, ...], ...]
    clauses: tuple[tuple[int, ...], ...]
    table_bytes: bytes
    cnf_bytes: bytes
    lean_data_bytes: bytes
    metadata_bytes: bytes
    metadata: dict[str, object]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def edge(graph: Graph, left: int, right: int) -> bool:
    return bool((graph[left] >> right) & 1)


def graph_from_ternary(encoded: int, order: int, context: str) -> Graph:
    colours = cover.decode_edges(encoded, order, context)
    if any(colour not in (1, 2) for colour in colours):
        raise ClassificationError(f"{context}: expected a fully coloured graph")
    rows = [0] * order
    for colour, (left, right) in zip(colours, cover.edge_pairs(order), strict=True):
        # Direct Lean orientation: HOL colour 1 is a raw/true edge.
        if colour == 1:
            rows[left] |= 1 << right
            rows[right] |= 1 << left
    graph = tuple(rows)
    ramsey.validate_graph(graph)
    return graph


def induced_graph(graph: Graph, vertices: Sequence[int]) -> Graph:
    if len(set(vertices)) != len(vertices):
        raise ClassificationError("induced vertex list contains a duplicate")
    if any(vertex < 0 or vertex >= len(graph) for vertex in vertices):
        raise ClassificationError("induced vertex lies outside the graph")
    rows = [0] * len(vertices)
    for left in range(len(vertices)):
        for right in range(left + 1, len(vertices)):
            if edge(graph, vertices[left], vertices[right]):
                rows[left] |= 1 << right
                rows[right] |= 1 << left
    result = tuple(rows)
    ramsey.validate_graph(result)
    return result


def is_r34_free(graph: Graph) -> bool:
    return (
        ramsey.count_cliques(graph, 3) == 0
        and ramsey.count_cliques(ramsey.complement_graph(graph), 4) == 0
    )


def all_isomorphisms(source: Graph, target: Graph) -> tuple[tuple[int, ...], ...]:
    """Enumerate every source-to-target isomorphism deterministically."""

    ramsey.validate_graph(source)
    ramsey.validate_graph(target)
    if len(source) != len(target):
        return ()
    order = len(source)
    source_degrees = tuple(row.bit_count() for row in source)
    target_degrees = tuple(row.bit_count() for row in target)
    if sorted(source_degrees) != sorted(target_degrees):
        return ()

    # Degree plus neighbour-degree multiset is an inexpensive stable filter.
    def signature(graph: Graph, degrees: Sequence[int], vertex: int):
        return (
            degrees[vertex],
            tuple(
                sorted(
                    degrees[neighbor]
                    for neighbor in range(order)
                    if edge(graph, vertex, neighbor)
                )
            ),
        )

    source_signatures = tuple(
        signature(source, source_degrees, vertex) for vertex in range(order)
    )
    target_signatures = tuple(
        signature(target, target_degrees, vertex) for vertex in range(order)
    )
    if sorted(source_signatures) != sorted(target_signatures):
        return ()

    candidates = tuple(
        tuple(
            target_vertex
            for target_vertex in range(order)
            if target_signatures[target_vertex] == source_signatures[source_vertex]
        )
        for source_vertex in range(order)
    )
    mapping = [-1] * order
    results: list[tuple[int, ...]] = []

    def visit(mapped: int, used: int) -> None:
        if mapped == order:
            result = tuple(mapping)
            if not is_isomorphism(source, target, result):
                raise AssertionError("backtracking emitted a non-isomorphism")
            results.append(result)
            return

        best_source = -1
        best_targets: tuple[int, ...] | None = None
        for source_vertex in range(order):
            if mapping[source_vertex] >= 0:
                continue
            compatible = tuple(
                target_vertex
                for target_vertex in candidates[source_vertex]
                if not ((used >> target_vertex) & 1)
                and all(
                    edge(source, source_vertex, other_source)
                    == edge(target, target_vertex, mapping[other_source])
                    for other_source in range(order)
                    if mapping[other_source] >= 0
                )
            )
            if not compatible:
                return
            if best_targets is None or len(compatible) < len(best_targets):
                best_source = source_vertex
                best_targets = compatible

        assert best_source >= 0 and best_targets is not None
        for target_vertex in best_targets:
            mapping[best_source] = target_vertex
            visit(mapped + 1, used | (1 << target_vertex))
            mapping[best_source] = -1

    visit(0, 0)
    return tuple(sorted(results))


def is_isomorphism(
    source: Graph, target: Graph, permutation: Sequence[int]
) -> bool:
    if len(source) != len(target) or sorted(permutation) != list(range(len(source))):
        return False
    return all(
        edge(source, left, right)
        == edge(target, permutation[left], permutation[right])
        for left in range(len(source))
        for right in range(left + 1, len(source))
    )


def read_catalogue(path: Path, expected_order: int) -> tuple[Graph, ...]:
    records = tuple(
        line.strip()
        for line in path.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    graphs = tuple(ramsey.decode_graph6(record) for record in records)
    if any(len(graph) != expected_order for graph in graphs):
        raise ClassificationError(f"{path}: graph6 order mismatch")
    return graphs


def read_gen4416() -> tuple[tuple[int, Graph], ...]:
    stats = cover.check_cover(GEN4416)
    if (
        stats.family != "44"
        or stats.order != 16
        or stats.records != 2
        or stats.instances != 2
        or stats.parent_holes_total != 0
    ):
        raise ClassificationError(f"unexpected gen4416 structure: {stats}")

    result: list[tuple[int, Graph]] = []
    for line_number, raw_line in enumerate(
        GEN4416.read_text(encoding="ascii").splitlines(), 1
    ):
        fields = raw_line.split()
        if len(fields) != 2:
            raise ClassificationError(f"gen4416:{line_number}: expected one child")
        parent_id = int(fields[0], 10)
        child_id, permutation = cover.parse_child_token(
            fields[1], 16, f"gen4416:{line_number}:child"
        )
        if child_id != parent_id or permutation != list(range(16)):
            raise ClassificationError(
                f"gen4416:{line_number}: expected the complete parent as identity child"
            )
        graph = graph_from_ternary(parent_id, 16, f"gen4416:{line_number}")
        if ramsey.count_cliques(graph, 4) != 0:
            raise ClassificationError(f"gen4416:{line_number}: contains a K4")
        if ramsey.count_cliques(ramsey.complement_graph(graph), 4) != 0:
            raise ClassificationError(
                f"gen4416:{line_number}: contains an independent four-set"
            )
        result.append((parent_id, graph))
    return tuple(result)


def selector_variable(left_selector: int, anti_selector: int) -> int:
    if not 0 <= left_selector < len(LEFT_CATALOGUE_INDICES):
        raise ValueError("left selector outside 0..8")
    if not 0 <= anti_selector < len(ANTI_CATALOGUE_INDICES):
        raise ValueError("anti selector outside 0..2")
    return 57 + 3 * left_selector + anti_selector


def cross_variable(left: int, anti: int) -> int:
    if not 0 <= left < 7 or not 0 <= anti < 8:
        raise ValueError("cross coordinate outside 7 x 8")
    return 1 + 8 * left + anti


def cross_mask(
    graph: Graph,
    left_vertices: Sequence[int],
    anti_vertices: Sequence[int],
    left_isomorphism: Sequence[int],
    anti_isomorphism: Sequence[int],
) -> int:
    """Encode raw cross edges after mapping both sides to representatives."""

    mask = 0
    assigned = 0
    for source_left, original_left in enumerate(left_vertices):
        canonical_left = left_isomorphism[source_left]
        for source_anti, original_anti in enumerate(anti_vertices):
            canonical_anti = anti_isomorphism[source_anti]
            bit = 8 * canonical_left + canonical_anti
            if (assigned >> bit) & 1:
                raise AssertionError("isomorphisms assigned a cross bit twice")
            assigned |= 1 << bit
            if edge(graph, original_left, original_anti):
                mask |= 1 << bit
    if assigned != (1 << CROSS_VARIABLE_COUNT) - 1:
        raise AssertionError("isomorphisms did not assign every cross bit")
    return mask


def inverse_permutation(permutation: Sequence[int]) -> tuple[int, ...]:
    if sorted(permutation) != list(range(len(permutation))):
        raise ClassificationError("cannot invert a non-permutation")
    inverse = [0] * len(permutation)
    for source, target in enumerate(permutation):
        inverse[target] = source
    return tuple(inverse)


def rooted_completion(
    left_graph: Graph, anti_complement: Graph, mask: int
) -> Graph:
    """Materialize canonical labels L=0..6, A=7..14, root=15."""

    if len(left_graph) != 7 or len(anti_complement) != 8:
        raise ClassificationError("rooted completion expects orders seven and eight")
    if not 0 <= mask < 1 << CROSS_VARIABLE_COUNT:
        raise ClassificationError("rooted completion mask lies outside 56 bits")
    rows = [0] * 16

    def set_edge(left: int, right: int) -> None:
        rows[left] |= 1 << right
        rows[right] |= 1 << left

    for left in range(7):
        set_edge(left, 15)
        for right in range(left + 1, 7):
            if edge(left_graph, left, right):
                set_edge(left, right)
    for anti in range(8):
        for other in range(anti + 1, 8):
            # The selector stores complement(A), while this graph stores raw A.
            if not edge(anti_complement, anti, other):
                set_edge(7 + anti, 7 + other)
    for left in range(7):
        for anti in range(8):
            if (mask >> (8 * left + anti)) & 1:
                set_edge(left, 7 + anti)
    result = tuple(rows)
    ramsey.validate_graph(result)
    return result


def rooted_global_permutation(
    root: int,
    left_vertices: Sequence[int],
    anti_vertices: Sequence[int],
    left_isomorphism: Sequence[int],
    anti_isomorphism: Sequence[int],
) -> tuple[int, ...]:
    """Map canonical L,A,root labels to the original gen4416 graph."""

    if len(left_vertices) != 7 or len(anti_vertices) != 8:
        raise ClassificationError("rooted global permutation expects a 7 + 8 split")
    left_inverse = inverse_permutation(left_isomorphism)
    anti_inverse = inverse_permutation(anti_isomorphism)
    result = (
        tuple(left_vertices[left_inverse[canonical]] for canonical in range(7))
        + tuple(
            anti_vertices[anti_inverse[canonical]] for canonical in range(8)
        )
        + (root,)
    )
    if sorted(result) != list(range(16)):
        raise ClassificationError("rooted global map is not a permutation of 16")
    return result


def target_index_for_model(model: AllowedModel) -> int:
    pair = (model.left_selector, model.anti_selector)
    if pair == (0, 2):
        return 1
    if pair == (8, 0):
        return 0
    raise ClassificationError(f"allowed model has no gen4416 target: {pair}")


def extract_allowed_models(
    gen_graphs: Sequence[tuple[int, Graph]],
    left_representatives: Sequence[Graph],
    anti_representatives: Sequence[Graph],
) -> tuple[
    tuple[AllowedModel, ...],
    tuple[RootAudit, ...],
    tuple[ModelCoverWitness, ...],
]:
    left_lookup = {
        LEFT_CATALOGUE_INDICES[index]: index
        for index in range(len(LEFT_CATALOGUE_INDICES))
    }
    anti_lookup = {
        ANTI_CATALOGUE_INDICES[index]: index
        for index in range(len(ANTI_CATALOGUE_INDICES))
    }
    del left_lookup, anti_lookup  # indices are documented; matches below are explicit

    allowed: set[AllowedModel] = set()
    cover_candidates: defaultdict[
        AllowedModel, set[ModelCoverWitness]
    ] = defaultdict(set)
    audits: list[RootAudit] = []
    for graph_index, (graph_id, graph) in enumerate(gen_graphs):
        degree_seven_roots = tuple(
            vertex for vertex, row in enumerate(graph) if row.bit_count() == 7
        )
        if len(degree_seven_roots) != 8:
            raise ClassificationError(
                f"gen4416 graph {graph_index}: expected 8 degree-seven roots, "
                f"got {len(degree_seven_roots)}"
            )
        for root in degree_seven_roots:
            left_vertices = tuple(
                vertex for vertex in range(16) if edge(graph, root, vertex)
            )
            anti_vertices = tuple(
                vertex
                for vertex in range(16)
                if vertex != root and not edge(graph, root, vertex)
            )
            if len(left_vertices) != 7 or len(anti_vertices) != 8:
                raise AssertionError("degree-seven root did not split 7 + 8")
            left_graph = induced_graph(graph, left_vertices)
            anti_complement = ramsey.complement_graph(
                induced_graph(graph, anti_vertices)
            )
            if not is_r34_free(left_graph) or not is_r34_free(anti_complement):
                raise ClassificationError(
                    f"gen4416 graph {graph_index}, root {root}: bad R(3,4) side"
                )

            left_matches: list[tuple[int, tuple[tuple[int, ...], ...]]] = []
            for selector, representative in enumerate(left_representatives):
                isomorphisms = all_isomorphisms(left_graph, representative)
                if isomorphisms:
                    left_matches.append((selector, isomorphisms))
            anti_matches: list[tuple[int, tuple[tuple[int, ...], ...]]] = []
            for selector, representative in enumerate(anti_representatives):
                isomorphisms = all_isomorphisms(anti_complement, representative)
                if isomorphisms:
                    anti_matches.append((selector, isomorphisms))
            if len(left_matches) != 1 or len(anti_matches) != 1:
                raise ClassificationError(
                    f"gen4416 graph {graph_index}, root {root}: expected unique "
                    f"catalogue classes, got {len(left_matches)} x {len(anti_matches)}"
                )
            left_selector, left_isomorphisms = left_matches[0]
            anti_selector, anti_isomorphisms = anti_matches[0]
            root_models: set[AllowedModel] = set()
            for left_iso in left_isomorphisms:
                for anti_iso in anti_isomorphisms:
                    model = AllowedModel(
                        left_selector,
                        anti_selector,
                        cross_mask(
                            graph,
                            left_vertices,
                            anti_vertices,
                            left_iso,
                            anti_iso,
                        ),
                    )
                    permutation = rooted_global_permutation(
                        root,
                        left_vertices,
                        anti_vertices,
                        left_iso,
                        anti_iso,
                    )
                    canonical = rooted_completion(
                        left_representatives[left_selector],
                        anti_representatives[anti_selector],
                        model.mask,
                    )
                    if not is_isomorphism(canonical, graph, permutation):
                        raise ClassificationError(
                            "rooted global permutation is not an isomorphism"
                        )
                    if target_index_for_model(model) != graph_index:
                        raise ClassificationError(
                            f"model {model} unexpectedly targets graph {graph_index}"
                        )
                    root_models.add(model)
                    cover_candidates[model].add(
                        ModelCoverWitness(model, graph_index, permutation)
                    )
            allowed.update(root_models)
            audits.append(
                RootAudit(
                    graph_index=graph_index,
                    graph_id=graph_id,
                    root=root,
                    left_selector=left_selector,
                    anti_selector=anti_selector,
                    left_isomorphisms=len(left_isomorphisms),
                    anti_isomorphisms=len(anti_isomorphisms),
                    isomorphism_products=len(left_isomorphisms)
                    * len(anti_isomorphisms),
                    distinct_masks=len(root_models),
                )
            )

    result = tuple(sorted(allowed))
    counts = Counter((model.left_selector, model.anti_selector) for model in result)
    expected_counts = {(0, 2): 32, (8, 0): 32}
    if len(result) != 64 or dict(counts) != expected_counts:
        raise ClassificationError(
            f"unexpected allowed-model distribution: {len(result)}, {dict(counts)}"
        )
    if set(cover_candidates) != set(result):
        raise ClassificationError("cover provenance does not match allowed models")
    witnesses = tuple(
        min(
            cover_candidates[model],
            key=lambda witness: (witness.graph_index, witness.permutation),
        )
        for model in result
    )
    return result, tuple(audits), witnesses


def self_complement_permutations(
    gen_graphs: Sequence[tuple[int, Graph]],
) -> tuple[tuple[int, ...], ...]:
    result: list[tuple[int, ...]] = []
    for graph_index, (_graph_id, graph) in enumerate(gen_graphs):
        complement = ramsey.complement_graph(graph)
        isomorphisms = all_isomorphisms(complement, graph)
        if not isomorphisms:
            raise ClassificationError(
                f"gen4416 graph {graph_index} is not self-complementary"
            )
        result.append(min(isomorphisms))
    return tuple(result)


def triples(vertices: range | Sequence[int]) -> Iterator[tuple[int, int, int]]:
    yield from itertools.combinations(vertices, 3)


def pairs(vertices: range | Sequence[int]) -> Iterator[tuple[int, int]]:
    yield from itertools.combinations(vertices, 2)


def is_clique(graph: Graph, vertices: Sequence[int]) -> bool:
    return all(edge(graph, left, right) for left, right in pairs(vertices))


def is_independent(graph: Graph, vertices: Sequence[int]) -> bool:
    return all(not edge(graph, left, right) for left, right in pairs(vertices))


def guarded_local_clauses(
    left_selector: int,
    anti_selector: int,
    left_graph: Graph,
    anti_complement: Graph,
) -> tuple[tuple[str, tuple[int, ...]], ...]:
    """Mixed K4/I4 constraints for one selected representative pair."""

    selector = selector_variable(left_selector, anti_selector)
    clauses: list[tuple[str, tuple[int, ...]]] = []

    # Raw A triangles are independent triples in complement(A).
    for anti_triple in triples(range(8)):
        if is_independent(anti_complement, anti_triple):
            for left in range(7):
                clauses.append(
                    (
                        "k4_1left_3anti",
                        (-selector,)
                        + tuple(-cross_variable(left, anti) for anti in anti_triple),
                    )
                )

    # Raw A edges are non-edges in complement(A).
    for left_pair in pairs(range(7)):
        if not edge(left_graph, *left_pair):
            continue
        for anti_pair in pairs(range(8)):
            if edge(anti_complement, *anti_pair):
                continue
            clauses.append(
                (
                    "k4_2left_2anti",
                    (-selector,)
                    + tuple(
                        -cross_variable(left, anti)
                        for left in left_pair
                        for anti in anti_pair
                    ),
                )
            )

    for left_triple in triples(range(7)):
        if is_independent(left_graph, left_triple):
            for anti in range(8):
                clauses.append(
                    (
                        "i4_3left_1anti",
                        (-selector,)
                        + tuple(cross_variable(left, anti) for left in left_triple),
                    )
                )

    # Raw A non-edges are edges in complement(A).
    for left_pair in pairs(range(7)):
        if edge(left_graph, *left_pair):
            continue
        for anti_pair in pairs(range(8)):
            if not edge(anti_complement, *anti_pair):
                continue
            clauses.append(
                (
                    "i4_2left_2anti",
                    (-selector,)
                    + tuple(
                        cross_variable(left, anti)
                        for left in left_pair
                        for anti in anti_pair
                    ),
                )
            )
    return tuple(clauses)


def mask_blocking_clause(model: AllowedModel) -> tuple[int, ...]:
    selector = selector_variable(model.left_selector, model.anti_selector)
    return (-selector,) + tuple(
        -variable if (model.mask >> (variable - 1)) & 1 else variable
        for variable in range(1, CROSS_VARIABLE_COUNT + 1)
    )


def generate_clauses(
    left_representatives: Sequence[Graph],
    anti_representatives: Sequence[Graph],
    allowed_models: Sequence[AllowedModel],
) -> tuple[tuple[tuple[int, ...], ...], Counter[str], tuple[dict[str, object], ...]]:
    clauses: list[tuple[int, ...]] = [
        tuple(
            selector_variable(left_selector, anti_selector)
            for left_selector in range(len(left_representatives))
            for anti_selector in range(len(anti_representatives))
        )
    ]
    breakdown: Counter[str] = Counter({"selector_at_least_one": 1})
    pair_metadata: list[dict[str, object]] = []
    allowed_counts = Counter(
        (model.left_selector, model.anti_selector) for model in allowed_models
    )
    for left_selector, left_graph in enumerate(left_representatives):
        for anti_selector, anti_graph in enumerate(anti_representatives):
            local = guarded_local_clauses(
                left_selector, anti_selector, left_graph, anti_graph
            )
            clauses.extend(clause for _kind, clause in local)
            local_counts = Counter(kind for kind, _clause in local)
            breakdown.update(local_counts)
            pair_metadata.append(
                {
                    "left_selector": left_selector,
                    "left_catalogue_index": LEFT_CATALOGUE_INDICES[left_selector],
                    "anti_selector": anti_selector,
                    "anti_catalogue_index": ANTI_CATALOGUE_INDICES[anti_selector],
                    "selector_variable": selector_variable(
                        left_selector, anti_selector
                    ),
                    "local_clause_counts": dict(sorted(local_counts.items())),
                    "allowed_model_count": allowed_counts[
                        (left_selector, anti_selector)
                    ],
                }
            )
    blockers = tuple(mask_blocking_clause(model) for model in allowed_models)
    clauses.extend(blockers)
    breakdown["allowed_model_blockers"] += len(blockers)
    return tuple(clauses), breakdown, tuple(pair_metadata)


def render_allowed_table(allowed_models: Sequence[AllowedModel]) -> bytes:
    return "".join(
        f"{model.left_selector} {model.anti_selector} {model.mask}\n"
        for model in allowed_models
    ).encode("ascii")


def lean_list(values: Sequence[int]) -> str:
    return "[" + ",".join(map(str, values)) + "]"


def render_lean_cover_data(
    gen_graphs: Sequence[tuple[int, Graph]],
    allowed_models: Sequence[AllowedModel],
    cover_witnesses: Sequence[ModelCoverWitness],
    complements: Sequence[Sequence[int]],
    gen4416_sha256: str,
    allowed_table_sha256: str,
) -> bytes:
    if tuple(witness.model for witness in cover_witnesses) != tuple(allowed_models):
        raise ClassificationError("Lean cover witnesses are not model-aligned")
    if len(gen_graphs) != 2 or len(complements) != 2:
        raise ClassificationError("Lean cover data expects exactly two gen4416 graphs")
    lines = [
        "/- This file is generated by gen4416_rooted_classifier.py.",
        f"   gen4416 SHA-256: {gen4416_sha256}",
        f"   allowed_models.txt SHA-256: {allowed_table_sha256} -/",
        "namespace LRATCatcher.Tests.R44RootedGen4416CoverData",
        "",
        "def gen4416GraphIds : List Nat := "
        + lean_list([graph_id for graph_id, _graph in gen_graphs]),
        "",
        "def gen4416TargetIndexForSelectors",
        "    (leftSelector antiSelector : Nat) : Nat :=",
        "  if leftSelector == 0 && antiSelector == 2 then 1 else 0",
        "",
        "def gen4416CoverPermutations : List (List Nat) := [",
    ]
    for index, witness in enumerate(cover_witnesses):
        suffix = "," if index + 1 < len(cover_witnesses) else ""
        lines.append(f"  {lean_list(witness.permutation)}{suffix}")
    lines.extend(
        [
            "]",
            "",
            "def gen4416SelfComplementPermutations : List (List Nat) := [",
        ]
    )
    for index, permutation in enumerate(complements):
        suffix = "," if index + 1 < len(complements) else ""
        lines.append(f"  {lean_list(permutation)}{suffix}")
    lines.extend(
        ["]", "", "end LRATCatcher.Tests.R44RootedGen4416CoverData", ""]
    )
    return "\n".join(lines).encode("utf-8")


def render_cnf(clauses: Sequence[Sequence[int]], source_hashes: dict[str, str]) -> bytes:
    lines = [
        "c rooted gen4416 counterexample classifier",
        "c x(i,j)=1+8*i+j for 0<=i<7, 0<=j<8; 1 means raw edge",
        "c s(a,b)=57+3*a+b for 0<=a<9, 0<=b<3",
        f"c gen4416 sha256 {source_hashes['gen4416']}",
        f"c r35_7.g6 sha256 {source_hashes['r35_7.g6']}",
        f"c r35_8.g6 sha256 {source_hashes['r35_8.g6']}",
        f"p cnf {VARIABLE_COUNT} {len(clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    return ("\n".join(lines) + "\n").encode("ascii")


def build_result() -> BuildResult:
    source_paths = {
        "gen4416": GEN4416,
        "r35_7.g6": R35_7,
        "r35_8.g6": R35_8,
    }
    source_hashes = {name: sha256_file(path) for name, path in source_paths.items()}
    if source_hashes != EXPECTED_INPUT_HASHES:
        raise ClassificationError(
            f"input hashes differ from the audited repository data: {source_hashes}"
        )

    catalogue7 = read_catalogue(R35_7, 7)
    catalogue8 = read_catalogue(R35_8, 8)
    if len(catalogue7) != 71 or len(catalogue8) != 179:
        raise ClassificationError(
            f"unexpected catalogue lengths: {len(catalogue7)}, {len(catalogue8)}"
        )
    left_representatives = tuple(catalogue7[index] for index in LEFT_CATALOGUE_INDICES)
    anti_representatives = tuple(catalogue8[index] for index in ANTI_CATALOGUE_INDICES)
    if not all(is_r34_free(graph) for graph in left_representatives):
        raise ClassificationError("selected order-seven graph is not R(3,4)-free")
    if not all(is_r34_free(graph) for graph in anti_representatives):
        raise ClassificationError("selected order-eight graph is not R(3,4)-free")

    gen_graphs = read_gen4416()
    complements = self_complement_permutations(gen_graphs)
    allowed_models, root_audits, cover_witnesses = extract_allowed_models(
        gen_graphs, left_representatives, anti_representatives
    )
    clauses, breakdown, pair_metadata = generate_clauses(
        left_representatives, anti_representatives, allowed_models
    )
    validate_clauses(clauses)
    validate_allowed_models(
        allowed_models, left_representatives, anti_representatives
    )

    table_bytes = render_allowed_table(allowed_models)
    lean_data_bytes = render_lean_cover_data(
        gen_graphs,
        allowed_models,
        cover_witnesses,
        complements,
        source_hashes["gen4416"],
        sha256_bytes(table_bytes),
    )
    cnf_bytes = render_cnf(clauses, source_hashes)
    metadata: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "status": "ROOTED_CNF_UNSAT_WITH_REPRODUCIBLE_GEN4416_COVER_DATA",
        "scope": (
            "guarded finite cross-mask classification for a degree-seven root "
            "of an R(4,4,16) graph"
        ),
        "lean_replay": {
            "module": "LRATCatcher.Tests.R44RootedGen4416Classifier",
            "theorem": "LRATCatcher.Tests.r44_rooted_gen4416_classifier_unsat",
            "scope": "unsatisfiability of the exact generated labelled CNF",
        },
        "lean_composition": {
            "cover_checker_module": (
                "LRATCatcher.Tests.R44RootedGen4416Cover"
            ),
            "target_audit_module": (
                "LRATCatcher.Tests.R44Gen4416TargetAudit"
            ),
            "classification_module": (
                "LRATCatcher.Tests.R44Gen4416Classification"
            ),
            "theorem": "ramseyFree_isomorphic_to_gen4416",
        },
        "limitations": [
            "this generated artifact covers the rooted finite CNF and witness data",
            "separate Lean modules certify the catalogue reduction, finite cover, "
            "target audit, and unrooted complement composition",
        ],
        "sources": {
            name: {
                "path": path.relative_to(REPOSITORY).as_posix(),
                "bytes": path.stat().st_size,
                "sha256": source_hashes[name],
            }
            for name, path in source_paths.items()
        },
        "catalogues": {
            "left_order": 7,
            "left_r35_indices": list(LEFT_CATALOGUE_INDICES),
            "anti_order": 8,
            "anti_represents": "complement of the raw anti-neighbour graph",
            "anti_r35_indices": list(ANTI_CATALOGUE_INDICES),
            "selector_pairs": SELECTOR_COUNT,
        },
        "gen4416": {
            "graph_ids": [str(graph_id) for graph_id, _graph in gen_graphs],
            "graphs": len(gen_graphs),
            "degree_seven_roots_per_graph": [
                sum(row.bit_count() == 7 for row in graph)
                for _graph_id, graph in gen_graphs
            ],
        },
        "variables": {
            "cross": CROSS_VARIABLE_COUNT,
            "selectors": SELECTOR_COUNT,
            "total": VARIABLE_COUNT,
            "cross_formula": "x(i,j) = 1 + 8*i + j",
            "selector_formula": "s(a,b) = 57 + 3*a + b",
        },
        "allowed_models": {
            "count": len(allowed_models),
            "counts_by_pair": {
                f"{left},{anti}": count
                for (left, anti), count in sorted(
                    Counter(
                        (model.left_selector, model.anti_selector)
                        for model in allowed_models
                    ).items()
                )
            },
            "table": ALLOWED_TABLE_NAME,
            "table_bytes": len(table_bytes),
            "table_sha256": sha256_bytes(table_bytes),
        },
        "lean_cover_data": {
            "path": LEAN_COVER_DATA.relative_to(REPOSITORY).as_posix(),
            "module": "LRATCatcher.Tests.R44RootedGen4416CoverData",
            "bytes": len(lean_data_bytes),
            "sha256": sha256_bytes(lean_data_bytes),
            "cover_witnesses": len(cover_witnesses),
            "target_counts": {
                str(graph_index): count
                for graph_index, count in sorted(
                    Counter(
                        witness.graph_index for witness in cover_witnesses
                    ).items()
                )
            },
            "self_complement_witnesses": len(complements),
            "canonical_labels": {
                "left": "0..6",
                "anti": "7..14",
                "root": 15,
            },
        },
        "root_audit": [audit.__dict__ for audit in root_audits],
        "cnf": {
            "file": CNF_NAME,
            "variables": VARIABLE_COUNT,
            "clauses": len(clauses),
            "clause_breakdown": dict(sorted(breakdown.items())),
            "bytes": len(cnf_bytes),
            "sha256": sha256_bytes(cnf_bytes),
        },
        "selector_pairs": list(pair_metadata),
        "recommended_lrat_command": (
            "cadical --lrat --no-binary --checkproof=2 "
            f"{CNF_NAME} {LRAT_NAME}"
        ),
    }
    metadata_bytes = (
        json.dumps(metadata, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    return BuildResult(
        allowed_models=allowed_models,
        cover_witnesses=cover_witnesses,
        self_complement_permutations=complements,
        clauses=clauses,
        table_bytes=table_bytes,
        cnf_bytes=cnf_bytes,
        lean_data_bytes=lean_data_bytes,
        metadata_bytes=metadata_bytes,
        metadata=metadata,
    )


def validate_clauses(clauses: Sequence[Sequence[int]]) -> None:
    if not clauses:
        raise ClassificationError("CNF has no clauses")
    expected_selector_clause = tuple(range(57, 84))
    if tuple(clauses[0]) != expected_selector_clause:
        raise ClassificationError("first clause is not the 27-selector disjunction")
    for index, clause in enumerate(clauses):
        if not clause:
            raise ClassificationError(f"clause {index} is unexpectedly empty")
        if any(literal == 0 or abs(literal) > VARIABLE_COUNT for literal in clause):
            raise ClassificationError(f"clause {index} has an invalid literal")
        if len(set(clause)) != len(clause):
            raise ClassificationError(f"clause {index} repeats a literal")
        if any(-literal in clause for literal in clause):
            raise ClassificationError(f"clause {index} is tautological")


def clause_satisfied(clause: Sequence[int], true_variables: set[int]) -> bool:
    return any(
        (literal > 0 and literal in true_variables)
        or (literal < 0 and -literal not in true_variables)
        for literal in clause
    )


def validate_allowed_models(
    allowed_models: Sequence[AllowedModel],
    left_representatives: Sequence[Graph],
    anti_representatives: Sequence[Graph],
) -> None:
    if tuple(sorted(set(allowed_models))) != tuple(allowed_models):
        raise ClassificationError("allowed models are not sorted and unique")
    for model in allowed_models:
        local = guarded_local_clauses(
            model.left_selector,
            model.anti_selector,
            left_representatives[model.left_selector],
            anti_representatives[model.anti_selector],
        )
        true_variables = {
            selector_variable(model.left_selector, model.anti_selector)
        }
        true_variables.update(
            variable
            for variable in range(1, CROSS_VARIABLE_COUNT + 1)
            if (model.mask >> (variable - 1)) & 1
        )
        if not all(clause_satisfied(clause, true_variables) for _kind, clause in local):
            raise ClassificationError(f"allowed model violates local constraints: {model}")
        if clause_satisfied(mask_blocking_clause(model), true_variables):
            raise ClassificationError(f"blocking clause does not block model: {model}")


def parse_cnf(data: bytes) -> tuple[int, tuple[tuple[int, ...], ...]]:
    variables: int | None = None
    expected_clauses: int | None = None
    clauses: list[tuple[int, ...]] = []
    for line_number, raw_line in enumerate(data.decode("ascii").splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p "):
            if variables is not None:
                raise ClassificationError("CNF has multiple headers")
            fields = line.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ClassificationError(f"bad CNF header at line {line_number}")
            variables, expected_clauses = int(fields[2]), int(fields[3])
            continue
        if variables is None:
            raise ClassificationError("CNF clause precedes header")
        fields = tuple(int(field) for field in line.split())
        if not fields or fields[-1] != 0 or 0 in fields[:-1]:
            raise ClassificationError(f"bad clause terminator at line {line_number}")
        clauses.append(fields[:-1])
    if variables is None or expected_clauses is None:
        raise ClassificationError("CNF header missing")
    if len(clauses) != expected_clauses:
        raise ClassificationError(
            f"CNF says {expected_clauses} clauses but contains {len(clauses)}"
        )
    return variables, tuple(clauses)


def parse_allowed_table(data: bytes) -> tuple[AllowedModel, ...]:
    models: list[AllowedModel] = []
    for line_number, raw_line in enumerate(data.decode("ascii").splitlines(), 1):
        fields = raw_line.split()
        if len(fields) != 3:
            raise ClassificationError(f"allowed table line {line_number} is malformed")
        models.append(AllowedModel(*(int(field) for field in fields)))
    return tuple(models)


def write_new_or_equal(path: Path, data: bytes) -> None:
    if path.exists():
        if not path.is_file():
            raise ClassificationError(f"refusing to replace non-file {path}")
        existing = path.read_bytes()
        if existing != data:
            raise ClassificationError(
                f"refusing to overwrite differing artifact {path}; use a new output directory"
            )
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    # Exclusive creation avoids races and accidental replacement.
    with path.open("xb") as stream:
        stream.write(data)


def build(output: Path) -> dict[str, object]:
    result = build_result()
    write_new_or_equal(output / ALLOWED_TABLE_NAME, result.table_bytes)
    write_new_or_equal(LEAN_COVER_DATA, result.lean_data_bytes)
    write_new_or_equal(output / CNF_NAME, result.cnf_bytes)
    write_new_or_equal(output / METADATA_NAME, result.metadata_bytes)
    return summary(result, output)


def verify(output: Path) -> dict[str, object]:
    result = build_result()
    expected = {
        ALLOWED_TABLE_NAME: result.table_bytes,
        CNF_NAME: result.cnf_bytes,
        METADATA_NAME: result.metadata_bytes,
    }
    for name, data in expected.items():
        path = output / name
        if not path.is_file():
            raise ClassificationError(f"missing artifact {path}")
        if path.read_bytes() != data:
            raise ClassificationError(f"artifact differs from deterministic rebuild: {path}")

    if not LEAN_COVER_DATA.is_file():
        raise ClassificationError(f"missing Lean cover data {LEAN_COVER_DATA}")
    if LEAN_COVER_DATA.read_bytes() != result.lean_data_bytes:
        raise ClassificationError(
            f"Lean cover data differs from deterministic rebuild: {LEAN_COVER_DATA}"
        )
    variables, parsed_clauses = parse_cnf((output / CNF_NAME).read_bytes())
    if variables != VARIABLE_COUNT or parsed_clauses != result.clauses:
        raise ClassificationError("parsed CNF differs from generated clause sequence")
    parsed_models = parse_allowed_table((output / ALLOWED_TABLE_NAME).read_bytes())
    if parsed_models != result.allowed_models:
        raise ClassificationError("parsed model table differs from extracted models")
    stored_metadata = json.loads((output / METADATA_NAME).read_text(encoding="utf-8"))
    if stored_metadata != result.metadata:
        raise ClassificationError("parsed metadata differs from rebuilt metadata")
    return summary(result, output)


def summary(result: BuildResult, output: Path) -> dict[str, object]:
    cnf = result.metadata["cnf"]
    allowed = result.metadata["allowed_models"]
    assert isinstance(cnf, dict) and isinstance(allowed, dict)
    return {
        "status": "PASS",
        "output": str(output),
        "selector_pairs": SELECTOR_COUNT,
        "allowed_models": len(result.allowed_models),
        "cover_witnesses": len(result.cover_witnesses),
        "lean_cover_data_sha256": sha256_bytes(result.lean_data_bytes),
        "allowed_counts_by_pair": allowed["counts_by_pair"],
        "allowed_table_sha256": allowed["table_sha256"],
        "cnf_variables": VARIABLE_COUNT,
        "cnf_clauses": len(result.clauses),
        "cnf_sha256": cnf["sha256"],
    }


def solve(output: Path, solver: Path) -> dict[str, object]:
    verification = verify(output)
    solver = solver.resolve()
    if not solver.is_file():
        raise ClassificationError(f"solver not found: {solver}")
    proof = output / LRAT_NAME
    log = output / SOLVER_LOG_NAME
    proof_metadata = output / PROOF_METADATA_NAME
    for path in (proof, log, proof_metadata):
        if path.exists():
            raise ClassificationError(
                f"refusing to overwrite solver artifact {path}; choose a new output directory"
            )

    command = [
        str(solver),
        "--lrat",
        "--no-binary",
        "--checkproof=2",
        CNF_NAME,
        LRAT_NAME,
    ]
    completed = subprocess.run(
        command,
        cwd=output,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    normalized_log = (
        "\n".join(line.rstrip() for line in completed.stdout.splitlines()) + "\n"
    )
    write_new_or_equal(log, normalized_log.encode("utf-8"))
    if completed.returncode != 20 or "s UNSATISFIABLE" not in completed.stdout:
        raise ClassificationError(
            f"solver did not prove UNSAT (return code {completed.returncode}); see {log}"
        )
    if not proof.is_file() or proof.stat().st_size == 0:
        raise ClassificationError("solver reported UNSAT but emitted no LRAT proof")
    version = subprocess.run(
        [str(solver), "--version"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    ).stdout.strip()
    proof_document = {
        "schema_version": SCHEMA_VERSION,
        "status": "UNSAT_WITH_CADICAL_INTERNAL_LRAT_CHECK",
        "solver": solver.name,
        "solver_sha256": sha256_file(solver),
        "solver_version": version,
        "command": [solver.name, *command[1:]],
        "returncode": completed.returncode,
        "cnf_sha256": verification["cnf_sha256"],
        "lrat": LRAT_NAME,
        "lrat_bytes": proof.stat().st_size,
        "lrat_sha256": sha256_file(proof),
        "log": SOLVER_LOG_NAME,
        "log_sha256": sha256_file(log),
        "lean_replay": {
            "module": "LRATCatcher.Tests.R44RootedGen4416Classifier",
            "theorem": "LRATCatcher.Tests.r44_rooted_gen4416_classifier_unsat",
        },
        "validation_scope": (
            "CaDiCaL generated LRAT with --checkproof=2; the repository Lean "
            "module independently replays this exact CNF and LRAT"
        ),
    }
    proof_bytes = (
        json.dumps(proof_document, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    write_new_or_equal(proof_metadata, proof_bytes)
    return {**verification, **proof_document}


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    for name in ("build", "verify"):
        command = commands.add_parser(name)
        command.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
        command.set_defaults(action=name)
    command = commands.add_parser("solve")
    command.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    command.add_argument("--solver", type=Path, required=True)
    command.set_defaults(action="solve")
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.action == "build":
            report = build(args.output.resolve())
        elif args.action == "verify":
            report = verify(args.output.resolve())
        else:
            report = solve(args.output.resolve(), args.solver)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (ClassificationError, OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
