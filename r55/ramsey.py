"""Exact, dependency-free primitives for the Ramsey R(5,5) project.

The trusted mathematical predicate is deliberately small:

    there is a graph G on n vertices with no K_k in G or its complement.

An edge is represented by a true SAT variable.  The full CNF therefore has
one variable per unordered pair and, for every k-subset, two clauses: one
forbids all edges and the other forbids all non-edges.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Graph = tuple[int, ...]


class CnfBuilder:
    """Small deterministic Tseitin builder used for search-strengthening CNFs."""

    def __init__(self, first_auxiliary: int) -> None:
        self.next_variable = first_auxiliary
        self.clauses: list[tuple[int, ...]] = []

    def fresh(self) -> int:
        variable = self.next_variable
        self.next_variable += 1
        return variable

    def _append_normalized_clause(self, clause: Sequence[int]) -> None:
        """Append a clause after removing duplicates and tautologies.

        Some symmetry comparisons deliberately compare a vector with a
        permutation of itself.  Fixed coordinates can then produce clauses
        such as ``(-x, x)`` or ``(x, x, p)``.  They are harmless to a SAT
        solver, but proof checkers are not required to normalize them before
        replaying LRAT hints.  Emit the propositionally equivalent clean CNF
        instead.
        """

        normalized: list[int] = []
        seen: set[int] = set()
        for literal in clause:
            if -literal in seen:
                return
            if literal not in seen:
                normalized.append(literal)
                seen.add(literal)
        self.clauses.append(tuple(normalized))

    def add_at_most(
        self,
        inputs: Sequence[int],
        bound: int,
        *,
        guard: int | Sequence[int] | None = None,
    ) -> None:
        """Sinz-style sequential encoding of sum(inputs) <= bound.

        An input is a literal, not merely a variable, so the same routine
        encodes bounds on red edges and on their negations (blue edges).
        """

        inputs = tuple(inputs)

        if guard is None:
            guards: tuple[int, ...] = ()
        elif isinstance(guard, int):
            guards = (guard,)
        else:
            guards = tuple(guard)

        def emit(clause: tuple[int, ...]) -> None:
            self.clauses.append(clause + guards)

        if bound < 0:
            emit(())
            return
        if bound >= len(inputs):
            return
        if bound == 0:
            for literal in inputs:
                emit((-literal,))
            return

        # s[i,j] means: at least j inputs among positions 0..i are true.
        sequential: dict[tuple[int, int], int] = {}
        for i in range(len(inputs)):
            for j in range(1, min(bound, i + 1) + 1):
                sequential[i, j] = self.fresh()

        for i, literal in enumerate(inputs):
            emit((-literal, sequential[i, 1]))
            if i == 0:
                continue
            for j in range(1, min(bound, i) + 1):
                emit((-sequential[i - 1, j], sequential[i, j]))
            for j in range(2, min(bound, i + 1) + 1):
                emit((-literal, -sequential[i - 1, j - 1], sequential[i, j]))
            if i >= bound:
                emit((-literal, -sequential[i - 1, bound]))

    def add_lex_leq(self, left: Sequence[int], right: Sequence[int]) -> None:
        """Encode ``left <= right`` in lexicographic Boolean order.

        False precedes True.  The prefix variables are deliberately only
        forced when the prefix is equal; this existential encoding uses
        ``p-1`` auxiliaries and at most ``3p-2`` clauses for vectors of length
        ``p``.  Overlapping vectors can make some clauses redundant.
        """

        left = tuple(left)
        right = tuple(right)
        if len(left) != len(right):
            raise ValueError("lexicographic vectors must have equal length")
        if not left:
            return

        self._append_normalized_clause((-left[0], right[0]))
        previous_prefix: int | None = None
        for index in range(len(left) - 1):
            prefix = self.fresh()
            if previous_prefix is None:
                self._append_normalized_clause(
                    (left[index], right[index], prefix)
                )
                self._append_normalized_clause(
                    (-left[index], -right[index], prefix)
                )
            else:
                self._append_normalized_clause(
                    (-previous_prefix, left[index], right[index], prefix)
                )
                self._append_normalized_clause(
                    (-previous_prefix, -left[index], -right[index], prefix)
                )
            self._append_normalized_clause(
                (-prefix, -left[index + 1], right[index + 1])
            )
            previous_prefix = prefix


def edge_count(n: int) -> int:
    return n * (n - 1) // 2


def edge_var(n: int, i: int, j: int) -> int:
    """Return the one-based DIMACS variable for edge {i,j}.

    Variables are ordered lexicographically as
    (0,1), (0,2), ..., (0,n-1), (1,2), ... .
    """

    if i == j or not (0 <= i < n) or not (0 <= j < n):
        raise ValueError(f"not an edge of K_{n}: ({i}, {j})")
    if i > j:
        i, j = j, i
    offset = i * (2 * n - i - 1) // 2
    return offset + (j - i)


def graph_from_edge_bits(n: int, bits: Sequence[bool]) -> Graph:
    if len(bits) != edge_count(n):
        raise ValueError(f"expected {edge_count(n)} edge bits, got {len(bits)}")
    adjacency = [0] * n
    p = 0
    for i in range(n):
        for j in range(i + 1, n):
            if bits[p]:
                adjacency[i] |= 1 << j
                adjacency[j] |= 1 << i
            p += 1
    return tuple(adjacency)


def _graph6_order_pairs(n: int) -> Iterator[tuple[int, int]]:
    # graph6 uses the upper triangle by columns:
    # (0,1), (0,2), (1,2), (0,3), (1,3), (2,3), ...
    for j in range(1, n):
        for i in range(j):
            yield i, j


def decode_graph6(record: str) -> Graph:
    """Decode one graph6 record, including all three graph-size headers."""

    record = record.strip()
    prefix = ">>graph6<<"
    if record.startswith(prefix):
        record = record[len(prefix) :]
    if not record:
        raise ValueError("empty graph6 record")
    values = [ord(char) - 63 for char in record]
    if any(value < 0 or value > 63 for value in values):
        raise ValueError("graph6 characters must lie in ASCII range 63..126")

    if values[0] != 63:
        n = values[0]
        pos = 1
    elif len(values) >= 4 and values[1] != 63:
        n = (values[1] << 12) | (values[2] << 6) | values[3]
        pos = 4
    elif len(values) >= 8:
        n = 0
        for value in values[2:8]:
            n = (n << 6) | value
        pos = 8
    else:
        raise ValueError("truncated graph6 size header")

    payload = values[pos:]
    required_chars = (edge_count(n) + 5) // 6
    if len(payload) != required_chars:
        raise ValueError(
            f"K_{n} needs {required_chars} graph6 payload characters, "
            f"got {len(payload)}"
        )

    adjacency = [0] * n
    pairs = _graph6_order_pairs(n)
    used = 0
    for value in payload:
        for shift in range(5, -1, -1):
            if used == edge_count(n):
                if value & ((1 << (shift + 1)) - 1):
                    raise ValueError("non-zero graph6 padding bits")
                break
            i, j = next(pairs)
            if (value >> shift) & 1:
                adjacency[i] |= 1 << j
                adjacency[j] |= 1 << i
            used += 1
    return tuple(adjacency)


def has_edge(graph: Graph, i: int, j: int) -> bool:
    return bool((graph[i] >> j) & 1)


def complement_graph(graph: Graph) -> Graph:
    validate_graph(graph)
    mask = (1 << len(graph)) - 1
    return tuple((~row) & mask & ~(1 << i) for i, row in enumerate(graph))


def graph_edge_count(graph: Graph) -> int:
    validate_graph(graph)
    return sum(row.bit_count() for row in graph) // 2


def count_cliques(graph: Graph, k: int) -> int:
    """Count k-cliques exactly with a bitset branch-and-bound recursion."""

    validate_graph(graph)
    if k < 0:
        raise ValueError("clique size must be non-negative")

    def visit(candidates: int, needed: int) -> int:
        if needed == 0:
            return 1
        if candidates.bit_count() < needed:
            return 0
        total = 0
        while candidates.bit_count() >= needed:
            vertex_bit = candidates & -candidates
            vertex = vertex_bit.bit_length() - 1
            candidates ^= vertex_bit
            total += visit(candidates & graph[vertex], needed - 1)
        return total

    return visit((1 << len(graph)) - 1, k)


def ramsey_defect_counts(graph: Graph, k: int) -> tuple[int, int]:
    return count_cliques(graph, k), count_cliques(complement_graph(graph), k)


def validate_graph(graph: Graph) -> None:
    n = len(graph)
    mask = (1 << n) - 1
    for i, row in enumerate(graph):
        if row & ~mask:
            raise ValueError(f"adjacency row {i} contains a vertex outside 0..{n-1}")
        if (row >> i) & 1:
            raise ValueError(f"loop at vertex {i}")
        for j in range(i + 1, n):
            if ((row >> j) & 1) != ((graph[j] >> i) & 1):
                raise ValueError(f"asymmetric adjacency at ({i}, {j})")


def monochromatic_subsets(
    graph: Graph, k: int, *, keep: int = 0
) -> tuple[int, int, list[tuple[int, ...]], list[tuple[int, ...]]]:
    """Count K_k in the graph and in its complement.

    ``keep`` stores at most that many witnesses of each colour.  Counts always
    cover every k-subset, even when witness storage is capped.
    """

    validate_graph(graph)
    red = blue = 0
    red_examples: list[tuple[int, ...]] = []
    blue_examples: list[tuple[int, ...]] = []
    for vertices in itertools.combinations(range(len(graph)), k):
        all_red = True
        all_blue = True
        for i, j in itertools.combinations(vertices, 2):
            if has_edge(graph, i, j):
                all_blue = False
            else:
                all_red = False
            if not all_red and not all_blue:
                break
        if all_red:
            red += 1
            if len(red_examples) < keep:
                red_examples.append(vertices)
        if all_blue:
            blue += 1
            if len(blue_examples) < keep:
                blue_examples.append(vertices)
    return red, blue, red_examples, blue_examples


def is_ramsey_free(graph: Graph, k: int) -> bool:
    red, blue, _, _ = monochromatic_subsets(graph, k)
    return red == 0 and blue == 0


def ramsey_clauses(n: int, k: int) -> Iterator[tuple[int, ...]]:
    """Yield the canonical CNF for no monochromatic K_k on n vertices."""

    if not (2 <= k <= n):
        raise ValueError("require 2 <= k <= n")
    for vertices in itertools.combinations(range(n), k):
        variables = tuple(edge_var(n, i, j) for i, j in itertools.combinations(vertices, 2))
        yield tuple(-variable for variable in variables)  # no red K_k
        yield variables  # no blue K_k


def fixed_neighborhood_clauses(n: int, degree: int) -> Iterator[tuple[int, ...]]:
    """Fix N(0)={1,...,degree}, a representative under vertex relabelling."""

    if not (0 <= degree < n):
        raise ValueError("degree must lie in 0..n-1")
    for vertex in range(1, n):
        variable = edge_var(n, 0, vertex)
        yield (variable,) if vertex <= degree else (-variable,)


def ramsey_case_clauses(n: int, k: int, degree: int) -> Iterator[tuple[int, ...]]:
    yield from ramsey_clauses(n, k)
    yield from fixed_neighborhood_clauses(n, degree)


def fixed_anchor_codegree_clauses(n: int, degree: int, codegree: int) -> Iterator[tuple[int, ...]]:
    """Fix the red codegree of edge (0,1) inside the canonical N(0).

    Given N(0)={1,...,degree}, relabel its vertices so that vertex 1 has
    common red neighbors {2,...,codegree+1} with vertex 0.
    """

    if not (1 <= degree < n):
        raise ValueError("anchoring requires 1 <= degree < n")
    if not (0 <= codegree <= degree - 1):
        raise ValueError("codegree must lie in 0..degree-1")
    for vertex in range(2, degree + 1):
        variable = edge_var(n, 1, vertex)
        yield (variable,) if vertex <= codegree + 1 else (-variable,)


def fixed_anchor_type_clauses(n: int, type_graph: Graph) -> Iterator[tuple[int, ...]]:
    """Embed a labelled R(3,5,c) type on global vertices 2..c+1."""

    validate_graph(type_graph)
    codegree = len(type_graph)
    if codegree + 2 > n:
        raise ValueError("anchor type does not fit in the host graph")
    if count_cliques(type_graph, 3) or count_cliques(complement_graph(type_graph), 5):
        raise ValueError("anchor type is not an R(3,5,c) graph")
    for i, j in itertools.combinations(range(codegree), 2):
        variable = edge_var(n, i + 2, j + 2)
        yield (variable,) if has_edge(type_graph, i, j) else (-variable,)


def typed_branch_cube(n: int, degree: int, type_graph: Graph) -> tuple[int, ...]:
    """Return the assumptions fixing one anchored catalogue branch.

    The root neighbourhood is deliberately *not* repeated in the cube.  It is
    part of the common formula for a fixed root degree.  Every returned
    literal corresponds to a unit clause in the standalone typed-case CNF.
    """

    codegree = len(type_graph)
    units = itertools.chain(
        fixed_anchor_codegree_clauses(n, degree, codegree),
        fixed_anchor_type_clauses(n, type_graph),
    )
    return tuple(clause[0] for clause in units)


def incident_edge_literals(n: int, vertex: int) -> tuple[int, ...]:
    if not (0 <= vertex < n):
        raise ValueError(f"vertex {vertex} is outside K_{n}")
    return tuple(edge_var(n, vertex, other) for other in range(n) if other != vertex)


def degree_bound_encoding(n: int, maximum_per_colour: int) -> tuple[int, list[tuple[int, ...]]]:
    """Encode both colour degrees <= maximum_per_colour at every vertex.

    For n=43 and maximum 24 this is exactly 18 <= d(v) <= 24.  These
    constraints are mathematically implied by R(4,5)=25; they strengthen the
    *search* CNF.  A final proof must import that implication formally.
    """

    builder = CnfBuilder(edge_count(n) + 1)
    for vertex in range(n):
        red = incident_edge_literals(n, vertex)
        builder.add_at_most(red, maximum_per_colour)
        builder.add_at_most(tuple(-literal for literal in red), maximum_per_colour)
    return builder.next_variable - 1, builder.clauses


def rooted_degree_bound_encoding(
    n: int, degree: int, maximum_per_colour: int
) -> tuple[int, list[tuple[int, ...]]]:
    """Degree bounds specialized after fixing N(0)={1,...,degree}.

    The root edge is omitted from every counter.  For a red neighbor of the
    root it consumes one unit of the red allowance; for a blue neighbor it
    consumes one unit of the blue allowance.  This is equisatisfiable to the
    global degree window but gives the solver shorter, tighter counters.
    """

    if not (0 <= degree < n):
        raise ValueError("degree must lie in 0..n-1")
    builder = CnfBuilder(edge_count(n) + 1)
    for vertex in range(1, n):
        red = tuple(
            edge_var(n, vertex, other)
            for other in range(1, n)
            if other != vertex
        )
        if vertex <= degree:
            builder.add_at_most(red, maximum_per_colour - 1)
            builder.add_at_most(tuple(-literal for literal in red), maximum_per_colour)
        else:
            builder.add_at_most(red, maximum_per_colour)
            builder.add_at_most(tuple(-literal for literal in red), maximum_per_colour - 1)
    return builder.next_variable - 1, builder.clauses


def anchored_minimum_internal_degree_encoding(
    n: int,
    degree: int,
    codegree: int,
    first_auxiliary: int,
) -> tuple[int, list[tuple[int, ...]]]:
    """Require the anchor to have minimum red degree inside ``N_R(0)``.

    The anchored vertex 1 already has internal degree ``codegree`` through
    unit clauses.  For every other vertex of the root neighbourhood we encode
    ``internal_red_degree >= codegree``.  Coverage is sound because the anchor
    can be chosen as a minimum-degree vertex before relabelling.
    """

    if not (1 <= degree < n):
        raise ValueError("anchoring requires 1 <= degree < n")
    if not (0 <= codegree <= degree - 1):
        raise ValueError("codegree must lie in 0..degree-1")
    builder = CnfBuilder(first_auxiliary)
    side = tuple(range(1, degree + 1))
    maximum_blue = degree - 1 - codegree
    for vertex in side:
        if vertex == 1:
            continue
        internal_red = tuple(
            edge_var(n, vertex, other) for other in side if other != vertex
        )
        builder.add_at_most(tuple(-literal for literal in internal_red), maximum_blue)
    return builder.next_variable - 1, builder.clauses


def anchored_typed_minimum_internal_degree_encoding(
    n: int,
    degree: int,
    type_graph: Graph,
    first_auxiliary: int,
) -> tuple[int, list[tuple[int, ...]]]:
    """Type-specialized form of the anchored minimum-degree constraint.

    Edges from the anchor to its common neighbourhood, non-edges from the
    anchor to the remaining root neighbours, and all edges inside the type
    are already fixed.  Removing them before building counters roughly halves
    the encoding on the hard c=9/10 strata.
    """

    validate_graph(type_graph)
    codegree = len(type_graph)
    if not (1 <= degree < n):
        raise ValueError("anchoring requires 1 <= degree < n")
    if not (0 <= codegree <= degree - 1):
        raise ValueError("codegree must lie in 0..degree-1")
    if count_cliques(type_graph, 3) or count_cliques(complement_graph(type_graph), 5):
        raise ValueError("anchor type is not an R(3,5,c) graph")

    builder = CnfBuilder(first_auxiliary)
    common = tuple(range(2, codegree + 2))
    remainder = tuple(range(codegree + 2, degree + 1))

    for local_vertex, vertex in enumerate(common):
        fixed_red_degree = 1 + type_graph[local_vertex].bit_count()
        required_cross_red = codegree - fixed_red_degree
        maximum_cross_blue = len(remainder) - required_cross_red
        cross = tuple(edge_var(n, vertex, other) for other in remainder)
        builder.add_at_most(tuple(-literal for literal in cross), maximum_cross_blue)

    for vertex in remainder:
        free_internal = tuple(
            edge_var(n, vertex, other)
            for other in itertools.chain(common, remainder)
            if other != vertex
        )
        builder.add_at_most(
            tuple(-literal for literal in free_internal),
            len(free_internal) - codegree,
        )

    return builder.next_variable - 1, builder.clauses


def anchored_typed_internal_regular_encoding(
    n: int,
    degree: int,
    type_graph: Graph,
    regular_degree: int,
    first_auxiliary: int,
) -> tuple[int, list[tuple[int, ...]]]:
    """Encode exact internal regularity after specializing all typed units."""

    validate_graph(type_graph)
    codegree = len(type_graph)
    if not (1 <= degree < n):
        raise ValueError("anchoring requires 1 <= degree < n")
    if not (0 <= codegree <= degree - 1):
        raise ValueError("codegree must lie in 0..degree-1")
    if not (0 <= regular_degree <= degree - 1):
        raise ValueError("regular degree must lie in 0..degree-1")
    if codegree != regular_degree:
        raise ValueError("the fixed anchor degree must equal the regular degree")
    if count_cliques(type_graph, 3) or count_cliques(complement_graph(type_graph), 5):
        raise ValueError("anchor type is not an R(3,5,c) graph")

    builder = CnfBuilder(first_auxiliary)
    common = tuple(range(2, codegree + 2))
    remainder = tuple(range(codegree + 2, degree + 1))

    def add_exact(inputs: Sequence[int], target: int) -> None:
        builder.add_at_most(inputs, target)
        builder.add_at_most(tuple(-literal for literal in inputs), len(inputs) - target)

    for local_vertex, vertex in enumerate(common):
        fixed_red_degree = 1 + type_graph[local_vertex].bit_count()
        cross = tuple(edge_var(n, vertex, other) for other in remainder)
        add_exact(cross, regular_degree - fixed_red_degree)

    for vertex in remainder:
        free_internal = tuple(
            edge_var(n, vertex, other)
            for other in itertools.chain(common, remainder)
            if other != vertex
        )
        add_exact(free_internal, regular_degree)

    return builder.next_variable - 1, builder.clauses


def rooted_signature_lex_encoding(
    n: int,
    degree: int,
    codegree: int,
    first_auxiliary: int,
) -> tuple[int, list[tuple[int, ...]]]:
    """Sort still-interchangeable vertices by already distinguished sides.

    Vertices in ``L=N_R(0) \\ ({1} union C)`` are sorted by their adjacency
    signatures to the typed common neighbourhood ``C``.  Root non-neighbours
    are independently sorted by signatures to all of ``N_R(0)``.
    """

    if not (1 <= degree < n - 1):
        raise ValueError("root partition must have two non-empty sides")
    if not (0 <= codegree <= degree - 1):
        raise ValueError("codegree must lie in 0..degree-1")

    builder = CnfBuilder(first_auxiliary)
    side_a = tuple(range(1, degree + 1))
    common = tuple(range(2, codegree + 2))
    remainder = tuple(range(codegree + 2, degree + 1))
    side_b = tuple(range(degree + 1, n))

    for left_vertex, right_vertex in zip(remainder, remainder[1:]):
        left = tuple(edge_var(n, left_vertex, vertex) for vertex in common)
        right = tuple(edge_var(n, right_vertex, vertex) for vertex in common)
        builder.add_lex_leq(left, right)

    for left_vertex, right_vertex in zip(side_b, side_b[1:]):
        left = tuple(edge_var(n, left_vertex, vertex) for vertex in side_a)
        right = tuple(edge_var(n, right_vertex, vertex) for vertex in side_a)
        builder.add_lex_leq(left, right)

    return builder.next_variable - 1, builder.clauses


def w5_dihedral_permutations() -> tuple[tuple[int, ...], ...]:
    """Return the ten lifts of D5 preserving order inside the W5 twin pairs."""

    pairs = ((0, 9), (1, 2), (5, 6), (7, 8), (3, 4))
    permutations: list[tuple[int, ...]] = []
    for reflected in (False, True):
        for shift in range(5):
            permutation = list(range(10))
            for pair_index, pair in enumerate(pairs):
                target_index = (shift - pair_index) % 5 if reflected else (shift + pair_index) % 5
                target_pair = pairs[target_index]
                for slot in (0, 1):
                    permutation[pair[slot]] = target_pair[slot]
            permutations.append(tuple(permutation))
    return tuple(permutations)


def w5_first_signature_symmetry_encoding(
    n: int,
    degree: int,
    type_graph: Graph,
    first_auxiliary: int,
) -> tuple[int, list[tuple[int, ...]]]:
    """Break the residual 320-element automorphism group of the W5 type.

    The first remaining root neighbour is chosen jointly with an automorphism
    of ``C`` so that its ten-bit signature is canonical.  The five twin-pair
    swaps are normalized by binary clauses; nine lex comparisons handle the
    dihedral action on the quotient five-cycle.
    """

    expected = decode_graph6("Is`b?{]]?")
    if degree != 20 or type_graph != expected:
        raise ValueError("W5 symmetry breaking requires the labelled d20,c10,type312 graph")
    if n <= degree:
        raise ValueError("host graph is too small")

    builder = CnfBuilder(first_auxiliary)
    pairs = ((0, 9), (1, 2), (5, 6), (7, 8), (3, 4))
    first_remainder = len(type_graph) + 2
    signature = tuple(
        edge_var(n, first_remainder, local_vertex + 2)
        for local_vertex in range(len(type_graph))
    )

    for left, right in pairs:
        builder.clauses.append((-signature[left], signature[right]))

    for permutation in w5_dihedral_permutations()[1:]:
        transformed = tuple(signature[permutation[index]] for index in range(10))
        builder.add_lex_leq(signature, transformed)

    return builder.next_variable - 1, builder.clauses


def rooted_edge_common_bound_encoding(
    n: int, degree: int, bound: int, first_auxiliary: int
) -> tuple[int, list[tuple[int, ...]]]:
    """Conditional common-neighbor cuts across the root partition.

    If uv is red inside A=N_R(0), at most ``bound`` vertices of B can be red
    adjacent to both.  Dually, if uv is blue inside B, at most ``bound``
    vertices of A can be blue adjacent to both.  For R(5,5,43), bound=8 is
    justified by R(3,4)=9.
    """

    if not (1 <= degree < n - 1):
        raise ValueError("root partition must have two non-empty sides")
    builder = CnfBuilder(first_auxiliary)
    side_a = tuple(range(1, degree + 1))
    side_b = tuple(range(degree + 1, n))

    for u, v in itertools.combinations(side_a, 2):
        common: list[int] = []
        for w in side_b:
            indicator = builder.fresh()
            # Both cross edges red imply the indicator.
            builder.clauses.append(
                (-edge_var(n, u, w), -edge_var(n, v, w), indicator)
            )
            common.append(indicator)
        # Active exactly when uv is red.
        builder.add_at_most(common, bound, guard=-edge_var(n, u, v))

    for u, v in itertools.combinations(side_b, 2):
        common = []
        for w in side_a:
            indicator = builder.fresh()
            # Both cross edges blue imply the indicator.
            builder.clauses.append(
                (edge_var(n, u, w), edge_var(n, v, w), indicator)
            )
            common.append(indicator)
        # Active exactly when uv is blue.
        builder.add_at_most(common, bound, guard=edge_var(n, u, v))
    return builder.next_variable - 1, builder.clauses


def rooted_internal_cuts_encoding(
    n: int,
    degree: int,
    first_auxiliary: int,
    *,
    stars: bool = True,
    edges: bool = True,
    triangles: bool = True,
) -> tuple[int, list[tuple[int, ...]]]:
    """Local cuts inside both sides of a fixed root partition.

    On a side S whose root colour is sigma:
      * each vertex has sigma-degree <=13 and opposite-degree <=17;
      * a sigma-edge has at most four common sigma-neighbors in S;
      * an opposite-colour triangle has at most three common opposite-neighbors.

    The first two numeric degree bounds use R(3,5)=14 and R(4,4)=18.  The
    codegree and triangle bounds follow directly from the two forbidden K5s.
    """

    if not (1 <= degree < n - 1):
        raise ValueError("root partition must have two non-empty sides")
    builder = CnfBuilder(first_auxiliary)

    def add_side(vertices: tuple[int, ...], sigma_red: bool) -> None:
        def sigma_literal(u: int, v: int) -> int:
            variable = edge_var(n, u, v)
            return variable if sigma_red else -variable

        def tau_literal(u: int, v: int) -> int:
            return -sigma_literal(u, v)

        # Rooted local degree bounds.
        if stars:
            for u in vertices:
                sigma_edges = tuple(sigma_literal(u, v) for v in vertices if v != u)
                builder.add_at_most(sigma_edges, 13)
                builder.add_at_most(tuple(-literal for literal in sigma_edges), 17)

        # Conditional common sigma-neighbor bound for every sigma edge.
        if edges:
            for u, v in itertools.combinations(vertices, 2):
                activation = sigma_literal(u, v)
                common: list[int] = []
                for w in vertices:
                    if w == u or w == v:
                        continue
                    indicator = builder.fresh()
                    builder.clauses.append(
                        (-sigma_literal(u, w), -sigma_literal(v, w), indicator)
                    )
                    common.append(indicator)
                builder.add_at_most(common, 4, guard=-activation)

        # Conditional common tau-neighbor bound for every tau triangle.
        if triangles:
            for a, b, c in itertools.combinations(vertices, 3):
                triangle = (tau_literal(a, b), tau_literal(a, c), tau_literal(b, c))
                common = []
                for w in vertices:
                    if w == a or w == b or w == c:
                        continue
                    indicator = builder.fresh()
                    builder.clauses.append(
                        (
                            -tau_literal(a, w),
                            -tau_literal(b, w),
                            -tau_literal(c, w),
                            indicator,
                        )
                    )
                    common.append(indicator)
                builder.add_at_most(
                    common, 3, guard=tuple(-literal for literal in triangle)
                )

    add_side(tuple(range(1, degree + 1)), sigma_red=True)
    add_side(tuple(range(degree + 1, n)), sigma_red=False)
    return builder.next_variable - 1, builder.clauses


def extension_clauses(graph: Graph, k: int) -> Iterator[tuple[int, ...]]:
    """CNF for adding one vertex to a fixed Ramsey-free graph.

    Variable v+1 is true when the new vertex is adjacent to old vertex v.
    Existing red/blue (k-1)-cliques induce negative/positive clauses.
    """

    validate_graph(graph)
    for vertices in itertools.combinations(range(len(graph)), k - 1):
        all_red = True
        all_blue = True
        for i, j in itertools.combinations(vertices, 2):
            if has_edge(graph, i, j):
                all_blue = False
            else:
                all_red = False
            if not all_red and not all_blue:
                break
        variables = tuple(vertex + 1 for vertex in vertices)
        if all_red:
            yield tuple(-variable for variable in variables)
        if all_blue:
            yield variables


def write_dimacs(path: Path, variable_count: int, clauses: Iterable[Sequence[int]], clause_count: int) -> None:
    with path.open("w", encoding="ascii", newline="\n") as output:
        output.write(f"p cnf {variable_count} {clause_count}\n")
        written = 0
        for clause in clauses:
            if not clause:
                output.write("0\n")
            else:
                output.write(" ".join(str(literal) for literal in clause))
                output.write(" 0\n")
            written += 1
        if written != clause_count:
            raise ValueError(f"declared {clause_count} clauses but wrote {written}")


def write_inccnf(
    path: Path,
    clauses: Iterable[Sequence[int]],
    cubes: Iterable[Sequence[int]],
) -> None:
    """Write CaDiCaL's incremental DIMACS dialect.

    Ordinary lines form the common CNF.  Each ``a ... 0`` line is an
    independent assumption cube.  This is a search transport format: a final
    proof must still certify every UNSAT cube and the coverage theorem.
    """

    with path.open("w", encoding="ascii", newline="\n") as output:
        output.write("p inccnf\n")
        for clause in clauses:
            if clause:
                output.write(" ".join(str(literal) for literal in clause))
                output.write(" 0\n")
            else:
                output.write("0\n")
        for cube in cubes:
            output.write("a")
            if cube:
                output.write(" " + " ".join(str(literal) for literal in cube))
            output.write(" 0\n")


def parse_dimacs_model(text: str, variable_count: int) -> list[bool]:
    """Parse a SAT-solver model and reject partial or contradictory models."""

    values: list[bool | None] = [None] * variable_count
    for line in text.splitlines():
        line = line.strip()
        if not line or line[0] in "cs":
            continue
        tokens = line.split()
        if tokens[0] == "v":
            tokens = tokens[1:]
        for token in tokens:
            literal = int(token)
            if literal == 0:
                continue
            variable = abs(literal)
            if variable > variable_count:
                raise ValueError(f"model mentions out-of-range variable {variable}")
            value = literal > 0
            old = values[variable - 1]
            if old is not None and old != value:
                raise ValueError(f"contradictory values for variable {variable}")
            values[variable - 1] = value
    missing = [i + 1 for i, value in enumerate(values) if value is None]
    if missing:
        raise ValueError(f"partial model; first missing variables: {missing[:10]}")
    return [bool(value) for value in values]


def _cmd_stats(args: argparse.Namespace) -> None:
    variables = edge_count(args.n)
    clauses = 2 * math.comb(args.n, args.k)
    width = math.comb(args.k, 2)
    print(f"n={args.n} k={args.k} variables={variables} clauses={clauses} width={width}")


def _cmd_verify_g6(args: argparse.Namespace) -> None:
    graph = decode_graph6(args.record)
    red, blue, red_examples, blue_examples = monochromatic_subsets(graph, args.k, keep=3)
    print(f"n={len(graph)} k={args.k} red_K{args.k}={red} blue_K{args.k}={blue}")
    if red_examples:
        print(f"red examples: {red_examples}")
    if blue_examples:
        print(f"blue examples: {blue_examples}")
    if red or blue:
        raise SystemExit(1)


def _cmd_audit_g6(args: argparse.Namespace) -> None:
    records = [line.strip() for line in args.input.read_text(encoding="ascii").splitlines() if line.strip()]
    edge_counts: list[int] = []
    failures: list[tuple[int, int, int]] = []
    order: int | None = None
    for line_number, record in enumerate(records, 1):
        graph = decode_graph6(record)
        if order is None:
            order = len(graph)
        elif len(graph) != order:
            raise ValueError(f"mixed graph orders: line {line_number} has n={len(graph)}, expected {order}")
        red, blue = ramsey_defect_counts(graph, args.k)
        if red or blue:
            failures.append((line_number, red, blue))
        edges = graph_edge_count(graph)
        edge_counts.extend((edges, edge_count(len(graph)) - edges))

    print(f"records={len(records)} with_complements={len(edge_counts)} n={order} k={args.k}")
    print(f"invalid_records={len(failures)}")
    if failures:
        print(f"first failures={failures[:10]}")
    if edge_counts:
        print(f"edge_range={min(edge_counts)}..{max(edge_counts)}")
        if args.edge_threshold is not None:
            below = sum(edges <= args.edge_threshold for edges in edge_counts)
            print(f"edge_count<={args.edge_threshold}: {below}/{len(edge_counts)}")
    if failures:
        raise SystemExit(1)


def _cmd_write_cnf(args: argparse.Namespace) -> None:
    count = 2 * math.comb(args.n, args.k)
    write_dimacs(args.output, edge_count(args.n), ramsey_clauses(args.n, args.k), count)
    print(f"wrote {edge_count(args.n)} variables and {count} clauses to {args.output}")


def _cmd_write_case_cnf(args: argparse.Namespace) -> None:
    count = 2 * math.comb(args.n, args.k) + args.n - 1
    clauses = ramsey_case_clauses(args.n, args.k, args.degree)
    write_dimacs(args.output, edge_count(args.n), clauses, count)
    print(
        f"wrote fixed-degree case d={args.degree}: "
        f"{edge_count(args.n)} variables and {count} clauses to {args.output}"
    )


def _cmd_write_structured_case_cnf(args: argparse.Namespace) -> None:
    variable_count, degree_clauses = degree_bound_encoding(args.n, args.max_colour_degree)
    base_count = 2 * math.comb(args.n, args.k)
    count = base_count + len(degree_clauses) + args.n - 1
    clauses = itertools.chain(
        ramsey_clauses(args.n, args.k),
        degree_clauses,
        fixed_neighborhood_clauses(args.n, args.degree),
    )
    write_dimacs(args.output, variable_count, clauses, count)
    print(
        f"wrote structured case d={args.degree}: {variable_count} variables, "
        f"{count} clauses ({len(degree_clauses)} degree clauses) to {args.output}"
    )


def _cmd_write_anchored_case_cnf(args: argparse.Namespace) -> None:
    variable_count, degree_clauses = degree_bound_encoding(args.n, args.max_colour_degree)
    fixed = tuple(fixed_neighborhood_clauses(args.n, args.degree))
    anchor = tuple(fixed_anchor_codegree_clauses(args.n, args.degree, args.codegree))
    base_count = 2 * math.comb(args.n, args.k)
    count = base_count + len(degree_clauses) + len(fixed) + len(anchor)
    clauses = itertools.chain(ramsey_clauses(args.n, args.k), degree_clauses, fixed, anchor)
    write_dimacs(args.output, variable_count, clauses, count)
    print(
        f"wrote anchored case d={args.degree}, c={args.codegree}: "
        f"{variable_count} variables, {count} clauses to {args.output}"
    )


def _cmd_write_typed_case_cnf(args: argparse.Namespace) -> None:
    records = [line.strip() for line in args.catalogue.read_text(encoding="ascii").splitlines() if line.strip()]
    if not (0 <= args.index < len(records)):
        raise ValueError(f"catalogue index must lie in 0..{len(records)-1}")
    type_graph = decode_graph6(records[args.index])
    codegree = len(type_graph)
    if codegree > args.degree - 1:
        raise ValueError("anchor codegree exceeds the fixed neighborhood")

    if args.degree_encoding == "rooted":
        variable_count, degree_clauses = rooted_degree_bound_encoding(
            args.n, args.degree, args.max_colour_degree
        )
    else:
        variable_count, degree_clauses = degree_bound_encoding(args.n, args.max_colour_degree)
    cut_clauses: list[tuple[int, ...]] = []
    if args.anchor_minimum_degree:
        variable_count, minimum_degree = anchored_minimum_internal_degree_encoding(
            args.n, args.degree, codegree, variable_count + 1
        )
        cut_clauses.extend(minimum_degree)
    elif args.anchor_minimum_degree_specialized:
        variable_count, minimum_degree = anchored_typed_minimum_internal_degree_encoding(
            args.n, args.degree, type_graph, variable_count + 1
        )
        cut_clauses.extend(minimum_degree)
    if args.d20_c10_regularity:
        if args.degree != 20 or codegree != 10:
            raise ValueError("--d20-c10-regularity requires degree=20 and codegree=10")
        variable_count, regularity = anchored_typed_internal_regular_encoding(
            args.n, args.degree, type_graph, 10, variable_count + 1
        )
        cut_clauses.extend(regularity)
    if args.signature_lex:
        variable_count, lex_clauses = rooted_signature_lex_encoding(
            args.n, args.degree, codegree, variable_count + 1
        )
        cut_clauses.extend(lex_clauses)
    if args.w5_first_signature_symmetry:
        variable_count, w5_clauses = w5_first_signature_symmetry_encoding(
            args.n, args.degree, type_graph, variable_count + 1
        )
        cut_clauses.extend(w5_clauses)
    if (
        args.internal_cuts
        or args.internal_star_cuts
        or args.internal_edge_cuts
        or args.internal_triangle_cuts
    ):
        variable_count, internal = rooted_internal_cuts_encoding(
            args.n,
            args.degree,
            variable_count + 1,
            stars=args.internal_cuts or args.internal_star_cuts,
            edges=args.internal_cuts or args.internal_edge_cuts,
            triangles=args.internal_cuts or args.internal_triangle_cuts,
        )
        cut_clauses.extend(internal)
    if args.edge_common_bound is not None:
        variable_count, crossing = rooted_edge_common_bound_encoding(
            args.n, args.degree, args.edge_common_bound, variable_count + 1
        )
        cut_clauses.extend(crossing)
    fixed = tuple(fixed_neighborhood_clauses(args.n, args.degree))
    anchor = tuple(fixed_anchor_codegree_clauses(args.n, args.degree, codegree))
    typed = tuple(fixed_anchor_type_clauses(args.n, type_graph))
    base_count = 2 * math.comb(args.n, args.k)
    count = (
        base_count
        + len(degree_clauses)
        + len(cut_clauses)
        + len(fixed)
        + len(anchor)
        + len(typed)
    )
    clauses = itertools.chain(
        ramsey_clauses(args.n, args.k),
        degree_clauses,
        cut_clauses,
        fixed,
        anchor,
        typed,
    )
    write_dimacs(args.output, variable_count, clauses, count)
    print(
        f"wrote typed case d={args.degree}, c={codegree}, type={args.index}: "
        f"{variable_count} variables, {count} clauses to {args.output}"
    )


def _cmd_write_typed_inccnf(args: argparse.Namespace) -> None:
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    if manifest.get("host_order") != args.n:
        raise ValueError("manifest host order does not match n")
    if manifest.get("forbidden_clique") != args.k:
        raise ValueError("manifest forbidden clique does not match k")

    requested = set(args.branch_id or ())
    branches = []
    seen: set[str] = set()
    for branch in manifest.get("branches", ()):
        branch_id = branch.get("id")
        if not isinstance(branch_id, str) or branch_id in seen:
            raise ValueError("manifest branch identifiers must be unique strings")
        seen.add(branch_id)
        if branch.get("degree") == args.degree and (not requested or branch_id in requested):
            branches.append(branch)
    missing = requested - {branch["id"] for branch in branches}
    if missing:
        raise ValueError(f"requested branches are absent or have another degree: {sorted(missing)}")
    if not branches:
        raise ValueError(f"manifest contains no selected d={args.degree} branches")

    variable_count, degree_clauses = rooted_degree_bound_encoding(
        args.n, args.degree, args.max_colour_degree
    )
    fixed = tuple(fixed_neighborhood_clauses(args.n, args.degree))
    base_clauses = itertools.chain(ramsey_clauses(args.n, args.k), degree_clauses, fixed)
    cubes: list[tuple[int, ...]] = []
    for branch in branches:
        type_graph = decode_graph6(branch["graph6"])
        if len(type_graph) != branch.get("codegree"):
            raise ValueError(f"{branch['id']}: graph6 order does not match codegree")
        cube = typed_branch_cube(args.n, args.degree, type_graph)
        cubes.append(cube)

    write_inccnf(args.output, base_clauses, cubes)
    base_count = 2 * math.comb(args.n, args.k) + len(degree_clauses) + len(fixed)
    print(
        f"wrote incremental d={args.degree}: {variable_count} variables, "
        f"{base_count} common clauses, {len(cubes)} cubes to {args.output}"
    )


def _cmd_write_typed_manifest(args: argparse.Namespace) -> None:
    branches: list[dict[str, object]] = []
    total = 0
    for degree, first_codegree in ((18, 0), (20, 2)):
        maximum_codegree = {18: 9, 20: 10}[degree] if args.tight_codegrees else 13
        for codegree in range(first_codegree, maximum_codegree + 1):
            catalogue = args.directory / f"r35_{codegree}.g6"
            records = [line.strip() for line in catalogue.read_text(encoding="ascii").splitlines() if line.strip()]
            digest = hashlib.sha256(catalogue.read_bytes()).hexdigest()
            for index, record in enumerate(records):
                graph = decode_graph6(record)
                if len(graph) != codegree:
                    raise ValueError(f"{catalogue}: record {index} has wrong order")
                if count_cliques(graph, 3) or count_cliques(complement_graph(graph), 5):
                    raise ValueError(f"{catalogue}: record {index} is not R(3,5)")
                branch_id = f"d{degree}_c{codegree}_t{index}"
                unit_count = (args.n - 1) + max(0, degree - 1) + math.comb(codegree, 2)
                branches.append(
                    {
                        "id": branch_id,
                        "degree": degree,
                        "codegree": codegree,
                        "type_index": index,
                        "graph6": record,
                        "catalogue": catalogue.name,
                        "catalogue_sha256": digest,
                        "primary_unit_count": unit_count,
                    }
                )
                total += 1
    manifest = {
        "problem": "R(5,5)",
        "host_order": args.n,
        "forbidden_clique": args.k,
        "branches": branches,
        "branch_count": total,
        "catalogue_directory": str(args.directory),
        "tight_codegrees": args.tight_codegrees,
        "coverage_obligations": [
            "R(4,5)=25 implies every colour degree lies in 18..24.",
            "The handshaking parity lemma and colour complementation reduce a root degree to 18 or 20.",
            "A red root neighborhood of order d is an R(4,5,d) graph.",
            *(
                [
                    "Every R(4,5,18) root neighborhood has at most 85 red edges.",
                    "Every R(4,5,20) root neighborhood has at most 100 red edges.",
                    "Choosing a minimum internal-degree root neighbor gives codegree at most 9 or 10.",
                ]
                if args.tight_codegrees
                else []
            ),
            "R(4,4)=18 gives codegree at least d-18 for the anchored red edge.",
            (
                "Its common red neighborhood is an R(3,5,c) graph."
                if args.tight_codegrees
                else "Its common red neighborhood is R(3,5,c), and R(3,5)=14 gives c at most 13."
            ),
            "Each r35_c catalogue is exhaustive up to isomorphism and its recorded SHA-256 is trusted or certified.",
            "Vertex relabelling embeds the common neighborhood as the selected labelled catalogue type.",
        ],
    }
    args.output.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {total} validated branches to {args.output}")


def _cmd_verify_model(args: argparse.Namespace) -> None:
    bits = parse_dimacs_model(args.model.read_text(encoding="ascii"), edge_count(args.n))
    graph = graph_from_edge_bits(args.n, bits)
    red, blue, red_examples, blue_examples = monochromatic_subsets(graph, args.k, keep=3)
    print(f"n={args.n} k={args.k} red_K{args.k}={red} blue_K{args.k}={blue}")
    if red_examples:
        print(f"red examples: {red_examples}")
    if blue_examples:
        print(f"blue examples: {blue_examples}")
    if red or blue:
        raise SystemExit(1)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(required=True)

    stats = commands.add_parser("stats", help="print exact canonical-CNF dimensions")
    stats.add_argument("n", type=int)
    stats.add_argument("k", type=int)
    stats.set_defaults(func=_cmd_stats)

    verify_g6 = commands.add_parser("verify-g6", help="verify one graph6 Ramsey witness")
    verify_g6.add_argument("record")
    verify_g6.add_argument("--k", type=int, default=5)
    verify_g6.set_defaults(func=_cmd_verify_g6)

    audit_g6 = commands.add_parser("audit-g6", help="verify every graph6 record and its edge statistics")
    audit_g6.add_argument("input", type=Path)
    audit_g6.add_argument("--k", type=int, default=5)
    audit_g6.add_argument("--edge-threshold", type=int)
    audit_g6.set_defaults(func=_cmd_audit_g6)

    write_cnf = commands.add_parser("write-cnf", help="write the canonical CNF")
    write_cnf.add_argument("n", type=int)
    write_cnf.add_argument("k", type=int)
    write_cnf.add_argument("output", type=Path)
    write_cnf.set_defaults(func=_cmd_write_cnf)

    write_case_cnf = commands.add_parser(
        "write-case-cnf", help="write a case with N(0) fixed to the first d vertices"
    )
    write_case_cnf.add_argument("n", type=int)
    write_case_cnf.add_argument("k", type=int)
    write_case_cnf.add_argument("degree", type=int)
    write_case_cnf.add_argument("output", type=Path)
    write_case_cnf.set_defaults(func=_cmd_write_case_cnf)

    structured = commands.add_parser(
        "write-structured-case-cnf",
        help="fix N(0) and add sequential degree bounds for every vertex",
    )
    structured.add_argument("n", type=int)
    structured.add_argument("k", type=int)
    structured.add_argument("degree", type=int)
    structured.add_argument("output", type=Path)
    structured.add_argument("--max-colour-degree", type=int, default=24)
    structured.set_defaults(func=_cmd_write_structured_case_cnf)

    anchored = commands.add_parser(
        "write-anchored-case-cnf",
        help="also fix the red codegree and common-neighbor labels of edge (0,1)",
    )
    anchored.add_argument("n", type=int)
    anchored.add_argument("k", type=int)
    anchored.add_argument("degree", type=int)
    anchored.add_argument("codegree", type=int)
    anchored.add_argument("output", type=Path)
    anchored.add_argument("--max-colour-degree", type=int, default=24)
    anchored.set_defaults(func=_cmd_write_anchored_case_cnf)

    typed = commands.add_parser(
        "write-typed-case-cnf",
        help="fix one R(3,5,c) catalogue type in the common neighborhood of (0,1)",
    )
    typed.add_argument("n", type=int)
    typed.add_argument("k", type=int)
    typed.add_argument("degree", type=int)
    typed.add_argument("catalogue", type=Path)
    typed.add_argument("index", type=int, help="zero-based graph index")
    typed.add_argument("output", type=Path)
    typed.add_argument("--max-colour-degree", type=int, default=24)
    typed.add_argument("--degree-encoding", choices=("global", "rooted"), default="global")
    minimum = typed.add_mutually_exclusive_group()
    minimum.add_argument("--anchor-minimum-degree", action="store_true")
    minimum.add_argument("--anchor-minimum-degree-specialized", action="store_true")
    typed.add_argument("--d20-c10-regularity", action="store_true")
    typed.add_argument("--signature-lex", action="store_true")
    typed.add_argument("--w5-first-signature-symmetry", action="store_true")
    typed.add_argument("--edge-common-bound", type=int)
    typed.add_argument("--internal-cuts", action="store_true")
    typed.add_argument("--internal-star-cuts", action="store_true")
    typed.add_argument("--internal-edge-cuts", action="store_true")
    typed.add_argument("--internal-triangle-cuts", action="store_true")
    typed.set_defaults(func=_cmd_write_typed_case_cnf)

    incremental = commands.add_parser(
        "write-typed-inccnf",
        help="write one rooted common CNF followed by selected typed assumption cubes",
    )
    incremental.add_argument("n", type=int)
    incremental.add_argument("k", type=int)
    incremental.add_argument("degree", type=int)
    incremental.add_argument("manifest", type=Path)
    incremental.add_argument("output", type=Path)
    incremental.add_argument("--branch-id", action="append")
    incremental.add_argument("--max-colour-degree", type=int, default=24)
    incremental.set_defaults(func=_cmd_write_typed_inccnf)

    manifest = commands.add_parser(
        "write-typed-manifest", help="validate all R(3,5,c) catalogues and write branch metadata"
    )
    manifest.add_argument("n", type=int)
    manifest.add_argument("k", type=int)
    manifest.add_argument("directory", type=Path)
    manifest.add_argument("output", type=Path)
    manifest.add_argument("--tight-codegrees", action="store_true")
    manifest.set_defaults(func=_cmd_write_typed_manifest)

    verify_model = commands.add_parser("verify-model", help="verify a complete DIMACS SAT model")
    verify_model.add_argument("n", type=int)
    verify_model.add_argument("k", type=int)
    verify_model.add_argument("model", type=Path)
    verify_model.set_defaults(func=_cmd_verify_model)
    return parser


def main() -> None:
    args = build_parser().parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
