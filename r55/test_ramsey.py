import itertools
import tempfile
import unittest
from pathlib import Path

from ramsey import (
    CnfBuilder,
    anchored_minimum_internal_degree_encoding,
    anchored_typed_internal_regular_encoding,
    anchored_typed_minimum_internal_degree_encoding,
    complement_graph,
    count_cliques,
    decode_graph6,
    degree_bound_encoding,
    edge_count,
    edge_var,
    fixed_neighborhood_clauses,
    fixed_anchor_codegree_clauses,
    fixed_anchor_type_clauses,
    graph_from_edge_bits,
    has_edge,
    is_ramsey_free,
    monochromatic_subsets,
    ramsey_clauses,
    rooted_degree_bound_encoding,
    rooted_edge_common_bound_encoding,
    rooted_internal_cuts_encoding,
    rooted_signature_lex_encoding,
    typed_branch_cube,
    write_inccnf,
    w5_dihedral_permutations,
    w5_first_signature_symmetry_encoding,
)


# One of McKay's published 42-vertex (5,5)-Ramsey graphs.
MCKAY_42 = r"i?Udjp^j}?W@`bIRhHgk\SY~ECeQS\CniuKP]RQLdsX~F?b|L?h_SvygSNziSVdZ`P|CxamFHKax[PhPyVEYxAqkY\_xCfYxNscNtb]k_uFsLruaJwr`nPMMc]\qGhwyhfLjTELQ}T]h@qtuW"


def cycle_graph(n: int):
    adjacency = [0] * n
    for i in range(n):
        j = (i + 1) % n
        adjacency[i] |= 1 << j
        adjacency[j] |= 1 << i
    return tuple(adjacency)


class RamseyTests(unittest.TestCase):
    def test_edge_numbering_is_bijection(self):
        for n in range(2, 12):
            variables = [edge_var(n, i, j) for i, j in itertools.combinations(range(n), 2)]
            self.assertEqual(variables, list(range(1, edge_count(n) + 1)))

    def test_fixed_neighborhood_case(self):
        self.assertEqual(
            list(fixed_neighborhood_clauses(6, 2)),
            [(1,), (2,), (-3,), (-4,), (-5,)],
        )

    def test_fixed_anchor_codegree_case(self):
        self.assertEqual(
            list(fixed_anchor_codegree_clauses(8, 5, 2)),
            [(8,), (9,), (-10,), (-11,)],
        )

    def test_fixed_anchor_type_embedding(self):
        c5 = cycle_graph(5)
        clauses = list(fixed_anchor_type_clauses(8, c5))
        self.assertEqual(len(clauses), 10)
        # Global edge (2,3) is the first red cycle edge.
        self.assertIn((edge_var(8, 2, 3),), clauses)
        # Global edge (2,4) is not a cycle edge.
        self.assertIn((-edge_var(8, 2, 4),), clauses)

    def test_typed_branch_cube_matches_standalone_units(self):
        c5 = cycle_graph(5)
        expected = tuple(
            clause[0]
            for clause in itertools.chain(
                fixed_anchor_codegree_clauses(9, 6, 5),
                fixed_anchor_type_clauses(9, c5),
            )
        )
        self.assertEqual(typed_branch_cube(9, 6, c5), expected)

    def test_inccnf_writer(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "tiny.inccnf"
            write_inccnf(output, [(1, -2), ()], [(-1,), (1, 2)])
            self.assertEqual(
                output.read_text(encoding="ascii"),
                "p inccnf\n1 -2 0\n0\na -1 0\na 1 2 0\n",
            )

    def test_sequential_at_most_encoding_exhaustively(self):
        # Three primary variables and a <=1 counter.  Exhaust both primary
        # and auxiliary assignments to check exact equisatisfiability.
        builder = CnfBuilder(4)
        builder.add_at_most((1, 2, 3), 1)
        variable_count = builder.next_variable - 1

        def satisfies(packed):
            def value(literal):
                bit = ((packed >> (abs(literal) - 1)) & 1) == 1
                return bit if literal > 0 else not bit
            return all(any(value(literal) for literal in clause) for clause in builder.clauses)

        for primary in range(8):
            has_extension = False
            for auxiliary in range(1 << (variable_count - 3)):
                packed = primary | (auxiliary << 3)
                has_extension |= satisfies(packed)
            self.assertEqual(has_extension, primary.bit_count() <= 1)

    def test_lex_encoding_exhaustively(self):
        for width in range(1, 5):
            builder = CnfBuilder(2 * width + 1)
            left_literals = tuple(range(1, width + 1))
            right_literals = tuple(range(width + 1, 2 * width + 1))
            builder.add_lex_leq(left_literals, right_literals)
            auxiliary_count = builder.next_variable - (2 * width + 1)
            self.assertEqual(auxiliary_count, width - 1)
            self.assertEqual(len(builder.clauses), 3 * width - 2)

            def satisfies(packed):
                return all(
                    any(
                        bool((packed >> (abs(literal) - 1)) & 1) == (literal > 0)
                        for literal in clause
                    )
                    for clause in builder.clauses
                )

            for primary in range(1 << (2 * width)):
                has_extension = any(
                    satisfies(primary | (auxiliary << (2 * width)))
                    for auxiliary in range(1 << auxiliary_count)
                )
                left = tuple(bool((primary >> index) & 1) for index in range(width))
                right = tuple(
                    bool((primary >> (width + index)) & 1) for index in range(width)
                )
                self.assertEqual(has_extension, left <= right)

    def test_lex_encoding_with_overlapping_permuted_vectors(self):
        for width in range(1, 5):
            left_literals = tuple(range(1, width + 1))
            for permutation in itertools.permutations(range(width)):
                right_literals = tuple(
                    left_literals[index] for index in permutation
                )
                builder = CnfBuilder(width + 1)
                builder.add_lex_leq(left_literals, right_literals)
                auxiliary_count = builder.next_variable - (width + 1)

                for clause in builder.clauses:
                    self.assertEqual(len(clause), len(set(clause)))
                    self.assertFalse(
                        any(-literal in clause for literal in clause)
                    )

                def satisfies(packed):
                    return all(
                        any(
                            bool((packed >> (abs(literal) - 1)) & 1)
                            == (literal > 0)
                            for literal in clause
                        )
                        for clause in builder.clauses
                    )

                for primary in range(1 << width):
                    has_extension = any(
                        satisfies(primary | (auxiliary << width))
                        for auxiliary in range(1 << auxiliary_count)
                    )
                    left = tuple(
                        bool((primary >> index) & 1)
                        for index in range(width)
                    )
                    right = tuple(left[index] for index in permutation)
                    self.assertEqual(has_extension, left <= right)

    def test_guarded_at_most_encoding(self):
        builder = CnfBuilder(4)
        builder.add_at_most((1, 2), 0, guard=3)
        for packed in range(8):
            values = [bool((packed >> i) & 1) for i in range(3)]
            sat = all(
                any(values[abs(lit) - 1] == (lit > 0) for lit in clause)
                for clause in builder.clauses
            )
            self.assertEqual(sat, values[2] or not (values[0] or values[1]))

    def test_multi_guarded_at_most_encoding(self):
        builder = CnfBuilder(5)
        builder.add_at_most((1, 2), 0, guard=(3, 4))
        for packed in range(16):
            values = [bool((packed >> i) & 1) for i in range(4)]
            sat = all(
                any(values[abs(lit) - 1] == (lit > 0) for lit in clause)
                for clause in builder.clauses
            )
            expected = values[2] or values[3] or not (values[0] or values[1])
            self.assertEqual(sat, expected)

    def test_rooted_degree_encoding_is_smaller(self):
        global_variables, global_clauses = degree_bound_encoding(8, 5)
        rooted_variables, rooted_clauses = rooted_degree_bound_encoding(8, 3, 5)
        self.assertLess(rooted_variables, global_variables)
        self.assertLess(len(rooted_clauses), len(global_clauses))

    def test_anchor_minimum_degree_encoding_dimensions(self):
        first = edge_count(43) + 1
        variable_count, clauses = anchored_minimum_internal_degree_encoding(43, 18, 9, first)
        self.assertEqual(variable_count - edge_count(43), 1836)
        self.assertEqual(len(clauses), 3689)

        variable_count, clauses = anchored_minimum_internal_degree_encoding(43, 20, 10, first)
        self.assertEqual(variable_count - edge_count(43), 2565)
        self.assertEqual(len(clauses), 5149)

    def test_typed_anchor_minimum_degree_encoding_dimensions(self):
        first = edge_count(43) + 1
        type9 = decode_graph6("H?CdQjK")
        variable_count, clauses = anchored_typed_minimum_internal_degree_encoding(
            43, 18, type9, first
        )
        self.assertEqual(variable_count - edge_count(43), 898)
        self.assertEqual(len(clauses), 1836)

        type10 = decode_graph6("I?CcjQK[G")
        variable_count, clauses = anchored_typed_minimum_internal_degree_encoding(
            43, 20, type10, first
        )
        self.assertEqual(variable_count - edge_count(43), 1282)
        self.assertEqual(len(clauses), 2612)

    def test_typed_internal_regularity_encoding_dimensions(self):
        first = edge_count(43) + 1
        type10 = decode_graph6("I?CcjQK[G")
        variable_count, clauses = anchored_typed_internal_regular_encoding(
            43, 20, type10, 10, first
        )
        self.assertEqual(variable_count - edge_count(43), 2885)
        self.assertEqual(len(clauses), 5770)

    def test_rooted_common_bound_encoding_dimensions(self):
        variable_count, clauses = rooted_edge_common_bound_encoding(8, 3, 2, edge_count(8) + 1)
        self.assertGreater(variable_count, edge_count(8))
        self.assertTrue(clauses)

    def test_rooted_internal_cuts_dimensions(self):
        variable_count, clauses = rooted_internal_cuts_encoding(9, 4, edge_count(9) + 1)
        self.assertGreater(variable_count, edge_count(9))
        self.assertTrue(clauses)

    def test_rooted_signature_lex_dimensions(self):
        first = edge_count(43) + 1
        variable_count, clauses = rooted_signature_lex_encoding(43, 18, 9, first)
        self.assertEqual(variable_count - edge_count(43), 447)
        self.assertEqual(len(clauses), 1371)

        variable_count, clauses = rooted_signature_lex_encoding(43, 20, 10, first)
        self.assertEqual(variable_count - edge_count(43), 471)
        self.assertEqual(len(clauses), 1442)

    def test_w5_symmetry_encoding_and_automorphisms(self):
        graph = decode_graph6("Is`b?{]]?")
        permutations = w5_dihedral_permutations()
        self.assertEqual(len(set(permutations)), 10)
        for permutation in permutations:
            self.assertEqual(sorted(permutation), list(range(10)))
            for i, j in itertools.combinations(range(10), 2):
                self.assertEqual(
                    has_edge(graph, i, j),
                    has_edge(graph, permutation[i], permutation[j]),
                )

        first = edge_count(43) + 1
        variable_count, clauses = w5_first_signature_symmetry_encoding(
            43, 20, graph, first
        )
        self.assertEqual(variable_count - edge_count(43), 81)
        self.assertEqual(len(clauses), 247)
        for clause in clauses:
            self.assertEqual(len(clause), len(set(clause)))
            self.assertFalse(any(-literal in clause for literal in clause))

    def test_w5_signature_break_selects_one_value_per_full_orbit(self):
        pairs = ((0, 9), (1, 2), (5, 6), (7, 8), (3, 4))
        full_group = set()
        for dihedral in w5_dihedral_permutations():
            for swap_mask in range(1 << len(pairs)):
                twin_swap = list(range(10))
                for index, (left, right) in enumerate(pairs):
                    if (swap_mask >> index) & 1:
                        twin_swap[left], twin_swap[right] = right, left
                full_group.add(
                    tuple(twin_swap[dihedral[index]] for index in range(10))
                )
        self.assertEqual(len(full_group), 320)

        accepted = 0
        for packed in range(1 << 10):
            signature = tuple(bool((packed >> index) & 1) for index in range(10))
            pair_sorted = all(
                signature[left] <= signature[right] for left, right in pairs
            )
            dihedral_minimal = all(
                signature
                <= tuple(signature[permutation[index]] for index in range(10))
                for permutation in w5_dihedral_permutations()[1:]
            )
            is_full_orbit_minimum = signature == min(
                tuple(signature[permutation[index]] for index in range(10))
                for permutation in full_group
            )
            self.assertEqual(
                pair_sorted and dihedral_minimal,
                is_full_orbit_minimum,
            )
            accepted += is_full_orbit_minimum

        self.assertEqual(accepted, 39)

    def test_r33_cnf_has_exact_dimensions_and_is_unsat(self):
        clauses = list(ramsey_clauses(6, 3))
        self.assertEqual(edge_count(6), 15)
        self.assertEqual(len(clauses), 40)
        self.assertTrue(all(len(clause) == 3 for clause in clauses))

        # Exhaust all 2^15 assignments.  This is deliberately independent of
        # a SAT solver and proves the tiny pipeline benchmark is UNSAT.
        for packed in range(1 << edge_count(6)):
            bits = [(packed >> i) & 1 == 1 for i in range(edge_count(6))]
            self.assertFalse(all(any(bits[abs(lit) - 1] == (lit > 0) for lit in clause) for clause in clauses))

    def test_c5_is_lower_witness_for_r33(self):
        self.assertTrue(is_ramsey_free(cycle_graph(5), 3))

    def test_known_mckay_42_graph(self):
        graph = decode_graph6(MCKAY_42)
        self.assertEqual(len(graph), 42)
        red, blue, _, _ = monochromatic_subsets(graph, 5)
        self.assertEqual((red, blue), (0, 0))

    def test_complete_and_empty_k5_each_have_one_defect(self):
        complete = graph_from_edge_bits(5, [True] * edge_count(5))
        empty = graph_from_edge_bits(5, [False] * edge_count(5))
        self.assertEqual(monochromatic_subsets(complete, 5)[:2], (1, 0))
        self.assertEqual(monochromatic_subsets(empty, 5)[:2], (0, 1))

    def test_bitset_clique_counter_matches_exhaustive_counter(self):
        # Exhaust every labelled graph on five vertices.  This checks both
        # colours and the bitset recursion against the simpler subset scan.
        for packed in range(1 << edge_count(5)):
            graph = graph_from_edge_bits(
                5, [(packed >> i) & 1 == 1 for i in range(edge_count(5))]
            )
            red, blue, _, _ = monochromatic_subsets(graph, 3)
            self.assertEqual(count_cliques(graph, 3), red)
            self.assertEqual(count_cliques(complement_graph(graph), 3), blue)


if __name__ == "__main__":
    unittest.main()
