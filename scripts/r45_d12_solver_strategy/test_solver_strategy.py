from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import cross_pattern_orbits as orbits
import cross_interval_cover as intervals
import cube_benchmark as cubes
import strategy_probe as strategy


class StrategyStructureTests(unittest.TestCase):
    def test_r34_catalogue_counts_and_rooted_cover_size(self) -> None:
        counts = {order: len(strategy.r34_catalogue(order)) for order in range(3, 9)}
        self.assertEqual(counts, {3: 3, 4: 6, 5: 9, 6: 15, 7: 9, 8: 3})
        self.assertEqual(
            sum(counts[degree] * counts[11 - degree] for degree in range(3, 9)),
            396,
        )

    def test_lex_cross_exact_dimensions(self) -> None:
        builder = strategy.ramsey.CnfBuilder(strategy.EDGE_VARIABLE_COUNT + 1)
        strategy.add_lex_cross(builder)
        self.assertEqual(builder.next_variable - 1, 397)
        self.assertEqual(len(builder.clauses), 374)
        self.assertTrue(all(builder.clauses))

    def test_rooted_degree_three_units(self) -> None:
        units = strategy.rooted_b_units(3, 0, 0)
        self.assertEqual(len(units), 42)
        self.assertTrue(all(len(unit) == 1 for unit in units))
        self.assertEqual(len({abs(unit[0]) for unit in units}), len(units))


class CubeBenchmarkTests(unittest.TestCase):
    def test_parse_solver_statuses(self) -> None:
        output = (
            "s UNSATISFIABLE\n"
            "c conflicts:                 1234\n"
            "c total process time since initialization:        1.25    seconds\n"
        )
        self.assertEqual(cubes.parse_solver(output, 20), ("UNSAT", 1234, 1.25))
        self.assertEqual(cubes.parse_solver("c UNKNOWN\n", 0), ("UNKNOWN", None, None))

    def test_materialize_cube_updates_header_and_appends_units(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.cnf"
            target = Path(directory) / "cube.cnf"
            source.write_text("p cnf 3 2\n1 2 0\n-1 3 0\n", encoding="ascii")
            cubes.materialize_cube(source, target, 3, 2, (-2, 3))
            self.assertEqual(
                target.read_text(encoding="ascii").splitlines(),
                ["p cnf 3 4", "1 2 0", "-1 3 0", "-2 0", "3 0"],
            )


class OrbitTests(unittest.TestCase):
    def test_catalogue_type_ten_has_48_automorphisms(self) -> None:
        records = tuple(
            line.strip()
            for line in orbits.CATALOGUE_PATH.read_text(encoding="ascii").splitlines()
            if line.strip()
        )
        graph = orbits.ramsey.decode_graph6(records[10])
        automorphisms = orbits.all_automorphisms(graph)
        self.assertEqual(len(automorphisms), 48)
        self.assertEqual(len(set(automorphisms)), 48)

    def test_mask_action_preserves_weight(self) -> None:
        permutation = (1, 2, 0)
        transformed = orbits.permute_mask(0b101, permutation)
        self.assertEqual(transformed.bit_count(), 2)
        self.assertEqual(transformed, 0b011)


class IntervalCoverTests(unittest.TestCase):
    def test_type_zero_exact_cover_has_81_cubes(self) -> None:
        record = next(
            line.strip()
            for line in intervals.CATALOGUE_PATH.read_text(encoding="ascii").splitlines()
            if line.strip()
        )
        graph = intervals.ramsey.decode_graph6(record)
        blocks = intervals.independent_four_masks(graph)
        self.assertEqual(len(blocks), 23)
        cubes = intervals.optimal_disjoint_cover(blocks)
        self.assertEqual(len(cubes), 81)


if __name__ == "__main__":
    unittest.main()
