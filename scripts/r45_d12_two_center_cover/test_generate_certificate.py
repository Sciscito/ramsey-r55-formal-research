#!/usr/bin/env python3
"""Light deterministic tests for the two-centre cover certificate."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "generate_certificate.py"
SPEC = importlib.util.spec_from_file_location("r45_d12_two_center_certificate", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {MODULE_PATH}")
certificate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(certificate)


def pattern(assignments: dict[tuple[int, int], int]):
    edges = [0] * certificate.EDGE_COUNT
    for pair, colour in assignments.items():
        edges[certificate.PAIR_INDEX[tuple(sorted(pair))]] = colour
    return certificate.pattern_from_edges(edges)


class TwoCenterCertificateTests(unittest.TestCase):
    def test_ssd_output_guard_requires_absolute_s_path(self):
        certificate.require_ssd_path(Path(r"S:\proofs\certificate.json"))
        for rejected in (
            Path(r"S:relative.json"),
            Path(r"C:\proofs\certificate.json"),
            Path("relative.json"),
        ):
            with self.subTest(path=str(rejected)):
                with self.assertRaises(ValueError):
                    certificate.require_ssd_path(rejected)

    def test_permutation_convention_and_round_trip(self):
        source = pattern({(0, 1): 2, (1, 2): 1, (3, 7): 2, (5, 11): 1})
        new_to_old = [1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 11, 10]
        transformed = certificate.permute_pattern(source, new_to_old)
        self.assertEqual(certificate.ternary_digit(transformed, 0), 2)
        transformed_02 = certificate.PAIR_INDEX[(0, 2)]
        source_13 = certificate.PAIR_INDEX[(1, 3)]
        self.assertEqual(
            certificate.ternary_digit(transformed, transformed_02),
            certificate.ternary_digit(source, source_13),
        )
        inverse = [0] * certificate.ORDER
        for new, old in enumerate(new_to_old):
            inverse[old] = new
        self.assertEqual(certificate.permute_pattern(transformed, inverse), source)

    def test_profile_matching_respects_holes(self):
        weak = ((0, 1), (2, 0), (1, 2))
        strong = ((2, 1), (2, 2), (1, 2))
        matching = certificate.profile_matching(weak, strong)
        self.assertIsNotNone(matching)
        assert matching is not None
        self.assertEqual(sorted(matching), [0, 1, 2])
        self.assertTrue(
            all(
                certificate.profile_subsumes(weak[index], strong[target])
                for index, target in enumerate(matching)
            )
        )

    def test_synthetic_orientation_is_direct_and_uses_a_permutation(self):
        weak_profiles = (
            (0, 0),
            (0, 1),
            (0, 2),
            (1, 0),
            (1, 1),
            (1, 2),
            (2, 0),
            (2, 1),
            (2, 2),
            (0, 0),
        )
        weak = (2, weak_profiles)
        assignments = {(0, 1): 2}
        for outside, profile in zip(range(2, 12), weak_profiles, strict=True):
            if profile[0]:
                assignments[(0, outside)] = profile[0]
            if profile[1]:
                assignments[(1, outside)] = profile[1]
        oriented_source = pattern(assignments)
        scramble = [1, 0, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10]
        scrambled = certificate.permute_pattern(oriented_source, scramble)
        result = certificate.orientation_to_weak(scrambled, weak)
        self.assertIsNotNone(result)
        assert result is not None
        oriented, new_to_old = result
        self.assertEqual(sorted(new_to_old), list(range(12)))
        self.assertTrue(certificate.directly_extends_weak(oriented, weak))

    def test_consensus_is_extended_by_every_member(self):
        first = pattern({(0, 1): 2, (0, 2): 1, (2, 3): 2})
        second = pattern({(0, 1): 2, (0, 2): 1, (2, 3): 1, (4, 5): 2})
        fused = certificate.consensus([first, second])
        expected = pattern({(0, 1): 2, (0, 2): 1})
        self.assertEqual(fused, expected)
        self.assertTrue(certificate.extends_pattern(first, fused))
        self.assertTrue(certificate.extends_pattern(second, fused))

    def test_raw_hol_dimacs_polarity_and_blue_block_range(self):
        source = pattern({(0, 1): 1, (10, 11): 2})
        units = certificate.raw_hol_dimacs_units(source)
        self.assertEqual(units, (-211, 276))
        self.assertTrue(all(211 <= abs(literal) <= 276 for literal in units))

    def test_antichain_drops_a_stronger_isomorphism_class(self):
        holes = ((0, 0),) * 10
        weak = (0, holes)
        strong = (2, ((2, 2),) + holes[1:])
        self.assertTrue(certificate.two_center_subsumes(weak, strong))
        self.assertEqual(certificate.minimal_two_center_antichain({weak, strong}), [weak])


if __name__ == "__main__":
    unittest.main()
