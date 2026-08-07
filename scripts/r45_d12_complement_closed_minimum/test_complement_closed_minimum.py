from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import derive_lower_kernel as derive
from . import search_complement_closed_minimum as search
from . import verify_cover6 as upper
from . import verify_minimum as minimum


class ComplementClosedMinimumTests(unittest.TestCase):
    def test_frozen_small_artifact_hashes(self) -> None:
        self.assertEqual(minimum.sha256(minimum.COVER_PATH), minimum.EXPECTED_COVER_SHA256)
        self.assertEqual(minimum.sha256(minimum.KERNEL_PATH), minimum.EXPECTED_KERNEL_SHA256)
        self.assertEqual(len(minimum.records(minimum.KERNEL_PATH)), 30)

    def test_cover_closure_and_exact_complement_pairs(self) -> None:
        orbits, owner = upper.build_closure()
        self.assertEqual(tuple(map(len, orbits)), upper.EXPECTED_ORBIT_SIZES)
        self.assertEqual(len(owner), upper.EXPECTED_CLOSURE_SIZE)
        self.assertEqual(upper.digest_masks(owner), upper.EXPECTED_CLOSURE_SHA256)

    def test_three_explicit_pair_removal_witnesses(self) -> None:
        _orbits, owner = upper.build_closure()
        for local_pair, (_external, _index, record, _holes) in enumerate(
            upper.REMOVAL_WITNESSES
        ):
            self.assertEqual(upper.selected_pair_signature(record, owner), (local_pair,))

    def test_two_element_hitting_set_logic(self) -> None:
        clauses = (0b001, 0b010, 0b100)
        self.assertIsNone(minimum.hitting_set_at_most_two(clauses, 3))
        self.assertIsNone(derive.hitting_set_at_most_two(clauses, 3))
        self.assertEqual(minimum.hitting_set_at_most_two((0b001, 0b010), 3), (0, 1))
        self.assertIsNone(minimum.hitting_set_at_most_two((0,), 3))
        self.assertIsNone(derive.hitting_set_at_most_two((0,), 3))
        self.assertEqual(minimum.hitting_set_at_most_two((), 3), ())

    def test_exact_cover_search_synthetic(self) -> None:
        covers = (0b011, 0b101, 0b110)
        self.assertIsNone(search.exact_cover_search(covers, 3, 1)["cover"])
        found = search.exact_cover_search(covers, 3, 2)["cover"]
        self.assertIsNotNone(found)
        self.assertEqual(len(found), 2)

    def test_graph6_padding_corruption_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "padding"):
            minimum.decode_graph6("F@h^h", 7)

    def test_non_ramsey_kernel_graph_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, r"not R\(4,4,12\)"):
            minimum.kernel_signature("K~~~~~~~~~~~", {}, [0] * 362)

    @unittest.skipUnless(os.environ.get("R45_R44_SOURCE_DIR"), "external source unset")
    def test_external_independent_minimum_replay(self) -> None:
        source = Path(os.environ["R45_R44_SOURCE_DIR"]) / "r44_7.g6"
        report = minimum.verify(source)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["claim"]["minimum_motif_classes"], 6)

    @unittest.skipUnless(
        os.environ.get("R45_RUN_SLOW_COVER6") and os.environ.get("R45_R44_SOURCE_DIR"),
        "167-second direct replay not requested",
    )
    def test_external_direct_upper_replay(self) -> None:
        source = Path(os.environ["R45_R44_SOURCE_DIR"]) / "r44_12.g6"
        report = upper.verify(source)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["direct_replay"]["uncovered"], 0)


if __name__ == "__main__":
    unittest.main()
