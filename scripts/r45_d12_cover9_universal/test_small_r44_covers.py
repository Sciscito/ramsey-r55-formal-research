from __future__ import annotations

import json
import unittest
from pathlib import Path
from unittest import mock

from scripts.r45_d12_complement_closed_minimum import verify_cover6
from . import augment_small_r44_covers as augment
from . import independent_replay_small_r44_covers as replay
from . import scan_small_r44_covers as scan


class SmallR44CoverTests(unittest.TestCase):
    def test_generic_subset_counts_and_greedy_tie_break(self) -> None:
        self.assertEqual(len(scan.subset_positions(10)), 120)
        self.assertEqual(len(scan.subset_positions(11)), 330)
        holes = (frozenset((1, 2)), frozenset((2, 3)), frozenset((3,)))
        result = augment.greedy_individual(holes, (1, 2, 3))
        self.assertEqual(result["selected_class_ids"], [2, 3])
        self.assertEqual(result["new_holes_covered"], [2, 1])

    def test_independent_graph6_representation_agrees_on_manifest_motifs(self) -> None:
        data = json.loads(replay.DEFAULT_MANIFEST.read_text(encoding="utf-8"))
        records = set(data["q_at_least_12"]["individual_records"])
        records.update(data["q_at_least_12"]["complement_closed_records"])
        for order in (10, 11):
            records.update(data[f"q{order}"]["individual_records"])
            records.update(data[f"q{order}"]["complement_closed_records"])
        for record in records:
            expected = verify_cover6.decode_graph6(record, 7)
            observed = replay.local_mask(
                replay.decode_graph6_rows(record, 7), tuple(range(7))
            )
            self.assertEqual(observed, expected, record)

    def test_manifest_identities_and_architecture_without_external_catalogues(self) -> None:
        fake_result = {
            "order": 0,
            "graphs": 0,
            "all_sources_r44": True,
            "uncovered": 0,
        }
        with mock.patch.object(replay, "verify_catalogue", return_value=fake_result):
            report = replay.verify(
                replay.DEFAULT_MANIFEST,
                replay.DEFAULT_MANIFEST_SHA,
                Path("unused-r44-10.g6.gz"),
                Path("unused-r44-11.g6.gz"),
            )
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(
            report["k45_obligation_arithmetic"],
            {"individual": 112, "complement_closed": 126},
        )


if __name__ == "__main__":
    unittest.main()
