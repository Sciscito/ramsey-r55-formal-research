from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from . import certify_cover6_cube_motif_bridge as bridge
from . import exact_replay_cover6_d8 as replay


class Cover6CubeMotifBridgeTests(unittest.TestCase):
    @classmethod
    def report(cls) -> dict[str, object]:
        path = Path(bridge.__file__).with_name(bridge.REPORT_NAME)
        return json.loads(path.read_text(encoding="utf-8"))

    def test_pair_order_is_the_shared_graph6_cube_order(self) -> None:
        expected = tuple(
            (left, right) for right in range(1, 7) for left in range(right)
        )
        self.assertEqual(bridge.PAIR_ORDER, expected)
        self.assertEqual(len(expected), 21)
        self.assertEqual(
            bridge.pair_order_sha256(),
            "4FB68D969B2D9E65D9C8348608F334BBC2A8294644BC00F5574831D3F2C9C0B8",
        )

    def test_blocker_polarity_detects_fixed_bit_mutations(self) -> None:
        result = bridge.polarity_report()
        self.assertTrue(result["blocker_false_iff_cube_matches"])
        self.assertEqual(
            result["representative_blocker_sha256"],
            "EAB0F2D63FA755C32B83915ABACFA5DDC8AB98C02F828F906271A5171EE82B5D",
        )

    def test_six_rows_force_one_r44_completion_each(self) -> None:
        rows, implied, digest = bridge.representative_certificate()
        self.assertEqual([row["motif_index"] for row in rows], [2, 3, 5, 4, 1, 0])
        self.assertEqual([row["r44_completions"] for row in rows], [1] * 6)
        self.assertEqual(len(implied), 25_200)
        self.assertEqual(len({mask for mask, _index in implied.values()}), 25_200)
        self.assertEqual(
            digest,
            "964A3C3A051590BF992966619FFE1AC78E13BF8B174AA87206274A1D390690E6",
        )

    def test_three_complement_witnesses_exist_but_six_rows_are_preferred(self) -> None:
        rows, _implied, _digest = bridge.representative_certificate()
        witnesses = bridge.complement_witnesses(rows)
        self.assertEqual(
            [(row["source_representative"], row["target_representative"]) for row in witnesses],
            [(0, 1), (2, 3), (4, 5)],
        )

    def test_tracked_report_has_compact_honest_scope(self) -> None:
        report = self.report()
        self.assertEqual(report["status"], "PASS_COMPACT_CUBE_MOTIF_BRIDGE")
        self.assertEqual(len(report["representatives"]), 6)
        self.assertFalse(
            report["minimal_lean_certificate"]["table_of_25200_cube_to_motif_rows_required"]
        )
        self.assertEqual(
            report["root_containing_conditioning"]["selected_projected_cubes"],
            [0, 300, 360, 540, 360, 300, 0],
        )
        self.assertEqual(
            report["root_containing_conditioning"][
                "total_stabilizer_orbit_representatives"
            ],
            38,
        )
        self.assertEqual(
            report["root_free_conditioning"]["total_stabilizer_orbit_representatives"],
            334,
        )
        self.assertIn("no SAT, LRAT", report["scope"])

    def test_projected_mask_round_trip_preserves_nonroot_pair_order(self) -> None:
        for neighbour_count in range(7):
            for projected in (0, 1, 0x1234, (1 << 15) - 1):
                full = bridge.full_mask_from_projected(projected, neighbour_count)
                self.assertEqual(replay.project_nonroot(full), projected)
                for vertex in range(1, 7):
                    self.assertEqual(
                        bool((full >> replay.local_edge(0, vertex)) & 1),
                        vertex <= neighbour_count,
                    )

    @unittest.skipUnless(
        os.environ.get("RAMSEY_COVER6_BRIDGE_FULL") == "1",
        "set RAMSEY_COVER6_BRIDGE_FULL=1 for all conditioning checks",
    )
    def test_full_tracked_bridge_report(self) -> None:
        generated = bridge.build_report()
        tracked = self.report()
        self.assertEqual(generated, tracked)


if __name__ == "__main__":
    unittest.main()
