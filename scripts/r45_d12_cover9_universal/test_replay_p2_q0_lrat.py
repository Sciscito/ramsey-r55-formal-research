from __future__ import annotations

import json
import unittest
from pathlib import Path

from . import replay_p2_q0_lrat as replay


class ReplayP2Q0Tests(unittest.TestCase):
    def test_frozen_identity_and_theorem(self) -> None:
        self.assertEqual(replay.EXPECTED_CNF_BYTES, 44_764_698)
        self.assertEqual(replay.EXPECTED_LRAT_BYTES, 10_683_195)
        self.assertEqual(
            replay.QUALIFIED_THEOREM,
            "LRATCatcher.Tests.R45D12Cover9UniversalP2Q0Replay."
            "cover9_d8_two_center_p2_q0_unsat",
        )

    def test_generated_source_uses_portable_lean_path_spelling(self) -> None:
        source = replay.lean_source(
            Path(r"S:\proof\case.cnf"), Path(r"S:\proof\case.lrat")
        ).decode("utf-8")
        self.assertIn('"S:/proof/case.cnf"', source)
        self.assertIn('"S:/proof/case.lrat"', source)
        self.assertIn("lrat_reflect_trim cover9_d8_two_center_p2_q0_unsat", source)

    def test_certificate_manifest_matches_frozen_inputs(self) -> None:
        manifest = json.loads(
            (replay.HERE / "P2_Q0_CERTIFICATE.json").read_text(encoding="utf-8")
        )
        self.assertEqual(manifest["status"], "EXACT_CNF_UNSAT_CERTIFIED_BY_LEAN_LRAT")
        self.assertEqual(manifest["formula"]["sha256"], replay.EXPECTED_CNF_SHA256)
        self.assertEqual(manifest["lrat"]["sha256"], replay.EXPECTED_LRAT_SHA256)
        self.assertEqual(manifest["lean_replay"]["theorem"], replay.QUALIFIED_THEOREM)


if __name__ == "__main__":
    unittest.main()
