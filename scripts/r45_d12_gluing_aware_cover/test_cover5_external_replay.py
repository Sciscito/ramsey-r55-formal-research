from __future__ import annotations

import os
import unittest
from pathlib import Path

from . import cover_audit
from . import verify_mixed_witness


HERE = Path(__file__).resolve().parent
COVER = HERE / "cover5_order7.tsv"
EXPECTED_ENTRIES = 1_449_166
EXPECTED_COVER_SHA256 = "CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288"
EXPECTED_INCIDENCE_SHA256 = "B14A1693C28CFED8965149ADB8C4410B993F86688466BC18736089E7D6735523"
EXPECTED_WITNESS_SHA256 = "36EC5E95D8599F6AE8099A6D3376D0E3F43269059FC644A1A3F96C52846414CB"
EXPECTED_SOURCES = {
    "r44_7.g6": ("6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010", 362),
    "r44_8.g6": ("B27389F7B1C70F823161A2CCA629BED3F4FBF058A43907637C0F9CE2E0CC4AB3", 2_079),
    "r44_12.g6": ("C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A", EXPECTED_ENTRIES),
}
EXPECTED_RECORDS = (
    (7, "F@h^g"),
    (7, "FCUrO"),
    (7, "FDLmW"),
    (7, "FG`Xo"),
    (7, "FdW}w"),
)


class CoverFiveExternalReplayTests(unittest.TestCase):
    def test_frozen_cover_and_induced_witness(self) -> None:
        names = (
            "R45_R44_SOURCE_DIR",
            "R45_R44_ORDER7_INCIDENCE",
            "R45_R44_COVER5_WITNESS",
        )
        configured = {name: os.environ.get(name) for name in names}
        missing = tuple(name for name, value in configured.items() if not value)
        if missing:
            self.skipTest("external cover5 replay environment is unset: " + ", ".join(missing))

        source = Path(configured["R45_R44_SOURCE_DIR"] or "")
        incidence = Path(configured["R45_R44_ORDER7_INCIDENCE"] or "")
        witness = Path(configured["R45_R44_COVER5_WITNESS"] or "")

        audit = cover_audit.verify(source, incidence, COVER)
        self.assertEqual(audit["status"], "PASS")
        self.assertEqual(audit["incidence"]["catalogue_records"], EXPECTED_ENTRIES)
        self.assertEqual(audit["incidence"]["uncovered"], 0)
        self.assertEqual(audit["incidence"]["sha256"], EXPECTED_INCIDENCE_SHA256)
        self.assertEqual(audit["incidence"]["candidate_pool"], 362)
        self.assertEqual(audit["incidence"]["candidate_order7"], 362)
        self.assertEqual(audit["incidence"]["candidate_order8"], 0)
        self.assertEqual(audit["cover"]["sha256"], EXPECTED_COVER_SHA256)
        self.assertEqual(audit["cover"]["size"], 5)
        self.assertEqual(audit["cover"]["order7"], 5)
        self.assertEqual(audit["cover"]["order8"], 0)
        self.assertTrue(audit["cover"]["irredundant"])
        self.assertEqual(
            tuple((row["order"], row["graph6"]) for row in audit["cover"]["records"]),
            EXPECTED_RECORDS,
        )
        self.assertEqual(
            tuple(row["holes_if_removed"] for row in audit["cover"]["records"]),
            (30, 18, 46, 159, 90),
        )
        for name, (digest, records) in EXPECTED_SOURCES.items():
            self.assertEqual(audit["sources"][name]["sha256"], digest)
            self.assertEqual(audit["sources"][name]["records"], records)

        replay = verify_mixed_witness.verify(source, witness, COVER)
        self.assertEqual(replay["status"], "PASS")
        self.assertEqual(replay["cover"]["sha256"], EXPECTED_COVER_SHA256)
        self.assertEqual(replay["cover"]["records"], EXPECTED_RECORDS)
        self.assertEqual(replay["witness"]["sha256"], EXPECTED_WITNESS_SHA256)
        self.assertEqual(replay["witness"]["entries"], EXPECTED_ENTRIES)
        self.assertEqual(sum(replay["witness"]["candidate_distribution"]), EXPECTED_ENTRIES)
        self.assertEqual(replay["sources"], audit["sources"])


if __name__ == "__main__":
    unittest.main()
