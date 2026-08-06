#!/usr/bin/env python3
"""Integrity checks for the generated rooted ``gen4416`` LRAT artifacts."""

from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "gen4416_rooted_classification"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


class Gen4416RootedProofArtifactTests(unittest.TestCase):
    def test_proof_metadata_matches_files_and_unsat_log(self) -> None:
        cnf = OUTPUT / "guarded_counterexample.cnf"
        proof = OUTPUT / "guarded_counterexample.lrat"
        log = OUTPUT / "solver.log"
        metadata_path = OUTPUT / "proof_metadata.json"
        for path in (cnf, proof, log, metadata_path):
            self.assertTrue(path.is_file(), path)

        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        self.assertEqual(metadata["returncode"], 20)
        self.assertEqual(
            metadata["status"], "UNSAT_WITH_CADICAL_INTERNAL_LRAT_CHECK"
        )
        self.assertEqual(metadata["solver"], "cadical.exe")
        self.assertEqual(
            metadata["lean_replay"]["module"],
            "LRATCatcher.Tests.R44RootedGen4416Classifier",
        )
        self.assertEqual(
            metadata["lean_replay"]["theorem"],
            "LRATCatcher.Tests.r44_rooted_gen4416_classifier_unsat",
        )
        self.assertNotIn("C:\\\\Users", metadata_path.read_text(encoding="utf-8"))
        self.assertEqual(metadata["cnf_sha256"], sha256(cnf))
        self.assertEqual(metadata["lrat_bytes"], proof.stat().st_size)
        self.assertEqual(metadata["lrat_sha256"], sha256(proof))
        self.assertEqual(metadata["log_sha256"], sha256(log))
        self.assertIn("--lrat", metadata["command"])
        self.assertIn("--no-binary", metadata["command"])
        self.assertIn("--checkproof=2", metadata["command"])

        log_text = log.read_text(encoding="utf-8", errors="replace")
        self.assertIn("s UNSATISFIABLE", log_text)
        self.assertIn("c exit 20", log_text)
        self.assertTrue(proof.read_bytes().rstrip().endswith(b"43612 0 43601 43594 42850 43596 805 0"))


if __name__ == "__main__":
    unittest.main()
