from __future__ import annotations

import hashlib
import json
import os
import tempfile
import unittest
from pathlib import Path

from . import exact_replay_cover6_d8 as replay


class ExactReplayCover6D8Tests(unittest.TestCase):
    def write_formula(
        self,
        directory: Path,
        clauses: tuple[replay.Clause, ...],
        *,
        declared_count: int | None = None,
    ) -> Path:
        path = directory / "fixture.cnf"
        with path.open("wb") as stream:
            count = len(clauses) if declared_count is None else declared_count
            stream.write(f"p cnf 66 {count}\n".encode("ascii"))
            for clause in clauses:
                stream.write(replay.clause_line(clause))
        return path

    def test_global_variable_numbering_and_branch_units(self) -> None:
        self.assertEqual([replay.global_edge(0, vertex) for vertex in range(1, 12)], list(range(1, 12)))
        self.assertEqual([replay.global_edge(1, vertex) for vertex in range(2, 12)], list(range(12, 22)))
        for p, q in replay.CASES:
            units = replay.exact_units(p, q)
            self.assertEqual({abs(literal) for literal in units}, set(range(1, 22)))
            self.assertEqual(sum(literal > 0 for literal in units[11:18]), p)
            self.assertEqual(sum(literal > 0 for literal in units[18:]), q)

    def test_clause_encoding_round_trip_uses_frozen_sort_order(self) -> None:
        clauses = ((1,), (-1,), (12, -21, 66), (), (-12, 21))
        for clause in clauses:
            self.assertEqual(replay.decode_clause(replay.encode_clause(clause)), tuple(sorted(clause, key=abs)))
        keys = sorted(map(replay.encode_clause, ((-2,), (1,), (-1,), (2,))))
        self.assertEqual([replay.decode_clause(key) for key in keys], [(1,), (2,), (-1,), (-2,)])

    def test_source_base_is_exactly_the_root_conditioned_ramsey_block(self) -> None:
        clauses = replay.base_clauses()
        self.assertEqual(len(clauses), 717)
        self.assertEqual(clauses[0], (-12, -13, -14, -22, -23, -31))
        self.assertEqual(clauses[1], (12, 13, 14, 22, 23, 31))
        self.assertTrue(all(abs(literal) > 11 for clause in clauses for literal in clause))

    def test_mutated_source_polarity_is_rejected_at_first_clause(self) -> None:
        expected = ((12, -22), (13, 23))
        mutated = ((-12, -22), (13, 23))
        with tempfile.TemporaryDirectory() as raw:
            path = self.write_formula(Path(raw), mutated)
            with self.assertRaisesRegex(replay.ExactReplayError, "DIMACS line 2"):
                replay.compare_formula(path, iter(expected), len(expected))

    def test_deleted_clause_is_rejected(self) -> None:
        expected = ((12,), (13,))
        with tempfile.TemporaryDirectory() as raw:
            path = self.write_formula(Path(raw), expected[:1], declared_count=2)
            with self.assertRaisesRegex(replay.ExactReplayError, "DIMACS line 3"):
                replay.compare_formula(path, iter(expected), len(expected))

    def test_mutated_second_center_unit_is_rejected(self) -> None:
        p, q = 2, 1
        expected = tuple((literal,) for literal in replay.exact_units(p, q))
        mutated = list(expected)
        mutated[11] = (-mutated[11][0],)
        with tempfile.TemporaryDirectory() as raw:
            path = self.write_formula(Path(raw), tuple(mutated))
            with self.assertRaisesRegex(replay.ExactReplayError, "DIMACS line 13"):
                replay.compare_formula(path, iter(expected), len(expected))

    def test_simplification_distinguishes_satisfied_and_false_literals(self) -> None:
        assignment = {12: True, 13: False}
        self.assertIsNone(replay.simplify_clause((-20, 12, 30), assignment))
        self.assertEqual(replay.simplify_clause((-12, 13, 30), assignment), (30,))
        self.assertEqual(replay.simplify_clause((22, -31), assignment), (22, -31))

    def test_small_injected_reduction_exercises_satisfaction_dedup_and_units(self) -> None:
        clauses = (
            (12, 22),
            (12, 22),
            (-12, 23),
            (-19, 24),
            (20, 25),
        )
        keys, metrics = replay.reduce_clauses(clauses, 0, 2)
        self.assertEqual(metrics, {
            "source_clauses": 5,
            "satisfied_clauses_removed": 2,
            "surviving_before_deduplication": 3,
            "exact_duplicates_removed": 1,
            "false_second_center_literals_removed": 3,
            "unique_residual_clauses": 2,
            "exact_unit_clauses_added": 21,
            "output_clauses": 23,
        })
        clauses_after = {replay.decode_clause(key) for key in keys}
        self.assertIn((22,), clauses_after)
        self.assertIn((24,), clauses_after)
        self.assertTrue({(literal,) for literal in replay.exact_units(0, 2)} <= clauses_after)

    @unittest.skipUnless(
        os.environ.get("RAMSEY_COVER6_SLOW") == "1",
        "set RAMSEY_COVER6_SLOW=1 for the exhaustive 2^21 local semantic replay",
    )
    def test_slow_exhaustive_local_cube_semantics(self) -> None:
        self.assertEqual(replay.validate_local_exactness(), {
            "checked_assignments": 1 << replay.LOCAL_EDGES,
            "r44_assignments": replay.R44_ASSIGNMENT_COUNT,
            "motif_assignments": replay.LABELLED_MASK_COUNT,
            "cube_rejected_r44_assignments": replay.LABELLED_MASK_COUNT,
            "exact": True,
        })

    def test_tracked_report_matches_frozen_formulas_and_arithmetic(self) -> None:
        path = Path(replay.__file__).with_name("COVER6_D8_SEMANTIC_REPLAY_V1.json")
        payload = path.read_bytes()
        report = json.loads(payload.decode("utf-8"))
        checkpoint = json.loads(
            path.with_name("COVER6_D8_CHECKPOINT13.json").read_text(encoding="utf-8")
        )
        replay_identity = checkpoint["finite_cnf_replay"]
        self.assertEqual(replay_identity["bytes"], len(payload))
        self.assertEqual(replay_identity["sha256"], hashlib.sha256(payload).hexdigest().upper())
        self.assertEqual(report["status"], "PASS_EXACT_FINITE_CNF_REPLAY")
        self.assertEqual(
            report["local_inputs"]["local_exactness"],
            {
                "checked_assignments": 1 << replay.LOCAL_EDGES,
                "r44_assignments": replay.R44_ASSIGNMENT_COUNT,
                "motif_assignments": replay.LABELLED_MASK_COUNT,
                "cube_rejected_r44_assignments": replay.LABELLED_MASK_COUNT,
                "exact": True,
            },
        )
        self.assertEqual(
            (report["source"]["clauses"], report["source"]["bytes"], report["source"]["sha256"]),
            (replay.SOURCE_CLAUSES, replay.SOURCE_BYTES, replay.SOURCE_SHA256),
        )
        rows = {(row["p"], row["q"]): row for row in report["residuals"]}
        self.assertEqual(len(report["residuals"]), len(replay.CASES))
        self.assertEqual(set(rows), set(replay.CASES))
        for case, (clauses, size, digest) in replay.RESIDUALS.items():
            row = rows[case]
            self.assertEqual((row["output_clauses"], row["bytes"], row["sha256"]), (clauses, size, digest))
            self.assertEqual(row["unique_residual_clauses"] + row["exact_unit_clauses_added"], clauses)
            self.assertEqual(
                row["surviving_before_deduplication"] - row["exact_duplicates_removed"],
                row["unique_residual_clauses"],
            )
            self.assertEqual(
                row["satisfied_clauses_removed"] + row["surviving_before_deduplication"],
                replay.SOURCE_CLAUSES,
            )


if __name__ == "__main__":
    unittest.main()
