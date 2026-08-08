from __future__ import annotations

import json
import hashlib
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from . import reduce_master8_lrat_core as reducer


TINY_CNF = b"""p cnf 2 4
1 0
-1 2 0
-2 0
1 2 0
"""

TINY_LRAT = b"""5 2 0 1 2 0
5 d 1 4 0
6 0 5 3 0
"""


def check_tiny_rup(cnf: bytes, lrat: bytes) -> None:
    cnf_lines = cnf.splitlines()
    header = cnf_lines[0].split()
    clauses = {
        index: tuple(map(int, line.split()[:-1]))
        for index, line in enumerate(cnf_lines[1:], 1)
    }
    if len(clauses) != int(header[3]):
        raise AssertionError("bad tiny CNF header")

    def assign_literal(assignment: dict[int, bool], literal: int) -> bool:
        variable, value = abs(literal), literal > 0
        previous = assignment.get(variable)
        if previous is not None and previous != value:
            return False
        assignment[variable] = value
        return True

    empty_seen = False
    for line_number, raw in enumerate(lrat.splitlines(), 1):
        action = reducer.parse_lrat_line(raw, line_number)
        if isinstance(action, reducer.Deletion):
            for clause_id in action.clause_ids:
                clauses.pop(clause_id, None)
            continue
        if not isinstance(action, reducer.Addition):
            continue
        if action.rat_hints:
            raise AssertionError("tiny checker only accepts RUP")
        assignment: dict[int, bool] = {}
        contradiction = False
        for literal in action.clause:
            if not assign_literal(assignment, -literal):
                contradiction = True
                break
        if not contradiction:
            for hint in action.rup_hints:
                hinted = clauses[hint]
                unresolved: list[int] = []
                satisfied = False
                for literal in hinted:
                    value = assignment.get(abs(literal))
                    if value is None:
                        unresolved.append(literal)
                    elif value == (literal > 0):
                        satisfied = True
                        break
                if satisfied or len(unresolved) > 1:
                    raise AssertionError(f"hint {hint} is not unit or conflicting")
                if not unresolved:
                    contradiction = True
                    break
                if not assign_literal(assignment, unresolved[0]):
                    contradiction = True
                    break
        if not contradiction:
            raise AssertionError(f"addition {action.clause_id} is not RUP")
        clauses[action.clause_id] = action.clause
        if not action.clause:
            empty_seen = True
            break
    if not empty_seen:
        raise AssertionError("tiny proof did not derive the empty clause")


class Master8CoreReducerTests(unittest.TestCase):
    @classmethod
    def tracked_report(cls) -> dict[str, object]:
        path = Path(reducer.__file__).with_name("MASTER8_LRAT_CORE_ANALYSIS_V1.json")
        return json.loads(path.read_text(encoding="utf-8"))

    @classmethod
    def core_directory(cls) -> Path:
        return Path(reducer.__file__).with_name("master8_core")

    @classmethod
    def tracked_manifest(cls) -> dict[str, object]:
        return json.loads(
            (cls.core_directory() / "MANIFEST.json").read_text(encoding="utf-8")
        )

    def test_parser_distinguishes_rup_rat_and_deletion(self) -> None:
        rup = reducer.parse_lrat_line(b"5 2 0 1 2 0\n", 1)
        self.assertEqual(rup, reducer.Addition(5, (2,), (1, 2), ()))
        rat = reducer.parse_lrat_line(b"6 -2 3 0 1 -4 2 5 -3 1 0\n", 2)
        self.assertEqual(
            rat,
            reducer.Addition(6, (-2, 3), (1,), ((4, (2, 5)), (3, (1,)))),
        )
        deletion = reducer.parse_lrat_line(b"6 d 1 4 0\n", 3)
        self.assertEqual(deletion, reducer.Deletion((1, 4)))

    def test_tiny_reduction_remaps_core_and_preserves_deletion(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            output = root / "out"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(TINY_LRAT)
            check_tiny_rup(TINY_CNF, TINY_LRAT)
            report = reducer.reduce_pair(
                cnf,
                lrat,
                output,
                master_identity=False,
                require_repository_output=False,
            )
            reduced_cnf = (output / "cover6_closed_master_d8_bounded13_core.cnf").read_bytes()
            reduced_lrat = (output / "cover6_closed_master_d8_bounded13_core.lrat").read_bytes()
            mapping = (output / "core_clause_map.tsv").read_text(encoding="ascii")
            self.assertEqual(reduced_cnf, b"p cnf 2 3\n1 0\n-1 2 0\n-2 0\n")
            self.assertEqual(
                reduced_lrat,
                b"4 2 0 1 2 0\n1 d 1 0\n5 0 4 3 0\n",
            )
            self.assertEqual(
                [line.split("\t")[:2] for line in mapping.splitlines()[1:]],
                [["1", "1"], ["2", "2"], ["3", "3"]],
            )
            check_tiny_rup(reduced_cnf, reduced_lrat)
            verification = reducer.verify_reduced_pair(
                output / "cover6_closed_master_d8_bounded13_core.cnf",
                output / "cover6_closed_master_d8_bounded13_core.lrat",
            )
            self.assertEqual(
                verification["status"],
                "PASS_CLOSED_RUP_DEPENDENCY_CORE_REPLAY_STILL_REQUIRED",
            )
            mapping_verification = reducer.verify_clause_mapping(
                cnf,
                output / "cover6_closed_master_d8_bounded13_core.cnf",
                output / "core_clause_map.tsv",
            )
            self.assertEqual(
                mapping_verification["status"], "PASS_EXACT_ORDERED_SUBSEQUENCE"
            )
            self.assertEqual(report["core"]["initial_clauses"], 3)
            self.assertEqual(report["core"]["derived_additions"], 2)
            self.assertEqual(report["output"]["lrat"]["deletion_actions"], 1)
            self.assertEqual(report["output"]["initial_clause_mapping"]["rows"], 3)

    def test_forward_hint_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "bad.lrat"
            path.write_bytes(b"5 2 0 6 0\n6 0 5 3 0\n")
            with self.assertRaisesRegex(reducer.CoreReductionError, "non-backward"):
                reducer.index_proof(path, 4)

    def test_noncontiguous_addition_id_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "gap.lrat"
            path.write_bytes(b"5 2 0 1 2 0\n7 0 5 3 0\n")
            with self.assertRaisesRegex(reducer.CoreReductionError, "non-contiguous"):
                reducer.index_proof(path, 4)

    def test_two_empty_additions_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "two-empty.lrat"
            path.write_bytes(b"5 0 1 2 0\n6 0 3 4 0\n")
            with self.assertRaisesRegex(reducer.CoreReductionError, "exactly one empty"):
                reducer.index_proof(path, 4)

    def test_rat_input_is_reported_and_reduction_refused(self) -> None:
        rat_lrat = b"5 2 0 -1 2 0\n6 0 3 4 0\n"
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "rat.lrat"
            output = root / "out"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(rat_lrat)
            analysis = reducer.analyze(cnf, lrat, master_identity=False)
            self.assertEqual(analysis["status"], "RAT_REDUCTION_REFUSED")
            self.assertEqual(analysis["proof"]["rat_additions"], 1)
            with self.assertRaises(reducer.RatReductionUnsupported):
                reducer.reduce_pair(
                    cnf,
                    lrat,
                    output,
                    master_identity=False,
                    require_repository_output=False,
                )
            self.assertFalse(output.exists())

    def test_existing_output_directory_is_never_reused(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            output = root / "out"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(TINY_LRAT)
            output.mkdir()
            with self.assertRaises(FileExistsError):
                reducer.reduce_pair(
                    cnf,
                    lrat,
                    output,
                    master_identity=False,
                    require_repository_output=False,
                )

    def test_source_identity_change_before_publication_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            output = root / "out"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(TINY_LRAT)
            original_sha256_file = reducer.sha256_file
            calls = 0

            def changed_on_final_cnf_hash(path: Path) -> tuple[str, int]:
                nonlocal calls
                calls += 1
                digest, size = original_sha256_file(path)
                if calls == 3:
                    return "0" * 64, size
                return digest, size

            with mock.patch.object(
                reducer, "sha256_file", side_effect=changed_on_final_cnf_hash
            ):
                with self.assertRaisesRegex(
                    reducer.CoreReductionError, "source CNF changed"
                ):
                    reducer.reduce_pair(
                        cnf,
                        lrat,
                        output,
                        master_identity=False,
                        require_repository_output=False,
                    )
            self.assertFalse(output.exists())

    def test_mapping_hash_and_id_mutants_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            output = root / "out"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(TINY_LRAT)
            reducer.reduce_pair(
                cnf,
                lrat,
                output,
                master_identity=False,
                require_repository_output=False,
            )
            mapping = output / "core_clause_map.tsv"
            original = mapping.read_text(encoding="ascii")

            hash_mutant = root / "hash-mutant.tsv"
            rows = original.splitlines()
            fields = rows[1].split("\t")
            fields[2] = ("0" if fields[2][0] != "0" else "1") + fields[2][1:]
            rows[1] = "\t".join(fields)
            hash_mutant.write_text("\n".join(rows) + "\n", encoding="ascii")
            with self.assertRaisesRegex(reducer.CoreReductionError, "hash differs"):
                reducer.verify_clause_mapping(
                    cnf,
                    output / "cover6_closed_master_d8_bounded13_core.cnf",
                    hash_mutant,
                )

            id_mutant = root / "id-mutant.tsv"
            rows = original.splitlines()
            fields = rows[2].split("\t")
            fields[1] = "1"
            rows[2] = "\t".join(fields)
            id_mutant.write_text("\n".join(rows) + "\n", encoding="ascii")
            with self.assertRaisesRegex(reducer.CoreReductionError, "ordered one-to-one"):
                reducer.verify_clause_mapping(
                    cnf,
                    output / "cover6_closed_master_d8_bounded13_core.cnf",
                    id_mutant,
                )

            clause_mutant = root / "core-clause-mutant.cnf"
            core_lines = (
                output / "cover6_closed_master_d8_bounded13_core.cnf"
            ).read_bytes().splitlines()
            core_lines[1] = b"-1 0"
            clause_mutant.write_bytes(b"\n".join(core_lines) + b"\n")
            with self.assertRaisesRegex(reducer.CoreReductionError, "content differs"):
                reducer.verify_clause_mapping(cnf, clause_mutant, mapping)

    def test_tracked_master_analysis_is_honest(self) -> None:
        report = self.tracked_report()
        self.assertEqual(report["status"], "PASS_RUP_CORE_ANALYSIS")
        self.assertEqual(report["proof"]["rat_additions"], 0)
        self.assertLess(
            report["core"]["initial_clauses"], report["input"]["initial_clauses"]
        )
        self.assertIn("must be replayed", report["scope"])

    def test_tracked_core_manifest_matches_every_artifact(self) -> None:
        manifest = self.tracked_manifest()
        self.assertEqual(manifest["status"], "PASS_REDUCED_MASTER8_CORE_DUAL_REPLAY")
        directory = self.core_directory()
        for metadata in manifest["artifacts"].values():
            path = directory / metadata["name"]
            payload = path.read_bytes()
            self.assertEqual(len(payload), metadata["bytes"], path.name)
            self.assertEqual(
                hashlib.sha256(payload).hexdigest().upper(),
                metadata["sha256"],
                path.name,
            )
            if "lines" in metadata:
                self.assertEqual(payload.count(b"\n"), metadata["lines"], path.name)
        self.assertEqual(
            manifest["validation"]["remapped_lrat"]["status"],
            "LEAN_LRAT_REPLAY_PASS",
        )
        self.assertEqual(
            manifest["validation"]["cadical_regenerated_lrat"]["cadical_status"],
            "UNSAT_WITH_INTERNAL_LRAT_CHECK_PASS",
        )
        self.assertEqual(
            manifest["validation"]["cadical_regenerated_lrat"]["lean_status"],
            "LEAN_LRAT_REPLAY_PASS",
        )
        self.assertIn("frozen Master8 CNF", manifest["scope"])

    def test_both_tracked_lrats_parse_and_match_manifest(self) -> None:
        manifest = self.tracked_manifest()
        directory = self.core_directory()
        cnf = directory / manifest["artifacts"]["cnf"]["name"]
        remapped = reducer.verify_reduced_pair(
            cnf, directory / manifest["artifacts"]["remapped_lrat"]["name"]
        )
        self.assertEqual(
            remapped["proof"]["additions"],
            manifest["artifacts"]["remapped_lrat"]["additions"],
        )
        self.assertEqual(remapped["proof"]["rat_additions"], 0)
        self.assertEqual(
            remapped["input"]["lrat"]["sha256"],
            manifest["artifacts"]["remapped_lrat"]["sha256"],
        )
        regenerated = reducer._public_analysis(
            reducer.analyze(
                cnf,
                directory
                / manifest["artifacts"]["cadical_regenerated_lrat"]["name"],
                master_identity=False,
            )
        )
        self.assertEqual(
            regenerated["proof"]["additions"],
            manifest["artifacts"]["cadical_regenerated_lrat"]["additions"],
        )
        self.assertEqual(
            regenerated["proof"]["lines"],
            manifest["artifacts"]["cadical_regenerated_lrat"]["lines"],
        )
        self.assertEqual(regenerated["proof"]["rat_additions"], 0)
        self.assertEqual(
            regenerated["input"]["lrat"]["sha256"],
            manifest["artifacts"]["cadical_regenerated_lrat"]["sha256"],
        )

    @unittest.skipUnless(
        os.environ.get("RAMSEY_MASTER8_TRIM_FULL") == "1",
        "set RAMSEY_MASTER8_TRIM_FULL=1 for the read-only S: audit",
    )
    def test_full_master_analysis_matches_report(self) -> None:
        source = Path(
            r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover6-master8-v1"
        )
        generated = reducer._public_analysis(
            reducer.analyze(
                source / reducer.MASTER_CNF_NAME,
                source / reducer.MASTER_LRAT_NAME,
                master_identity=True,
            )
        )
        self.assertEqual(generated, self.tracked_report())

    @unittest.skipUnless(
        os.environ.get("RAMSEY_MASTER8_TRIM_FULL") == "1",
        "set RAMSEY_MASTER8_TRIM_FULL=1 for exact mapping verification",
    )
    def test_full_mapping_and_reduced_pair_match_manifest(self) -> None:
        source = Path(
            r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover6-master8-v1"
        )
        directory = self.core_directory()
        manifest = self.tracked_manifest()
        mapping = reducer.verify_clause_mapping(
            source / reducer.MASTER_CNF_NAME,
            directory / manifest["artifacts"]["cnf"]["name"],
            directory / manifest["artifacts"]["initial_clause_mapping"]["name"],
        )
        self.assertEqual(mapping["status"], "PASS_EXACT_ORDERED_SUBSEQUENCE")
        self.assertEqual(
            mapping["mapping"],
            {
                "bytes": manifest["artifacts"]["initial_clause_mapping"]["bytes"],
                "sha256": manifest["artifacts"]["initial_clause_mapping"]["sha256"],
            },
        )
        reduced = reducer.verify_reduced_pair(
            directory / manifest["artifacts"]["cnf"]["name"],
            directory / manifest["artifacts"]["remapped_lrat"]["name"],
        )
        self.assertEqual(
            reduced["status"],
            "PASS_CLOSED_RUP_DEPENDENCY_CORE_REPLAY_STILL_REQUIRED",
        )
        self.assertEqual(reduced["input"]["cnf"], {
            "bytes": manifest["artifacts"]["cnf"]["bytes"],
            "sha256": manifest["artifacts"]["cnf"]["sha256"],
        })
        self.assertEqual(reduced["input"]["lrat"], {
            "bytes": manifest["artifacts"]["remapped_lrat"]["bytes"],
            "sha256": manifest["artifacts"]["remapped_lrat"]["sha256"],
        })

    @unittest.skipUnless(
        os.environ.get("RAMSEY_MASTER8_TRIM_LEAN_MUTANT") == "1",
        "set RAMSEY_MASTER8_TRIM_LEAN_MUTANT=1 and RAMSEY_LAKE for Lean mutant replay",
    )
    def test_lean_rejects_mutated_remapped_lrat(self) -> None:
        lake = os.environ.get("RAMSEY_LAKE")
        if not lake:
            self.skipTest("RAMSEY_LAKE is not set")
        directory = self.core_directory()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "core.cnf"
            lrat = root / "mutant.lrat"
            cnf.write_bytes(
                (directory / "cover6_closed_master_d8_bounded13_core.cnf").read_bytes()
            )
            lines = (
                directory / "cover6_closed_master_d8_bounded13_core.lrat"
            ).read_bytes().splitlines()
            final = reducer.parse_lrat_line(lines[-1], len(lines))
            self.assertIsInstance(final, reducer.Addition)
            lrat.write_bytes(b"\n".join(lines[:-1]) + b"\n" + f"{final.clause_id} 0 0\n".encode())
            harness = root / "MutantReplay.lean"
            harness.write_text(
                "import LRATCatcher.Reflect\n\n"
                "lrat_reflect mutated_core_unsat\n"
                f'  "{cnf.as_posix()}"\n'
                f'  "{lrat.as_posix()}"\n',
                encoding="utf-8",
            )
            completed = subprocess.run(
                [lake, "env", "lean", str(harness)],
                cwd=reducer.REPOSITORY / "vendor" / "lrat-catcher",
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                check=False,
            )
            self.assertNotEqual(completed.returncode, 0)
            self.assertIn("native_decide", completed.stdout)


if __name__ == "__main__":
    unittest.main()
