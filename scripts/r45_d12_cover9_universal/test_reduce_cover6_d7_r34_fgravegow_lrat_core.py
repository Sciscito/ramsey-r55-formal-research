from __future__ import annotations

import copy
import hashlib
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from . import reduce_cover6_d7_r34_fgravegow_lrat_core as reducer
from . import reduce_master8_lrat_core as corelib


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

TRACKED_GOLDEN = {
    ".gitattributes": (
        78,
        "0D3A87415F0DD8A34B869279597919CB8F2F7843D82BD4AAEDA98C1307F19650",
    ),
    "core_clause_map.tsv": (
        450_424,
        "4324BD649921CA8EF00673A002D051C7046FE0B5D31144B59A07FAD7BF73D992",
    ),
    "cover6_closed_f7_r34_i6_FgraveGOW_core.cnf": (
        289_163,
        "2DD4F2F3359A78163B20B7103804A34E081F71CE436D8332DAE71309A54C0B6E",
    ),
    "cover6_closed_f7_r34_i6_FgraveGOW_core.lrat": (
        864_692,
        "2663E5943CE593EB7E9C3E21D588601AFFD528C419C946CE3B337D4649A1D188",
    ),
    "lean_replay.log": (
        202,
        "8FC2F5C4F8C37914211C8C2A6414CF1942C553D2014A91F77F5EBAFDB5621C6B",
    ),
    "MANIFEST.json": (
        9_942,
        "8A7E66C31F1AF2E8BA81F4FE765D6D1D1EAC2C457EB8FCEB80C1DCC1313C1409",
    ),
    "reduction.json": (
        4_725,
        "FD9A9191DAA2D9CA86903E28A5FF0EF2B52320920D569C50F91F8AC26825C52A",
    ),
    "Replay.lean": (
        520,
        "B4FC1D0B115D6A334C19B1B1D55F5B29916DBDEBD5D955AD18D3DB05FCEADAAD",
    ),
}
TRACKED_MILESTONE_GOLDEN = (
    4_218,
    "2AA548863E6CD3D4BB78910AB289F9EB2F76A0D6DBF2D0F85E3C9E6CBFFD028E",
)


def valid_run_report_payload() -> dict[str, object]:
    return {
        "status": "CADICAL_CHECKED_LRAT_CANDIDATE_PENDING_INDEPENDENT_REPLAY",
        "formula": {
            "sha256": reducer.SOURCE_CNF_SHA256,
            "bytes": reducer.SOURCE_CNF_BYTES,
            "lines": reducer.SOURCE_CNF_CLAUSES + 1,
        },
        "result": {
            "lrat": {
                "sha256": reducer.SOURCE_LRAT_SHA256,
                "bytes": reducer.SOURCE_LRAT_BYTES,
            },
            "metrics": {"lrat_added_clauses": reducer.SOURCE_LRAT_ADDITIONS},
            "lrat_published": True,
        },
        "solver": {"returncode": 20},
        "selection": {
            "record": "F`GOW",
            "source_catalogue_index_zero_based": 5,
            "incremental_position_one_based": 6,
        },
    }


class FgraveGowCoreReducerTests(unittest.TestCase):
    @classmethod
    def tracked_directory(cls) -> Path:
        return Path(reducer.__file__).with_name("master7_r34_fgravegow_core")

    @classmethod
    def tracked_manifest(cls) -> dict[str, object]:
        return json.loads(
            (cls.tracked_directory() / "MANIFEST.json").read_text(encoding="utf-8")
        )

    def test_only_absolute_s_paths_are_accepted(self) -> None:
        accepted = Path(r"S:\proofs\core-v1")
        self.assertEqual(reducer.require_absolute_s(accepted, "test"), accepted)
        for rejected in (Path("relative"), Path(r"C:\proofs\core-v1")):
            with self.subTest(path=rejected):
                with self.assertRaisesRegex(reducer.FgraveGowCoreError, "absolute S"):
                    reducer.require_absolute_s(rejected, "test")
        with self.assertRaisesRegex(reducer.FgraveGowCoreError, "must not contain"):
            reducer.require_absolute_s(Path(r"S:\proofs\..\escape"), "test")

    def test_reparse_component_is_rejected(self) -> None:
        with mock.patch.object(
            reducer.os,
            "lstat",
            return_value=SimpleNamespace(st_file_attributes=0x00000400),
        ):
            with self.assertRaisesRegex(reducer.FgraveGowCoreError, "reparse point"):
                reducer.reject_reparse_components(Path(r"S:\proofs\core"), "test")

    def test_caps_are_inclusive_and_every_overrun_is_rejected(self) -> None:
        result = reducer.validate_compact_caps(
            reducer.MAX_CORE_CLAUSES,
            reducer.MAX_CORE_CNF_BYTES,
            reducer.MAX_CORE_LRAT_BYTES,
        )
        self.assertEqual(result["status"], "PASS_COMPACT_CORE_CAPS")
        overruns = (
            (reducer.MAX_CORE_CLAUSES + 1, 0, 0),
            (0, reducer.MAX_CORE_CNF_BYTES + 1, 0),
            (0, 0, reducer.MAX_CORE_LRAT_BYTES + 1),
            (-1, 0, 0),
        )
        for values in overruns:
            with self.subTest(values=values):
                with self.assertRaises(reducer.FgraveGowCoreError):
                    reducer.validate_compact_caps(*values)

    def test_run_report_semantics_and_nested_mutant(self) -> None:
        report = valid_run_report_payload()
        reducer.validate_run_report_payload(report)
        mutant = copy.deepcopy(report)
        mutant["result"]["lrat"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(reducer.FgraveGowCoreError, "semantic mismatch"):
            reducer.validate_run_report_payload(mutant)
        malformed = copy.deepcopy(report)
        malformed["result"] = "not-an-object"
        with self.assertRaisesRegex(reducer.FgraveGowCoreError, "semantic mismatch"):
            reducer.validate_run_report_payload(malformed)

    def test_tiny_core_uses_custom_source_label_and_dense_remap(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            core_cnf = root / "core.cnf"
            core_lrat = root / "core.lrat"
            mapping = root / "mapping.tsv"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(TINY_LRAT)
            analysis = corelib.analyze(cnf, lrat, master_identity=False)
            index = analysis["_index"]
            dependency = analysis["_core"]
            initial_map, _, _ = corelib.write_core_cnf(
                cnf,
                core_cnf,
                mapping,
                2,
                4,
                dependency,
                source_clause_label=reducer.MAPPING_SOURCE_LABEL,
            )
            corelib.write_core_lrat(
                lrat, core_lrat, 4, index, dependency, initial_map
            )
            self.assertEqual(
                mapping.read_bytes().splitlines()[0],
                b"core_clause_id\tfgravegow_clause_id\tclause_sha256",
            )
            self.assertEqual(
                core_cnf.read_bytes(), b"p cnf 2 3\n1 0\n-1 2 0\n-2 0\n"
            )
            self.assertEqual(
                core_lrat.read_bytes(),
                b"4 2 0 1 2 0\n1 d 1 0\n5 0 4 3 0\n",
            )
            verified = corelib.verify_clause_mapping(
                cnf,
                core_cnf,
                mapping,
                source_clause_label=reducer.MAPPING_SOURCE_LABEL,
            )
            self.assertEqual(verified["status"], "PASS_EXACT_ORDERED_SUBSEQUENCE")
            self.assertEqual(
                corelib.verify_reduced_pair(core_cnf, core_lrat)["proof"]["rat_additions"],
                0,
            )

            rows = mapping.read_text(encoding="ascii").splitlines()
            fields = rows[1].split("\t")
            fields[2] = "0" * 64
            rows[1] = "\t".join(fields)
            mutant = root / "mapping-mutant.tsv"
            mutant.write_text("\n".join(rows) + "\n", encoding="ascii")
            with self.assertRaisesRegex(corelib.CoreReductionError, "hash differs"):
                corelib.verify_clause_mapping(
                    cnf,
                    core_cnf,
                    mutant,
                    source_clause_label=reducer.MAPPING_SOURCE_LABEL,
                )

    def test_forward_hint_and_rat_are_detected_before_reduction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            forward = root / "forward.lrat"
            forward.write_bytes(b"5 2 0 6 0\n6 0 5 3 0\n")
            with self.assertRaisesRegex(corelib.CoreReductionError, "non-backward"):
                corelib.index_proof(forward, 4)
            cnf = root / "tiny.cnf"
            rat = root / "rat.lrat"
            cnf.write_bytes(TINY_CNF)
            rat.write_bytes(b"5 2 0 -1 2 0\n6 0 3 4 0\n")
            analysis = corelib.analyze(cnf, rat, master_identity=False)
            self.assertEqual(analysis["proof"]["rat_additions"], 1)
            self.assertEqual(analysis["status"], "RAT_REDUCTION_REFUSED")

    def test_mapping_header_label_is_part_of_verification(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            core_cnf = root / "core.cnf"
            mapping = root / "mapping.tsv"
            cnf.write_bytes(TINY_CNF)
            lrat.write_bytes(TINY_LRAT)
            analysis = corelib.analyze(cnf, lrat, master_identity=False)
            corelib.write_core_cnf(
                cnf,
                core_cnf,
                mapping,
                2,
                4,
                analysis["_core"],
                source_clause_label=reducer.MAPPING_SOURCE_LABEL,
            )
            with self.assertRaisesRegex(corelib.CoreReductionError, "unexpected.*header"):
                corelib.verify_clause_mapping(cnf, core_cnf, mapping)

            variable_mutant = root / "variable-mutant.cnf"
            lines = core_cnf.read_bytes().splitlines()
            lines[0] = b"p cnf 3 3"
            variable_mutant.write_bytes(b"\n".join(lines) + b"\n")
            with self.assertRaisesRegex(corelib.CoreReductionError, "variable count"):
                corelib.verify_clause_mapping(
                    cnf,
                    variable_mutant,
                    mapping,
                    source_clause_label=reducer.MAPPING_SOURCE_LABEL,
                )

    def test_replay_source_freezes_paths_namespace_and_theorem(self) -> None:
        payload = reducer.lean_source(
            Path(r"S:\core\leaf.cnf"), Path(r"S:\core\leaf.lrat")
        ).decode("utf-8")
        self.assertIn('"S:/core/leaf.cnf"', payload)
        self.assertIn('"S:/core/leaf.lrat"', payload)
        self.assertIn(f"namespace {reducer.LEAN_NAMESPACE}", payload)
        self.assertIn(f"lrat_reflect {reducer.LEAN_THEOREM}", payload)
        self.assertIn(f"#print axioms {reducer.LEAN_THEOREM}", payload)

    def test_tracked_replay_source_is_portable_and_repo_relative(self) -> None:
        payload = reducer.tracked_replay_source()
        reducer._assert_no_absolute_paths(payload, "test Replay")
        text_payload = payload.decode("utf-8")
        self.assertIn(
            '"../../scripts/r45_d12_cover9_universal/'
            'master7_r34_fgravegow_core/'
            f'{reducer.CORE_CNF_NAME}"',
            text_payload,
        )
        self.assertNotIn("S:", text_payload)

    def test_portability_scan_rejects_drive_unc_uri_and_unix_roots(self) -> None:
        reducer._assert_no_absolute_paths(b'{"path":"relative/file"}', "relative")
        mutants = (
            b'{"path":"C:\\\\Users\\\\name"}',
            b'{"path":"\\\\\\\\server\\\\share"}',
            b'{"path":"file://host/path"}',
            b'{"path":"/home/name/file"}',
            b'{"path":"/tmp/file"}',
        )
        for mutant in mutants:
            with self.subTest(mutant=mutant):
                with self.assertRaisesRegex(reducer.FgraveGowCoreError, "absolute path"):
                    reducer._assert_no_absolute_paths(mutant, "mutant")

    def test_portable_replay_provenance_strips_machine_paths(self) -> None:
        stack = {
            "status": "PASS_PINNED_SELECTED_LEAN_LRATCATCHER_IDENTITIES",
            "lean_version": "4.30.0",
            "lean_executable": {
                "path": r"S:\toolchain\lean.exe",
                "bytes": 1,
                "sha256": "A" * 64,
            },
            "toolchain_bin_tree": {
                "path": r"S:\toolchain\bin",
                "files": 1,
                "bytes": 1,
                "sha256": "B" * 64,
                "algorithm": "test",
            },
            "standard_modules": [],
            "lratcatcher_source_files": [],
            "lratcatcher_build_files": [],
            "identity_scope": {
                "pinned": "selected",
                "not_exhaustive": "transitive closure",
                "runtime_import_path": "direct target",
            },
        }
        supervision = {
            "command": [r"S:\toolchain\lean.exe", r"C:\repo\Replay.lean"],
            "environment_policy": {"path": r"S:\toolchain\bin"},
            "returncode": 0,
            "stop_reason": None,
            "wall_seconds": 1.0,
            "peak_job_memory_bytes": 1,
            "job_memory_limit_bytes": 2,
            "wall_limit_seconds": 600.0,
            "log_limit_bytes": 8,
            "job_object_assigned": True,
            "launch_suspended_until_job_assignment": True,
            "job_memory_scope": "lean plus every descendant process",
            "kill_on_job_close": True,
            "launch_error": None,
        }
        portable = {
            "stack": reducer._portable_stack(stack),
            "supervision": reducer._portable_supervision(supervision),
        }
        payload = json.dumps(portable, sort_keys=True).encode("utf-8")
        reducer._assert_no_absolute_paths(payload, "portable provenance")
        self.assertNotIn("path", portable["stack"]["toolchain_bin_tree"])

    def test_stream_copy_is_exact_and_refuses_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            target = root / "target.partial"
            source.write_bytes(b"one\ntwo\n")
            metadata = reducer._copy_new(source, target)
            self.assertEqual(target.read_bytes(), source.read_bytes())
            self.assertEqual(metadata["bytes"], 8)
            self.assertEqual(metadata["lines"], 2)
            with self.assertRaises(FileExistsError):
                reducer._copy_new(source, target)

    def test_tracked_artifact_golden_hashes_and_manifest(self) -> None:
        directory = self.tracked_directory()
        manifest = self.tracked_manifest()
        self.assertEqual(
            manifest["status"],
            "PASS_TRACKED_FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY",
        )
        for name, (expected_bytes, expected_hash) in TRACKED_GOLDEN.items():
            with self.subTest(name=name):
                payload = (directory / name).read_bytes()
                self.assertEqual(len(payload), expected_bytes)
                self.assertEqual(
                    hashlib.sha256(payload).hexdigest().upper(), expected_hash
                )
        milestone_payload = reducer.TRACKED_MILESTONE_REPORT.read_bytes()
        self.assertEqual(len(milestone_payload), TRACKED_MILESTONE_GOLDEN[0])
        self.assertEqual(
            hashlib.sha256(milestone_payload).hexdigest().upper(),
            TRACKED_MILESTONE_GOLDEN[1],
        )
        for metadata in manifest["artifacts"].values():
            path = directory / metadata["name"]
            payload = path.read_bytes()
            self.assertEqual(len(payload), metadata["bytes"], path.name)
            self.assertEqual(
                hashlib.sha256(payload).hexdigest().upper(),
                metadata["sha256"],
                path.name,
            )
            self.assertEqual(payload.count(b"\n"), metadata["lines"], path.name)
        self.assertEqual(manifest["dependency_core"]["initial_clauses"], 5_807)
        self.assertEqual(manifest["dependency_core"]["derived_additions"], 9_475)
        self.assertEqual(manifest["validation"]["lean"]["status"], "LEAN_LRAT_REPLAY_PASS")
        self.assertTrue(manifest["validation"]["lean"]["axioms_allowed"])
        self.assertIn(
            "not exhaustively hashed",
            manifest["validation"]["lean"]["frozen_stack"]["identity_scope"][
                "not_exhaustive"
            ],
        )
        self.assertFalse(list(directory.glob("*.partial")))

    def test_tracked_mapping_hashes_every_core_clause_in_order(self) -> None:
        directory = self.tracked_directory()
        cnf = directory / reducer.CORE_CNF_NAME
        mapping = directory / reducer.MAPPING_NAME
        with mapping.open("rb") as stream:
            self.assertEqual(
                stream.readline().rstrip(b"\r\n"),
                b"core_clause_id\tfgravegow_clause_id\tclause_sha256",
            )
            rows = [line.rstrip(b"\r\n").split(b"\t") for line in stream]
        self.assertEqual(len(rows), reducer.TRACKED_CORE_INITIAL_CLAUSES)
        previous_source_id = 0
        clauses = list(corelib._dimacs_clauses(cnf))
        self.assertEqual(len(clauses), len(rows))
        for expected_core_id, (fields, clause_entry) in enumerate(
            zip(rows, clauses), 1
        ):
            self.assertEqual(len(fields), 3)
            core_id, source_id = int(fields[0]), int(fields[1])
            observed_core_id, canonical_clause = clause_entry
            self.assertEqual(core_id, expected_core_id)
            self.assertEqual(observed_core_id, expected_core_id)
            self.assertGreater(source_id, previous_source_id)
            self.assertEqual(
                fields[2].decode("ascii"),
                hashlib.sha256(canonical_clause).hexdigest().upper(),
            )
            previous_source_id = source_id

        replay = corelib.verify_reduced_pair(
            cnf, directory / reducer.CORE_LRAT_NAME
        )
        self.assertEqual(replay["proof"]["additions"], 9_475)
        self.assertEqual(replay["proof"]["rup_additions"], 9_475)
        self.assertEqual(replay["proof"]["rat_additions"], 0)
        self.assertEqual(replay["proof"]["deletion_actions"], 8_283)
        self.assertEqual(replay["proof"]["deleted_identifiers"], 9_758)

    def test_tracked_portable_files_have_no_machine_paths(self) -> None:
        directory = self.tracked_directory()
        for path in (
            directory / "MANIFEST.json",
            directory / "reduction.json",
            directory / "Replay.lean",
            directory / "lean_replay.log",
            reducer.TRACKED_MILESTONE_REPORT,
        ):
            with self.subTest(path=path.name):
                reducer._assert_no_absolute_paths(path.read_bytes(), path.name)
        manifest = self.tracked_manifest()
        self.assertIn("S7 orbit coverage/composition", manifest["formal_boundary"])
        milestone = json.loads(
            reducer.TRACKED_MILESTONE_REPORT.read_text(encoding="utf-8")
        )
        self.assertEqual(
            milestone["status"], "PASS_MASTER7_R34_FGRAVEGOW_TRACKED_CORE_V1"
        )
        self.assertIn("not the remaining S7", milestone["value"])

    @unittest.skipUnless(
        os.environ.get("RAMSEY_FGRAVEGOW_TRACKED_SOURCE_FULL") == "1",
        "set RAMSEY_FGRAVEGOW_TRACKED_SOURCE_FULL=1 for exact source mapping",
    )
    def test_tracked_full_source_mapping_and_core_linkage(self) -> None:
        source = Path(
            r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-mincenter-v1"
        )
        verification = reducer.verify_tracked(source)
        self.assertEqual(
            verification["status"],
            "PASS_EXACT_TRACKED_FGRAVEGOW_CORE_REPLAY_REQUIRED",
        )
        self.assertEqual(
            verification["mapping"]["status"], "PASS_EXACT_ORDERED_SUBSEQUENCE"
        )

    @unittest.skipUnless(
        os.environ.get("RAMSEY_FGRAVEGOW_TRACKED_LEAN") == "1"
        and os.environ.get("RAMSEY_FGRAVEGOW_TRACKED_LEAN_TEMP"),
        "set RAMSEY_FGRAVEGOW_TRACKED_LEAN=1 and an absolute S: temp directory",
    )
    def test_tracked_opt_in_lean_replay_under_caps(self) -> None:
        temporary_directory = Path(
            os.environ["RAMSEY_FGRAVEGOW_TRACKED_LEAN_TEMP"]
        )
        reducer.require_absolute_s(temporary_directory, "Lean test temporary directory")
        reducer.reject_reparse_components(
            temporary_directory, "Lean test temporary directory"
        )
        paths = reducer.tracked_paths()
        core_keys = ("cnf", "lrat", "mapping", "reduction", "replay", "gitattributes")
        inputs = [paths[key] for key in core_keys] + reducer.frozen_replay_files()
        with tempfile.TemporaryDirectory() as local_temporary:
            log_partial = Path(local_temporary) / "lean.log.partial"
            with reducer.WindowsReadLocks(inputs):
                supervision = reducer._lean_supervised(
                    reducer.LEAN_EXE,
                    paths["replay"],
                    log_partial,
                    temporary_directory=temporary_directory,
                )
            log_text = log_partial.read_text(encoding="utf-8", errors="replace")
        self.assertEqual(supervision["returncode"], 0)
        self.assertIsNone(supervision["stop_reason"])
        self.assertLessEqual(
            supervision["peak_job_memory_bytes"],
            reducer.LEAN_JOB_MEMORY_LIMIT_BYTES,
        )
        self.assertTrue(reducer.axioms_allowed(reducer.parse_axioms(log_text)))

    def test_axiom_parser_accepts_only_expected_native_axiom(self) -> None:
        unrelated = "'Other.theorem' depends on axioms: [sorryAx]\n"
        log = unrelated + (
            f"'{reducer.LEAN_QUALIFIED_THEOREM}' depends on axioms: [propext,\n"
            " Classical.choice, Quot.sound,\n"
            f" {reducer.LEAN_THEOREM}._native.native_decide.ax_1_1]\n"
        )
        axioms = reducer.parse_axioms(log)
        self.assertTrue(reducer.axioms_allowed(axioms))
        self.assertFalse(reducer.axioms_allowed(axioms + ["sorryAx"]))
        self.assertEqual(reducer.parse_axioms("no axiom report"), [])

    def test_core_linkage_rejects_a_valid_but_different_compact_pair(self) -> None:
        analysis = {
            "core": {
                "initial_clauses": 3,
                "derived_additions": 2,
                "dependency_edges": 4,
                "retained_deletion_actions": 1,
                "retained_deleted_identifiers": 1,
            }
        }
        reduced = {
            "input": {"variables": reducer.SOURCE_CNF_VARIABLES, "initial_clauses": 3},
            "proof": {
                "additions": 2,
                "deletion_actions": 1,
                "deleted_identifiers": 1,
            },
            "core": {"dependency_edges": 4},
        }
        mapping = {
            "rows": 3,
            "core_clauses": 3,
            "master_variables": reducer.SOURCE_CNF_VARIABLES,
            "core_variables": reducer.SOURCE_CNF_VARIABLES,
            "master_clauses": reducer.SOURCE_CNF_CLAUSES,
        }
        caps = {"observed": {"clauses": 3}}
        reducer._verify_core_linkage(analysis, reduced, mapping, caps)
        mutant = copy.deepcopy(reduced)
        mutant["proof"]["additions"] = 1
        with self.assertRaisesRegex(reducer.FgraveGowCoreError, "compact additions"):
            reducer._verify_core_linkage(analysis, mutant, mapping, caps)

    def test_reduction_report_cross_checks_artifact_hash_claims(self) -> None:
        analysis = {
            "input": {"x": 1},
            "proof": {"x": 2},
            "core": {"x": 3},
            "audit": {"x": 4},
            "source_run_report": {"x": 5},
        }
        reduced = {"status": "ok"}
        mapping = {"status": "mapped"}
        caps = {"status": "caps"}
        artifacts = {
            key: {"name": key, "bytes": 1, "lines": 1, "sha256": "A" * 64}
            for key in ("cnf", "lrat", "mapping", "replay", "reduction")
        }
        report = {
            "status": "PASS_REDUCED_FGRAVEGOW_CORE_REPLAY_REQUIRED",
            **analysis,
            "caps": caps,
            "validation": {
                "reduced_pair": reduced,
                "initial_clause_mapping": mapping,
                "lean_replay": "PENDING",
            },
            "output": {
                "cnf": artifacts["cnf"],
                "lrat": artifacts["lrat"],
                "initial_clause_mapping": artifacts["mapping"],
                "replay_module": artifacts["replay"],
            },
        }
        reducer._verify_reduction_report(
            report, analysis, reduced, mapping, caps, artifacts
        )
        mutant = copy.deepcopy(report)
        mutant["output"]["lrat"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(reducer.FgraveGowCoreError, "lrat.sha256"):
            reducer._verify_reduction_report(
                mutant, analysis, reduced, mapping, caps, artifacts
            )

    def test_publish_is_atomic_and_never_overwrites(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            partial = root / "artifact.partial"
            final = root / "artifact"
            partial.write_bytes(b"new")
            final.write_bytes(b"old")
            with self.assertRaises(FileExistsError):
                reducer._publish_new(partial, final)
            self.assertEqual(partial.read_bytes(), b"new")
            self.assertEqual(final.read_bytes(), b"old")

    def test_simulated_lean_launch_is_job_supervised_and_log_bounded(self) -> None:
        events: list[object] = []

        class FakeProcess:
            def __init__(self) -> None:
                self.stdout = io.BytesIO(b"1234")
                self.returncode = 0
                self._handle = 42

            def poll(self) -> int:
                return self.returncode

            def wait(self, timeout: float | None = None) -> int:
                del timeout
                return self.returncode

            def kill(self) -> None:
                events.append("process-kill")

        class FakeJob:
            def __init__(self, limit: int) -> None:
                self.assigned = False
                events.append(("job-create", limit))

            def assign(self, process: FakeProcess) -> None:
                self.assigned = True
                events.append(("job-assign", process._handle))

            def peak_memory_bytes(self) -> int:
                return 123

            def terminate(self) -> None:
                events.append("job-terminate")

            def close(self) -> None:
                events.append("job-close")

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def fake_popen(*_args: object, **kwargs: object) -> FakeProcess:
                events.append(("popen", kwargs["creationflags"]))
                self.assertNotIn("PYTHONPATH", kwargs["env"])
                self.assertEqual(
                    kwargs["env"]["LEAN_PATH"], str(reducer.LRAT_CATCHER_LEAN_PATH)
                )
                return FakeProcess()

            def fake_resume(process: FakeProcess) -> None:
                events.append(("resume", process._handle))

            with mock.patch.object(reducer.subprocess, "Popen", side_effect=fake_popen):
                with mock.patch.object(reducer, "WindowsFamilyJob", FakeJob):
                    with mock.patch.object(
                        reducer, "resume_suspended_process", side_effect=fake_resume
                    ):
                        with mock.patch.object(reducer, "LEAN_LOG_LIMIT_BYTES", 4):
                            result = reducer._lean_supervised(
                                Path("lean.exe"),
                                root / "Replay.lean",
                                root / "lean.log.partial",
                            )
            self.assertTrue(result["job_object_assigned"])
            self.assertEqual(result["stop_reason"], "LOG_BYTES_LIMIT")
            self.assertEqual((root / "lean.log.partial").read_bytes(), b"1234")
            self.assertEqual(
                events[:4],
                [
                    ("job-create", reducer.LEAN_JOB_MEMORY_LIMIT_BYTES),
                    (
                        "popen",
                        getattr(reducer.subprocess, "CREATE_NO_WINDOW", 0)
                        | getattr(reducer.subprocess, "CREATE_SUSPENDED", 0x00000004),
                    ),
                    ("job-assign", 42),
                    ("resume", 42),
                ],
            )
            self.assertIn("job-close", events)

    @unittest.skipUnless(os.name == "nt", "file sharing locks are Windows-only")
    def test_read_lock_denies_write_and_delete_until_release(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "locked.txt"
            path.write_bytes(b"frozen")
            with reducer.WindowsReadLocks([path]):
                with self.assertRaises(PermissionError):
                    path.write_bytes(b"mutant")
                with self.assertRaises(PermissionError):
                    path.unlink()
                self.assertEqual(path.read_bytes(), b"frozen")
            path.write_bytes(b"released")
            self.assertEqual(path.read_bytes(), b"released")

    def test_termination_fallback_has_only_bounded_waits(self) -> None:
        events: list[object] = []

        class FakeProcess:
            returncode: int | None = None

            def poll(self) -> int | None:
                return self.returncode

            def kill(self) -> None:
                events.append("kill")
                self.returncode = -9

            def wait(self, timeout: float | None = None) -> int:
                events.append(("wait", timeout))
                if len([event for event in events if isinstance(event, tuple)]) == 1:
                    raise reducer.subprocess.TimeoutExpired("lean", timeout)
                return -9

        class FailingJob:
            assigned = True

            def terminate(self) -> None:
                events.append("job-terminate")
                raise OSError("simulated job termination failure")

        errors = reducer._terminate_and_wait(FakeProcess(), FailingJob())
        self.assertEqual(
            events,
            ["job-terminate", "kill", ("wait", 10), "kill", ("wait", 10)],
        )
        self.assertTrue(any("Job terminate failed" in error for error in errors))
        self.assertTrue(any("timed out" in error for error in errors))

    @unittest.skipUnless(os.name == "nt", "Job Object is intentionally Windows-only")
    def test_real_empty_family_job_has_hard_limit_and_closes(self) -> None:
        job = reducer.WindowsFamilyJob(16 * 1024 * 1024)
        self.assertTrue(job.handle)
        self.assertEqual(job.memory_limit_bytes, 16 * 1024 * 1024)
        job.close()
        self.assertIsNone(job.handle)

    def test_failed_replay_cli_exits_nonzero_after_printing_manifest(self) -> None:
        failure = {"status": "FGRAVEGOW_COMPACT_CORE_LEAN_REPLAY_FAILED"}
        arguments = [
            "reducer",
            "replay",
            "--source-dir",
            r"S:\source",
            "--output-dir",
            r"S:\output",
        ]
        with mock.patch.object(sys, "argv", arguments):
            with mock.patch.object(reducer, "replay_lean", return_value=failure):
                with self.assertRaisesRegex(SystemExit, "2"):
                    reducer.main()

    @unittest.skipUnless(
        os.environ.get("RAMSEY_FGRAVEGOW_STACK_FULL") == "1",
        "set RAMSEY_FGRAVEGOW_STACK_FULL=1 for the frozen Lean stack audit",
    )
    def test_frozen_lean_stack_matches_expected_identities(self) -> None:
        identity = reducer.verify_replay_stack()
        self.assertEqual(
            identity["status"],
            "PASS_PINNED_SELECTED_LEAN_LRATCATCHER_IDENTITIES",
        )
        self.assertEqual(identity["lean_version"], "4.30.0")

    @unittest.skipUnless(
        os.environ.get("RAMSEY_FGRAVEGOW_CORE_FULL") == "1",
        "set RAMSEY_FGRAVEGOW_CORE_FULL=1 for the read-only S: source audit",
    )
    def test_full_source_analysis_matches_independent_oracle(self) -> None:
        source = Path(
            r"S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-mincenter-v1"
        )
        analysis = reducer.public_analysis(reducer.analyze_exact(source))
        self.assertEqual(analysis["proof"]["lines"], 795_581)
        self.assertEqual(analysis["proof"]["additions"], 399_094)
        self.assertEqual(analysis["proof"]["rup_additions"], 399_094)
        self.assertEqual(analysis["proof"]["rat_additions"], 0)
        self.assertEqual(analysis["proof"]["deletion_actions"], 396_487)
        self.assertEqual(analysis["proof"]["deleted_identifiers"], 4_428_897)
        self.assertEqual(
            analysis["core"],
            {
                "initial_clauses": 5_807,
                "derived_additions": 9_475,
                "dependency_edges": 72_001,
                "retained_deletion_actions": 8_283,
                "retained_deleted_identifiers": 9_758,
            },
        )


if __name__ == "__main__":
    unittest.main()
