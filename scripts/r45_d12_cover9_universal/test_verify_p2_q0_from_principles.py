from __future__ import annotations

import ast
import os
import unittest
from pathlib import Path

from . import verify_p2_q0_from_principles as audit


class P2Q0FromPrinciplesLocalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.permutations = tuple(__import__("itertools").permutations(range(7)))
        cls.forbidden, cls.raw_orbits = audit.build_raw_forbidden(cls.permutations)
        cls.cubes, cls.cube_orbits = audit.build_reduced_cubes(cls.permutations)

    def test_standalone_verifier_has_no_project_imports(self) -> None:
        source_path = Path(audit.__file__)
        tree = ast.parse(source_path.read_text(encoding="utf-8"), filename=str(source_path))
        imported_roots: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported_roots.update(alias.name.split(".", 1)[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom):
                if node.level:
                    self.fail(f"non-stdlib/project import found: {ast.dump(node)}")
                if node.module != "__future__" and node.module is not None:
                    imported_roots.add(node.module.split(".", 1)[0])
        self.assertLessEqual(
            imported_roots,
            {
                "argparse",
                "collections",
                "hashlib",
                "itertools",
                "json",
                "math",
                "os",
                "pathlib",
                "sys",
                "typing",
            },
        )

    def test_nine_graph6_orbits_and_six_cube_orbits_are_frozen(self) -> None:
        self.assertEqual(self.raw_orbits, audit.EXPECTED_RAW_ORBIT_COUNTS)
        self.assertEqual(len(self.forbidden), 26_460)
        self.assertEqual(self.cube_orbits, audit.EXPECTED_REDUCED_ORBIT_COUNTS)
        self.assertEqual(len(self.cubes), 15_120)

    def test_k12_r44_and_both_assignments_are_exact(self) -> None:
        self.assertEqual(len(tuple(audit.ramsey_clauses())), 990)
        self.assertEqual(len(audit.build_root_base_clauses()), 717)
        self.assertEqual(
            tuple(variable if value else -variable for variable, value in audit.root_assignment().items()),
            tuple(range(1, 9)) + (-9, -10, -11),
        )
        self.assertEqual(
            tuple(
                variable if value else -variable
                for variable, value in audit.second_center_assignment().items()
            ),
            (12, 13, -14, -15, -16, -17, -18, -19, -20, -21),
        )

    def test_restriction_canonicalization_and_malformed_clause_guard(self) -> None:
        assignment = audit.second_center_assignment()
        untouched = audit.edge_var(12, 3, 4)
        self.assertIsNone(audit.canonical_restriction((12, untouched), assignment))
        self.assertEqual(
            audit.canonical_restriction((14, -untouched), assignment),
            (-untouched,),
        )
        with self.assertRaisesRegex(audit.AuditError, "duplicate|tautological|noncanonical"):
            audit._validate_canonical_clause((untouched, -untouched), frozenset())

    def test_frozen_formula_and_certificate_identities(self) -> None:
        self.assertEqual(audit.EXPECTED_FINAL_CLAUSES, 758_924)
        self.assertEqual(audit.EXPECTED_FINAL_BYTES, 44_764_698)
        self.assertEqual(
            audit.EXPECTED_FINAL_SHA256,
            "D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315",
        )
        self.assertEqual(audit.EXPECTED_LRAT_BYTES, 10_683_195)
        self.assertEqual(audit.EXPECTED_LRAT_FINAL_CLAUSE_ID, 859_522)


@unittest.skipUnless(
    os.environ.get("R45_D12_P2Q0_RUN_FULL_AUDIT") == "1"
    or os.environ.get("R45_D12_P2Q0_CNF"),
    "set R45_D12_P2Q0_RUN_FULL_AUDIT=1 or R45_D12_P2Q0_CNF for the exhaustive audit",
)
class P2Q0FromPrinciplesOptionalExternalTest(unittest.TestCase):
    def test_full_reconstruction_and_optional_external_artifacts(self) -> None:
        def optional_path(name: str) -> Path | None:
            value = os.environ.get(name)
            return Path(value) if value else None

        cnf = optional_path("R45_D12_P2Q0_CNF")
        report = audit.run_audit(
            cnf=cnf,
            lrat=optional_path("R45_D12_P2Q0_LRAT"),
            replay_lean=optional_path("R45_D12_P2Q0_REPLAY_LEAN"),
            replay_log=optional_path("R45_D12_P2Q0_REPLAY_LOG"),
            replay_json=optional_path("R45_D12_P2Q0_REPLAY_JSON"),
        )
        self.assertEqual(report["status"], "PASS")
        self.assertTrue(
            report["second_center"]["semantic_authorization"]
            ["every_final_clause_has_an_authorized_preimage"]
        )
        reconstructed = report["formula"]["reconstructed"]
        self.assertEqual(reconstructed["clauses"], audit.EXPECTED_FINAL_CLAUSES)
        self.assertEqual(reconstructed["bytes"], audit.EXPECTED_FINAL_BYTES)
        self.assertEqual(reconstructed["sha256"], audit.EXPECTED_FINAL_SHA256)
        if cnf is not None:
            self.assertTrue(
                report["formula"]["external"]
                ["byte_for_byte_equal_to_authorized_reconstruction"]
            )


if __name__ == "__main__":
    unittest.main()
