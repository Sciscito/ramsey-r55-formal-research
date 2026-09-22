#!/usr/bin/env python3
"""Regression tests for the deterministic rooted ``gen4416`` classifier."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from collections import Counter
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE / "gen4416_rooted_classifier.py"
SPEC = importlib.util.spec_from_file_location("tested_gen4416_classifier", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {MODULE_PATH}")
classifier = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = classifier
SPEC.loader.exec_module(classifier)


class Gen4416RootedClassifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = classifier.build_result()

    def test_exact_audited_model_table(self) -> None:
        models = self.result.allowed_models
        self.assertEqual(len(models), 64)
        self.assertEqual(
            Counter((model.left_selector, model.anti_selector) for model in models),
            {(0, 2): 32, (8, 0): 32},
        )
        self.assertEqual(
            classifier.sha256_bytes(self.result.table_bytes),
            "1995924E5D942F437BF24A649A23EC9843A9375678DA8A044ABAD4FBF05E4670",
        )
        self.assertEqual(classifier.parse_allowed_table(self.result.table_bytes), models)

    def test_exact_guarded_cnf(self) -> None:
        self.assertEqual(classifier.VARIABLE_COUNT, 83)
        self.assertEqual(len(self.result.clauses), 10880)
        self.assertEqual(
            classifier.sha256_bytes(self.result.cnf_bytes),
            "863C78226DDEFE17FEEF046F7F818D01ECFE63EE96663AEFEC1BE81EC591AAF4",
        )
        variables, clauses = classifier.parse_cnf(self.result.cnf_bytes)
        self.assertEqual(variables, 83)
        self.assertEqual(clauses, self.result.clauses)
        self.assertEqual(clauses[0], tuple(range(57, 84)))
        self.assertEqual(
            self.result.metadata["cnf"]["clause_breakdown"],
            {
                "allowed_model_blockers": 64,
                "i4_2left_2anti": 3861,
                "i4_3left_1anti": 1392,
                "k4_1left_3anti": 1890,
                "k4_2left_2anti": 3672,
                "selector_at_least_one": 1,
            },
        )

    def test_each_blocker_excludes_exactly_its_model(self) -> None:
        for model in self.result.allowed_models:
            selector = classifier.selector_variable(
                model.left_selector, model.anti_selector
            )
            assignment = {selector}
            assignment.update(
                variable
                for variable in range(1, classifier.CROSS_VARIABLE_COUNT + 1)
                if (model.mask >> (variable - 1)) & 1
            )
            blocker = classifier.mask_blocking_clause(model)
            self.assertFalse(classifier.clause_satisfied(blocker, assignment))
            for variable in range(1, classifier.CROSS_VARIABLE_COUNT + 1):
                flipped = set(assignment)
                if variable in flipped:
                    flipped.remove(variable)
                else:
                    flipped.add(variable)
                self.assertTrue(classifier.clause_satisfied(blocker, flipped))

    def test_each_allowed_model_has_a_checked_global_isomorphism(self) -> None:
        witnesses = self.result.cover_witnesses
        self.assertEqual(len(witnesses), 64)
        self.assertEqual(
            tuple(witness.model for witness in witnesses),
            self.result.allowed_models,
        )
        self.assertEqual(
            Counter(witness.graph_index for witness in witnesses),
            {0: 32, 1: 32},
        )

        catalogue7 = classifier.read_catalogue(classifier.R35_7, 7)
        catalogue8 = classifier.read_catalogue(classifier.R35_8, 8)
        left_representatives = tuple(
            catalogue7[index] for index in classifier.LEFT_CATALOGUE_INDICES
        )
        anti_representatives = tuple(
            catalogue8[index] for index in classifier.ANTI_CATALOGUE_INDICES
        )
        gen_graphs = classifier.read_gen4416()
        for witness in witnesses:
            model = witness.model
            self.assertEqual(
                witness.graph_index,
                classifier.target_index_for_model(model),
            )
            source = classifier.rooted_completion(
                left_representatives[model.left_selector],
                anti_representatives[model.anti_selector],
                model.mask,
            )
            target = gen_graphs[witness.graph_index][1]
            self.assertTrue(
                classifier.is_isomorphism(source, target, witness.permutation)
            )

    def test_self_complement_witnesses_are_checked_and_minimal(self) -> None:
        gen_graphs = classifier.read_gen4416()
        witnesses = self.result.self_complement_permutations
        self.assertEqual(len(witnesses), 2)
        for (_graph_id, graph), witness in zip(gen_graphs, witnesses, strict=True):
            complement = classifier.ramsey.complement_graph(graph)
            isomorphisms = classifier.all_isomorphisms(complement, graph)
            self.assertTrue(isomorphisms)
            self.assertEqual(witness, min(isomorphisms))

    def test_generated_lean_cover_data_is_exact(self) -> None:
        self.assertEqual(
            classifier.sha256_bytes(self.result.lean_data_bytes),
            "39A747796E2C3FE6FFB9CE2FDE541711A47487A035F4F0C7AB1981BA4243FAB3",
        )
        self.assertEqual(
            classifier.LEAN_COVER_DATA.read_bytes(),
            self.result.lean_data_bytes,
        )
        lean_metadata = self.result.metadata["lean_cover_data"]
        self.assertEqual(lean_metadata["cover_witnesses"], 64)
        self.assertEqual(lean_metadata["target_counts"], {"0": 32, "1": 32})
        self.assertEqual(lean_metadata["self_complement_witnesses"], 2)

    def test_generated_artifacts_rebuild_byte_for_byte(self) -> None:
        self.assertEqual(
            self.result.metadata["status"],
            "ROOTED_CNF_UNSAT_WITH_REPRODUCIBLE_GEN4416_COVER_DATA",
        )
        self.assertEqual(
            self.result.metadata["lean_composition"],
            {
                "cover_checker_module": (
                    "LRATCatcher.Tests.R44RootedGen4416Cover"
                ),
                "target_audit_module": (
                    "LRATCatcher.Tests.R44Gen4416TargetAudit"
                ),
                "classification_module": (
                    "LRATCatcher.Tests.R44Gen4416Classification"
                ),
                "theorem": "ramseyFree_isomorphic_to_gen4416",
            },
        )
        report = classifier.verify(classifier.DEFAULT_OUTPUT)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["allowed_models"], 64)
        self.assertEqual(report["cnf_clauses"], 10880)


if __name__ == "__main__":
    unittest.main()
