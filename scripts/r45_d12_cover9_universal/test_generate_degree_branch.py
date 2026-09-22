from __future__ import annotations

import unittest

from . import generate_degree_branch as branch
from . import generate_universal as universal
from . import independent_verify


class DegreeBranchTests(unittest.TestCase):
    def test_exact_clause_counts(self) -> None:
        self.assertEqual(
            {degree: branch.branch_clause_count(degree) for degree in branch.DEGREES},
            branch.EXPECTED_CLAUSE_COUNTS,
        )

    def test_restricted_local_counts_and_no_root_edges(self) -> None:
        restricted = branch.restricted_local_cubes()
        self.assertEqual(tuple(map(len, restricted)), branch.LOCAL_RESTRICTED_COUNTS)
        self.assertTrue(all(fixed < 1 << 15 for cubes in restricted for _ones, fixed in cubes))
        conditioned = branch.conditioned_local_cubes()
        self.assertEqual(tuple(map(len, conditioned)), branch.LOCAL_CONDITIONED_COUNTS)
        report = independent_verify.verify_conditioned_slices(conditioned)
        self.assertEqual(report["status"], "PASS")

    def test_clause_restriction_semantics(self) -> None:
        assignment = branch.root_assignment(5)
        clauses = list(universal.ramsey_clauses())
        for clause in clauses[:100] + clauses[-100:]:
            reduced = branch.simplify_clause(clause, assignment)
            if reduced is not None:
                self.assertTrue(all(abs(literal) not in assignment for literal in reduced))

    def test_root_assignment_is_prefix(self) -> None:
        assignment = branch.root_assignment(5)
        self.assertEqual(
            tuple(assignment[universal.edge_var(12, 0, vertex)] for vertex in range(1, 12)),
            (True,) * 5 + (False,) * 6,
        )


if __name__ == "__main__":
    unittest.main()
