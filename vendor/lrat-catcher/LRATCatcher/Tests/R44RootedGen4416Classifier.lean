import LRATCatcher.Reflect

/-!
  # Certified rooted classifier for the two `gen4416` graphs

  This module replays the single guarded LRAT certificate produced by
  `gen4416_rooted_classifier.py`.  The 83-variable CNF selects one of the
  `9 × 3` rooted `R(3,4)` block pairs, constrains all 56 cross edges, and
  blocks the 64 labelled masks extracted from the two `gen4416` graphs.

  The theorem below certifies this exact CNF as unsatisfiable.  Connecting
  the selectors, clauses, and mask table to the semantic catalogue theorems
  and to graph isomorphisms remains a separate composition obligation.
-/

namespace LRATCatcher.Tests

lrat_reflect r44_rooted_gen4416_classifier_unsat
  "../../scripts/r45_d8_pilot/gen4416_rooted_classification/guarded_counterexample.cnf"
  "../../scripts/r45_d8_pilot/gen4416_rooted_classification/guarded_counterexample.lrat"

#print axioms r44_rooted_gen4416_classifier_unsat

end LRATCatcher.Tests
