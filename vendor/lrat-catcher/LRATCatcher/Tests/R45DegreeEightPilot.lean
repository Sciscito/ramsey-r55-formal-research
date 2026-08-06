import LRATCatcher.Reflect

/-!
  # Certified prototype leaf for the R(4,5,25) degree-eight split

  This module replays the first LRAT certificate from the 54-leaf pilot.
  The certified formula is the exact direct-Lean-orientation leaf
  `d8_l22_r01`: the fixed-root `R(4,5,25)` reduction plus the selected
  `gen358` and `gen4416` parent units.

  This theorem certifies this one labelled CNF only. The semantic
  completeness of the two imported covers, and the remaining 53 leaves,
  are separate obligations before the degree-eight case can be promoted to
  a Ramsey theorem.
-/

namespace LRATCatcher.Tests

lrat_reflect r45_d8_l22_r01_unsat
  "../../scripts/r45_d8_pilot/evidence/lrat/d8_l22_r01.cnf"
  "../../scripts/r45_d8_pilot/evidence/lrat/d8_l22_r01.lrat"

#print axioms r45_d8_l22_r01_unsat

end LRATCatcher.Tests
