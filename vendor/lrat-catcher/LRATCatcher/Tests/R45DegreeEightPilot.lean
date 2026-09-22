import LRATCatcher.ReflectTrim

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

lrat_reflect_trim r45_d8_l22_r01_unsat
  "../../scripts/r45_d8_pilot/evidence/lrat/d8_l22_r01.cnf"
  "../../scripts/r45_d8_pilot/evidence/lrat/d8_l22_r01.lrat"

/-- Recover the exact formula occurring in an UNSAT theorem without parsing
the DIMACS file a second time. -/
def certifiedFormulaOfUnsat {formula : Std.Sat.CNF Nat}
    (_ : formula.Unsat) : Std.Sat.CNF Nat :=
  formula

/-- Exact parsed contents of the certified pilot leaf. -/
def r45D8L22R01Formula : Std.Sat.CNF Nat :=
  certifiedFormulaOfUnsat r45_d8_l22_r01_unsat

theorem r45D8L22R01Formula_unsat : r45D8L22R01Formula.Unsat := by
  exact r45_d8_l22_r01_unsat

theorem r45D8L22R01Formula_numClauses :
    r45D8L22R01Formula.clauses.size = 55154 := by
  native_decide

theorem r45D8L22R01Formula_numLiterals :
    r45D8L22R01Formula.numLiterals = 276 := by
  native_decide

#print axioms r45_d8_l22_r01_unsat
#print axioms r45D8L22R01Formula_unsat

end LRATCatcher.Tests
