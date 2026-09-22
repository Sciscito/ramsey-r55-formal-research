import LRATCatcher.CoverTrim
import LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics

/-!
  # Certified guarded master for the red-degree-eight branch

  This module replays the 59-leaf cube-and-conquer certificate for the exact
  guarded master CNF.  A computational equality then identifies every parsed
  clause with `guardedMasterDecomposition`, whose already-proved semantics
  converts UNSAT into all 54 admissible catalogue-pair contradictions.

  The terminal theorem excludes red degree eight at every vertex of a
  `(4,5)`-free coloring of `K_25`.  It is a certified branch result, not by
  itself a proof that no such coloring exists.
-/

namespace LRATCatcher.Tests.R45DegreeEightGuardedMaster

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightBranchComposition
open LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics

/-! ## Trimmed replay of the external cube-and-conquer artifacts -/

set_option maxRecDepth 1000000 in
lrat_cover_reflect_trim guardedMasterCover_unsat
  "../../scripts/r45_d8_pilot/guarded_master/guarded_master.cnf"
  "../../scripts/r45_d8_pilot/guarded_master/cover.icnf"
  "../../scripts/r45_d8_pilot/guarded_master/proofs/leaf_"
  "../../scripts/r45_d8_pilot/guarded_master/proofs/cover.lrat"

/-- Recover the exact parsed formula carried by an UNSAT theorem without
parsing or embedding the DIMACS input a second time. -/
def certifiedFormulaOfUnsat {formula : CNF Nat}
    (_ : formula.Unsat) : CNF Nat :=
  formula

/-- Exact parsed contents of the certified guarded-master DIMACS file. -/
def guardedMasterFormula : CNF Nat :=
  certifiedFormulaOfUnsat guardedMasterCover_unsat

theorem guardedMasterFormula_unsat : guardedMasterFormula.Unsat := by
  exact guardedMasterCover_unsat

/-! ## Exact source bridge and semantic consequences -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Clause-for-clause and literal-for-literal equality between the certified
external master and its Lean decomposition. -/
theorem guardedMasterFormula_eq_decomposition :
    guardedMasterFormula = guardedMasterDecomposition := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

/-- The exact Lean guarded-master decomposition is unsatisfiable. -/
theorem guardedMasterDecomposition_unsat_certified :
    guardedMasterDecomposition.Unsat :=
  Eq.mp (congrArg CNF.Unsat guardedMasterFormula_eq_decomposition)
    guardedMasterFormula_unsat

/-- The single guarded master certificate supplies all 27 × 2 admissible
catalogue-pair contradictions. -/
theorem allAdmissibleDegreeEightPairsContradictory_certified :
    AllAdmissibleDegreeEightPairsContradictory :=
  guardedMaster_unsat_implies_all_pair_contradictions
    guardedMasterDecomposition_unsat_certified

/-- Certified terminal result for this branch: a `(4,5)`-free coloring of
`K_25` has no vertex of red degree exactly eight. -/
theorem no_root_has_redDegree_eight_certified
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∀ root, root < 25 →
      (colorNeighbors coloring root false).length ≠ 8 :=
  no_root_has_redDegree_eight hfree
    allAdmissibleDegreeEightPairsContradictory_certified

#print axioms guardedMasterCover_unsat
#print axioms guardedMasterFormula_eq_decomposition
#print axioms guardedMasterDecomposition_unsat_certified
#print axioms allAdmissibleDegreeEightPairsContradictory_certified
#print axioms no_root_has_redDegree_eight_certified

end LRATCatcher.Tests.R45DegreeEightGuardedMaster
