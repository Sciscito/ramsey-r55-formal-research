import LRATCatcher.Reflect
import LRATCatcher.Tests.R55TypedUnitsBridge

/-!
  Exact source bridge for the certified hard `d=20, c=10, type=312` W5
  leaf.  The external formula contains the Ramsey clauses, rooted degree
  counters, internal-regularity counters, two symmetry-breaking blocks, and
  the 106 canonical/type units.

  This module only identifies the exact clause intervals.  It deliberately
  does not claim that the strengthening blocks follow from an arbitrary
  Ramsey-free coloring.
-/

namespace LRATCatcher.Tests.R55.HardLeaf

open Std.Sat

/- Keep the 116 MB W5 replay independent of the type-0 replay while this
semantic bridge is developed. -/
lrat_reflect r55_d20_c10_t312_w5_bridge_unsat
  "../../r55/hard_d20_c10_t312_reglex_w5.cnf"
  "../../r55/hard_t312_reglex_w5.lrat"

/-- Recover the formula appearing in an UNSAT theorem without parsing a
second copy of the external file. -/
def certifiedFormulaOfUnsat {formula : CNF Nat} (_ : formula.Unsat) : CNF Nat :=
  formula

/-- Exact parsed contents of the certified hard W5 DIMACS file. -/
def hardD20C10T312W5Formula : CNF Nat :=
  certifiedFormulaOfUnsat r55_d20_c10_t312_w5_bridge_unsat

theorem hardD20C10T312W5Formula_unsat : hardD20C10T312W5Formula.Unsat := by
  exact r55_d20_c10_t312_w5_bridge_unsat

/-! Exact zero-based clause layout emitted by `ramsey.py`. -/

def ramseyClauseCount : Nat := 1925196
def rootedDegreeClauseCount : Nat := 116928
def internalRegularityClauseCount : Nat := 5818
def signatureLexClauseCount : Nat := 1442
def w5SymmetryClauseCount : Nat := 247
def rootUnitCount : Nat := 42
def anchorUnitCount : Nat := 19
def typeUnitCount : Nat := 45

private def blockStartAfterRooted : Nat :=
  ramseyClauseCount + rootedDegreeClauseCount

private def blockStartAfterRegularity : Nat :=
  blockStartAfterRooted + internalRegularityClauseCount

private def blockStartAfterSignatureLex : Nat :=
  blockStartAfterRegularity + signatureLexClauseCount

def rootedDegreeClauses : Array (CNF.Clause Nat) :=
  hardD20C10T312W5Formula.clauses.extract ramseyClauseCount
    blockStartAfterRooted

def internalRegularityClauses : Array (CNF.Clause Nat) :=
  hardD20C10T312W5Formula.clauses.extract blockStartAfterRooted
    blockStartAfterRegularity

def signatureLexClauses : Array (CNF.Clause Nat) :=
  hardD20C10T312W5Formula.clauses.extract blockStartAfterRegularity
    blockStartAfterSignatureLex

def w5SymmetryClauses : Array (CNF.Clause Nat) :=
  hardD20C10T312W5Formula.clauses.extract blockStartAfterSignatureLex
    (blockStartAfterSignatureLex + w5SymmetryClauseCount)

theorem hardD20C10T312W5Formula_numClauses :
    hardD20C10T312W5Formula.clauses.size = 2049737 := by
  native_decide

theorem hardD20C10T312W5Formula_numLiterals :
    hardD20C10T312W5Formula.numLiterals = 63080 := by
  native_decide

#print axioms hardD20C10T312W5Formula_unsat

end LRATCatcher.Tests.R55.HardLeaf
