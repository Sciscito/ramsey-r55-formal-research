import LRATCatcher.Reflect
import LRATCatcher.Tests.R55TypedUnitsBridge

/-!
  A semantic bridge to the certified `d=20, c=10, type=0` minimum-anchor
  leaf.  The LRAT theorem certifies the external DIMACS formula; this file
  gives that formula a reusable Lean name and separates its two auxiliary
  counter blocks from the Ramsey clauses and the 106 canonical/type units.

  Crucially, the counter blocks are not claimed to follow merely from
  Ramsey-freeness.  Their satisfaction remains an explicit hypothesis until
  the degree-window and minimum-internal-degree encodings are proved sound.
-/

namespace LRATCatcher.Tests.R55

open Std.Sat
open LRATCatcher.Ramsey
open CanonicalUnits
open TypedUnits

namespace MinLeaf

/- Dedicated replay of the type-0 certificate.  Keeping this leaf separate
from `R55Branch` avoids also replaying the unrelated 116 MB type-312 proof
when developing the semantic bridge. -/
lrat_reflect r55_d20_c10_t0_min_bridge_unsat
  "../../r55/min_d20_c10.cnf"
  "../../r55/min_d20_c10_t0.lrat"

/-- Recover the exact formula occurring in an UNSAT theorem. -/
def certifiedFormulaOfUnsat {formula : CNF Nat} (_ : formula.Unsat) : CNF Nat :=
  formula

/-- The exact parsed contents of `r55/min_d20_c10.cnf`, recovered from the
statement of the already checked LRAT theorem without reading the file again. -/
def minD20C10T0Formula : CNF Nat :=
  certifiedFormulaOfUnsat r55_d20_c10_t0_min_bridge_unsat

theorem minD20C10T0Formula_unsat : minD20C10T0Formula.Unsat := by
  exact r55_d20_c10_t0_min_bridge_unsat

/-! Exact clause-layout constants emitted by `ramsey.py` for this leaf. -/

def ramseyClauseCount : Nat := 1925196
def rootedDegreeClauseCount : Nat := 116928
def minimumInternalDegreeClauseCount : Nat := 5149
def rootUnitCount : Nat := 42
def anchorUnitCount : Nat := 19
def typeUnitCount : Nat := 45

def rootedDegreeClauses : Array (CNF.Clause Nat) :=
  minD20C10T0Formula.clauses.extract ramseyClauseCount
    (ramseyClauseCount + rootedDegreeClauseCount)

def minimumInternalDegreeClauses : Array (CNF.Clause Nat) :=
  minD20C10T0Formula.clauses.extract
    (ramseyClauseCount + rootedDegreeClauseCount)
    (ramseyClauseCount + rootedDegreeClauseCount + minimumInternalDegreeClauseCount)

def unitClauses (units : List Int) : Array (CNF.Clause Nat) :=
  (units.map fun literal => [LRATCatcher.dimacsLit literal]).toArray

/-- Red then blue clauses over Lean's reversed-subset enumeration.  The exact
Python `itertools.combinations` order is defined and checked separately in
`R55MinLeafSemantics`. -/
def interleavedRamseyEncode (n k : Nat) : CNF Nat :=
  { clauses := ((subsets n k).flatMap fun vertices =>
      [redClause n vertices.reverse, blueClause n vertices.reverse]).toArray }

theorem minD20C10T0Formula_numClauses :
    minD20C10T0Formula.clauses.size = 2047379 := by
  native_decide

theorem minD20C10T0Formula_numLiterals :
    minD20C10T0Formula.numLiterals = 62184 := by
  native_decide

end MinLeaf

end LRATCatcher.Tests.R55
