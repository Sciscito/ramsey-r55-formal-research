import LRATCatcher.Tests.R55MinimumCounterSoundness

/-!
  Exact relabelling of nineteen abstract `<= 9` counters onto the 5,149
  clauses extracted from `min_d20_c10.cnf`.

  Counter `c` belongs to root-neighbour vertex `c+2`; its nineteen primaries
  are the red edge variables from that vertex to all other vertices in
  `{1,...,20}`.  Its 135 auxiliaries occupy one disjoint interval beginning at
  zero-based variable 59619 (DIMACS 59620).
-/

namespace LRATCatcher.Tests.R55.MinLeaf.MinimumBlock

open Std.Sat
open LRATCatcher.Ramsey
open MinimumCounter

def sideVertices : List Nat := List.range' 1 20

def internalOthers (vertex : Nat) : List Nat :=
  sideVertices.filter fun other => other != vertex

def auxiliaryRowOffset (index : Nat) : Nat :=
  (List.range index).foldl
    (fun total row => total + Nat.min 9 (row + 1)) 0

def counterAuxVariable (counter index threshold : Nat) : Nat :=
  59619 + counter * 135 + auxiliaryRowOffset index + (threshold - 1)

def counterRelabel (counter : Nat) : SeqVariable -> Nat
  | .inl position =>
      let vertex := counter + 2
      let other := (internalOthers vertex).getD position 0
      if vertex < other then edgeVar 43 vertex other else edgeVar 43 other vertex
  | .inr (index, threshold) =>
      counterAuxVariable counter index threshold

def relabelledCounter (counter : Nat) : CNF Nat :=
  CNF.relabel (counterRelabel counter) (sequentialAtMostNine 19)

def generatedMinimumInternalDegreeCNF : CNF Nat :=
  (List.range 19).foldl (fun formula counter =>
    formula ++ relabelledCounter counter) CNF.empty

set_option maxRecDepth 1000000 in
theorem auxiliaryRowOffset_nineteen : auxiliaryRowOffset 19 = 135 := by
  decide

set_option maxRecDepth 1000000 in
theorem sequentialAtMostNine_nineteen_numClauses :
    (sequentialAtMostNine 19).clauses.size = 271 := by
  decide

set_option maxRecDepth 1000000 in
theorem generatedMinimumInternalDegreeCNF_numClauses :
    generatedMinimumInternalDegreeCNF.clauses.size = 5149 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Exact bridge to clauses `[2042124,2047273)` of the certified external
formula.  This checks clause order, literal polarity, edge numbering,
auxiliary allocation, and all nineteen counter boundaries. -/
theorem generatedMinimumInternalDegreeCNF_eq_external :
    generatedMinimumInternalDegreeCNF = minimumInternalDegreeCNF := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

#print axioms generatedMinimumInternalDegreeCNF_eq_external

end LRATCatcher.Tests.R55.MinLeaf.MinimumBlock
