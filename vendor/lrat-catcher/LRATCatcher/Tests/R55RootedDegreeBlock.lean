import LRATCatcher.Tests.R55SequentialCounterGeneric
import LRATCatcher.Tests.R55MinimumBlockWitness

/-!
  Exact constructive semantics of the 116,928-clause rooted degree-window
  block in `r55/min_d20_c10.cnf`.

  Python emits two length-41 sequential counters for every vertex `1..42`,
  red then blue.  Vertices `1..20` are fixed red neighbours of the root, so
  their non-root red/blue bounds are `23/24`; vertices `21..42` use `24/23`.
  The 58,716 auxiliaries occupy exactly Lean variables `903..59618`.
-/

namespace LRATCatcher.Tests.R55.MinLeaf.RootedDegreeBlock

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55.SequentialCounter

def rootedVertices : List Nat := List.range' 1 42

def rootedOthers (vertex : Nat) : List Nat :=
  rootedVertices.filter fun other => other != vertex

def counterVertex (counter : Nat) : Nat := counter / 2 + 1

def redBound (vertex : Nat) : Nat := if vertex <= 20 then 23 else 24

def blueBound (vertex : Nat) : Nat := if vertex <= 20 then 24 else 23

def counterBound (counter : Nat) : Nat :=
  if counter % 2 = 0 then redBound (counterVertex counter)
  else blueBound (counterVertex counter)

/- The clause polarity guarding an inactive primary.  `false` is the red
counter and `true` is the blue counter. -/
def counterGuard (counter : Nat) : Bool := counter % 2 != 0

def auxiliaryPairs (bound : Nat) : List (Prod Nat Nat) :=
  (List.range 41).flatMap fun index =>
    (List.range' 1 (Nat.min bound (index + 1))).map fun threshold =>
      (index, threshold)

def auxiliaryCount (bound : Nat) : Nat := (auxiliaryPairs bound).length

def auxiliaryRowOffset (bound index : Nat) : Nat :=
  (List.range index).foldl
    (fun total row => total + Nat.min bound (row + 1)) 0

def counterBase (counter : Nat) : Nat :=
  903 + (counter / 2) * 1398 +
    if counter % 2 = 0 then 0 else redBound (counterVertex counter) |> auxiliaryCount

def counterAuxVariable (counter index threshold : Nat) : Nat :=
  counterBase counter + auxiliaryRowOffset (counterBound counter) index +
    (threshold - 1)

def counterRelabel (counter : Nat) : SeqVariable -> Nat
  | .inl position =>
      let vertex := counterVertex counter
      let other := (rootedOthers vertex).getD position 0
      if vertex < other then edgeVar 43 vertex other else edgeVar 43 other vertex
  | .inr (index, threshold) =>
      counterAuxVariable counter index threshold

def counterValues (coloring : Nat -> Bool) (counter position : Nat) : Bool :=
  coloring (counterRelabel counter (.inl position))

def relabelledCounter (counter : Nat) : CNF Nat :=
  CNF.relabel (counterRelabel counter)
    (sequentialAtMost 41 (counterBound counter) (counterGuard counter))

def generatedRootedDegreeCNF : CNF Nat :=
  (List.range 84).foldl
    (fun formula counter => formula ++ relabelledCounter counter) CNF.empty

set_option maxRecDepth 1000000 in
theorem auxiliaryCount_twentyThree : auxiliaryCount 23 = 690 := by
  decide

set_option maxRecDepth 1000000 in
theorem auxiliaryCount_twentyFour : auxiliaryCount 24 = 708 := by
  decide

set_option maxRecDepth 1000000 in
theorem generatedRootedDegreeCNF_numClauses :
    generatedRootedDegreeCNF.clauses.size = 116928 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/- Exact audit against clauses `[1925196,2042124)` extracted from the
LRAT-certified external formula. -/
theorem generatedRootedDegreeCNF_eq_external :
    generatedRootedDegreeCNF = rootedDegreeCNF := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

#print axioms generatedRootedDegreeCNF_eq_external

end LRATCatcher.Tests.R55.MinLeaf.RootedDegreeBlock
