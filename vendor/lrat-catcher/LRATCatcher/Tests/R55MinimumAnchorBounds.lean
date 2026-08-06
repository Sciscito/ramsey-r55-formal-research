import LRATCatcher.Tests.R55MinimumBlockWitness

/-!
  Semantic bridge from the minimum-anchor WLOG condition to the nineteen
  `<= 9` counter bounds used by the exact 5,149-clause block.

  In the canonical branch, vertex `0` has red neighbourhood `{1,...,20}` and
  vertex `1` is the anchor.  The anchor units give it exactly ten red
  neighbours inside that set.  If the anchor has minimum internal red degree,
  every vertex `2,...,20` has at least ten red and therefore at most nine blue
  incident edges inside the twenty-vertex side.
-/

namespace LRATCatcher.Tests.R55.MinLeaf.MinimumAnchor

open Std.Sat
open LRATCatcher.Ramsey
open CanonicalUnits
open MinimumCounter
open MinimumBlock

/-- Values of the nineteen edges from one canonical side vertex to all other
vertices of `{1,...,20}`, in the exact order used by the SAT counters. -/
def internalEdgeValues (coloring : Nat -> Bool) (vertex position : Nat) : Bool :=
  let other := (internalOthers vertex).getD position 0
  coloring (if vertex < other then edgeVar 43 vertex other
    else edgeVar 43 other vertex)

def redCount (values : Nat -> Bool) (stop : Nat) : Nat :=
  (List.range stop).countP values

def canonicalInternalRedDegree (coloring : Nat -> Bool) (vertex : Nat) : Nat :=
  redCount (internalEdgeValues coloring vertex) 19

/-- The precise extra WLOG hypothesis needed by the minimum-anchor leaf. -/
def CanonicalAnchorIsMinimum (coloring : Nat -> Bool) : Prop :=
  ∀ vertex, vertex ∈ sideVertices ->
    canonicalInternalRedDegree coloring 1 <=
      canonicalInternalRedDegree coloring vertex

/-- Canonical root/anchor units plus the explicit minimum-anchor condition.
The units imply that the anchor degree is ten; it is not assumed separately. -/
structure CanonicalMinimumAnchorWitness (coloring : Nat -> Bool) : Prop where
  canonical : CanonicalD20C10Units coloring
  anchor_minimum : CanonicalAnchorIsMinimum coloring

theorem redCount_add_falseCount (values : Nat -> Bool) (stop : Nat) :
    redCount values stop + falseCount values stop = stop := by
  have hpartition := List.length_eq_countP_add_countP
    (l := List.range stop) (fun index => values index)
  simpa [redCount, falseCount] using hpartition.symm

@[simp] theorem internalEdgeValues_counter (coloring : Nat -> Bool)
    (counter : Nat) :
    internalEdgeValues coloring (counter + 2) = counterValues coloring counter := by
  funext position
  rfl

set_option maxRecDepth 1000000 in
theorem internalOthers_one_lookup_checked :
    ∀ position : Fin 19,
      (internalOthers 1).getD position.val 0 = position.val + 2 := by
  native_decide

/-- The nineteen anchor units say exactly: positions `0,...,9` are red and
positions `10,...,18` are blue. -/
theorem internalEdgeValues_anchor_eq (coloring : Nat -> Bool)
    (canonical : CanonicalD20C10Units coloring)
    (position : Nat) (hposition : position < 19) :
    internalEdgeValues coloring 1 position = decide (position < 10) := by
  have hlookup :
      (internalOthers 1).getD position 0 = position + 2 := by
    simpa using internalOthers_one_lookup_checked ⟨position, hposition⟩
  unfold internalEdgeValues
  rw [hlookup]
  dsimp only
  have hordered : 1 < position + 2 := by omega
  rw [if_pos hordered]
  have hunit := canonical.anchor_unit (position + 2) (by omega) (by omega)
  by_cases hred : position < 10
  · have hpositive : position + 2 <= 11 := by omega
    have hvalue : coloring (edgeVar 43 1 (position + 2)) = true :=
      (positiveEdgeUnit_iff coloring 43 1 (position + 2)).mp
        (by simpa [canonicalAnchorUnit, hpositive] using hunit)
    simp [hred, hvalue]
  · have hnegative : ¬ position + 2 <= 11 := by omega
    have hvalue : coloring (edgeVar 43 1 (position + 2)) = false :=
      (negativeEdgeUnit_iff coloring 43 1 (position + 2)).mp
        (by simpa [canonicalAnchorUnit, hnegative] using hunit)
    simp [hred, hvalue]

/-- The value ten is derived from the canonical unit semantics. -/
theorem canonicalInternalRedDegree_anchor_eq_ten (coloring : Nat -> Bool)
    (canonical : CanonicalD20C10Units coloring) :
    canonicalInternalRedDegree coloring 1 = 10 := by
  unfold canonicalInternalRedDegree redCount
  calc
    (List.range 19).countP (internalEdgeValues coloring 1) =
        (List.range 19).countP (fun position => decide (position < 10)) := by
      apply List.countP_congr
      intro position hposition
      have hposition' := List.mem_range.mp hposition
      rw [internalEdgeValues_anchor_eq coloring canonical position hposition']
    _ = 10 := by decide

/-- Minimum internal red degree ten is exactly the collection of nineteen
blue-degree bounds consumed by the counter witness theorem. -/
theorem minimumInternalDegreeBounds_of_canonicalMinimum
    (coloring : Nat -> Bool)
    (witness : CanonicalMinimumAnchorWitness coloring) :
    MinimumInternalDegreeBounds coloring := by
  intro counter hcounter
  have hvertex : counter + 2 ∈ sideVertices := by
    apply List.mem_range'.mpr
    exact ⟨counter + 1, by omega, by omega⟩
  have hminimum := witness.anchor_minimum (counter + 2) hvertex
  rw [canonicalInternalRedDegree_anchor_eq_ten coloring witness.canonical,
    canonicalInternalRedDegree, internalEdgeValues_counter] at hminimum
  have hpartition := redCount_add_falseCount
    (counterValues coloring counter) 19
  omega

/-- End-to-end constructive endpoint for the exact external block. -/
theorem minimumInternalDegreeCNF_satisfied_of_canonicalMinimum
    (coloring : Nat -> Bool)
    (witness : CanonicalMinimumAnchorWitness coloring) :
    CNF.eval (minimumExtension coloring) minimumInternalDegreeCNF = true :=
  minimumInternalDegreeCNF_satisfied_of_bounds coloring
    (minimumInternalDegreeBounds_of_canonicalMinimum coloring witness)

#print axioms minimumInternalDegreeBounds_of_canonicalMinimum
#print axioms minimumInternalDegreeCNF_satisfied_of_canonicalMinimum

end LRATCatcher.Tests.R55.MinLeaf.MinimumAnchor
