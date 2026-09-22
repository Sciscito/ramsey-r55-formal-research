import LRATCatcher.Tests.R44OrderTwelveTwoCenterCases

/-!
  # Full degree-seven two-centre normalization

  This module is deliberately parameterized by a low-degree centre witness.
  The witness can be supplied by
  `R44Cover6DegreeSevenMinCenter.degreeSeven_has_internal_degree_one_or_two`
  once that module is built.  Keeping this file independent avoids rerunning
  its 21-bit finite check while developing the purely structural transport.
-/

namespace LRATCatcher.Tests.R44Cover6DegreeSevenNormalization

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44OrderTwelveDegreeBounds
open LRATCatcher.Tests.R44OrderTwelveTwoCenterCases

abbrev Vertex := Fin 12

/-! ## Exact root sort at degree seven -/

theorem d7SortedNonRoot_exact_seven (pattern : RootPattern)
    (hdegree : (List.finRange 11).countP (patternColor pattern) = 7)
    (position : Fin 11) :
    patternColor pattern
        ((sortedNonRoot pattern).getD position.val 0) =
      decide (position.val < 7) := by
  native_decide +revert

theorem d7RootSort_exact_seven (coloring : Nat -> Bool)
    (hdegree : positiveRootDegree coloring = 7)
    (position : Fin 11) :
    coloringEdge 12 (rootSortedColoring coloring)
        0 (position.val + 1) = decide (position.val < 7) := by
  have hcount :
      (List.finRange 11).countP (patternColor (rootPattern coloring)) = 7 := by
    rw [rootPattern_count_eq_positiveRootDegree, hdegree]
  have hsorted := d7SortedNonRoot_exact_seven
    (rootPattern coloring) hcount position
  rw [patternColor_rootPattern coloring
    ((sortedNonRoot (rootPattern coloring)).getD position.val 0)] at hsorted
  have hedge := coloringEdge_permuteColoring
    (rootSortPermutation coloring) coloring (0 : Vertex)
      ⟨position.val + 1, by omega⟩
  rw [rootSortPermutation_zero,
    rootSortPermutation_nonRoot_val coloring position] at hedge
  exact (by simpa [rootSortedColoring] using hedge.trans hsorted)

/-! ## Moving a selected positive neighbour to label one -/

def d7RemainingPositive (center : Fin 7) : List (Fin 7) :=
  (List.finRange 7).filter fun vertex => decide (vertex ≠ center)

theorem d7RemainingPositive_length (center : Fin 7) :
    (d7RemainingPositive center).length = 6 := by
  native_decide +revert

def d7CenterMoveLabels (center : Fin 7) : List Nat :=
  [0, center.val + 1] ++
    (d7RemainingPositive center).map (fun vertex => vertex.val + 1) ++
    [8, 9, 10, 11]

theorem d7CenterMoveLabels_isPermutation (center : Fin 7) :
    isPermutation (d7CenterMoveLabels center) 12 = true := by
  native_decide +revert

noncomputable def d7CenterMovePermutation
    (center : Fin 7) : FinPermutation 12 :=
  listPermutationToFin (d7CenterMoveLabels center) 12
    (d7CenterMoveLabels_isPermutation center)

@[simp] theorem d7CenterMovePermutation_zero (center : Fin 7) :
    d7CenterMovePermutation center (0 : Vertex) = 0 := by
  apply Fin.ext
  rw [d7CenterMovePermutation, listPermutationToFin_apply_val]
  simp [d7CenterMoveLabels]

@[simp] theorem d7CenterMovePermutation_one (center : Fin 7) :
    (d7CenterMovePermutation center (1 : Vertex)).val = center.val + 1 := by
  rw [d7CenterMovePermutation, listPermutationToFin_apply_val]
  simp [d7CenterMoveLabels]

theorem d7CenterMovePermutation_left_val
    (center : Fin 7) (position : Fin 6) :
    (d7CenterMovePermutation center ⟨position.val + 2, by omega⟩).val =
      ((d7RemainingPositive center).getD position.val 0).val + 1 := by
  rw [d7CenterMovePermutation, listPermutationToFin_apply_val]
  native_decide +revert

theorem d7CenterMovePermutation_left_bounds
    (center : Fin 7) (position : Fin 6) :
    1 ≤ (d7CenterMovePermutation center
      ⟨position.val + 2, by omega⟩).val ∧
      (d7CenterMovePermutation center
        ⟨position.val + 2, by omega⟩).val ≤ 7 := by
  rw [d7CenterMovePermutation_left_val]
  native_decide +revert

theorem d7CenterMovePermutation_right_val
    (center : Fin 7) (position : Fin 4) :
    (d7CenterMovePermutation center ⟨position.val + 8, by omega⟩).val =
      position.val + 8 := by
  rw [d7CenterMovePermutation, listPermutationToFin_apply_val]
  native_decide +revert

noncomputable def d7CenterMovedColoring
    (coloring : Nat -> Bool) (center : Fin 7) : Nat -> Bool :=
  permuteColoring (d7CenterMovePermutation center)
    (rootSortedColoring coloring)

theorem d7CenterMoved_root_center
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) :
    coloringEdge 12 (d7CenterMovedColoring coloring center) 0 1 = true := by
  have hedge := coloringEdge_permuteColoring
    (d7CenterMovePermutation center) (rootSortedColoring coloring)
    (0 : Vertex) (1 : Vertex)
  rw [d7CenterMovePermutation_zero, d7CenterMovePermutation_one] at hedge
  have hroot := d7RootSort_exact_seven coloring hdegree
    (show Fin 11 from ⟨center.val, by omega⟩)
  have hlt : center.val < 7 := center.isLt
  have htrue : decide (center.val < 7) = true := by simp [hlt]
  rw [htrue] at hroot
  unfold d7CenterMovedColoring
  exact (by simpa only [Fin.val_mk] using hedge.trans hroot)

theorem d7CenterMoved_root_left
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) (position : Fin 6) :
    coloringEdge 12 (d7CenterMovedColoring coloring center)
      0 (position.val + 2) = true := by
  let target : Vertex := ⟨position.val + 2, by omega⟩
  let oldVertex := d7CenterMovePermutation center target
  have hbounds := d7CenterMovePermutation_left_bounds center position
  have holdPositive : oldVertex.val - 1 < 7 := by
    dsimp [oldVertex, target]
    omega
  let oldPosition : Fin 11 := ⟨oldVertex.val - 1, by
    dsimp [oldVertex, target]
    omega⟩
  have hroot := d7RootSort_exact_seven coloring hdegree oldPosition
  have holdLower : 1 ≤ oldVertex.val := by
    simpa [oldVertex, target] using hbounds.1
  have holdPosition : oldPosition.val < 7 := by
    change oldVertex.val - 1 < 7
    exact holdPositive
  have htrue : decide (oldPosition.val < 7) = true := by
    simp [holdPosition]
  rw [htrue] at hroot
  have hvertex : oldPosition.val + 1 = oldVertex.val := by
    dsimp [oldPosition]
    omega
  rw [hvertex] at hroot
  have hedge := coloringEdge_permuteColoring
    (d7CenterMovePermutation center) (rootSortedColoring coloring)
    (0 : Vertex) target
  rw [d7CenterMovePermutation_zero] at hedge
  unfold d7CenterMovedColoring
  exact (by simpa [target, oldVertex] using hedge.trans hroot)

theorem d7CenterMoved_root_right
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) (position : Fin 4) :
    coloringEdge 12 (d7CenterMovedColoring coloring center)
      0 (position.val + 8) = false := by
  have hedge := coloringEdge_permuteColoring
    (d7CenterMovePermutation center) (rootSortedColoring coloring)
    (0 : Vertex) ⟨position.val + 8, by omega⟩
  rw [d7CenterMovePermutation_zero,
    d7CenterMovePermutation_right_val center position] at hedge
  let oldPosition : Fin 11 := ⟨position.val + 7, by omega⟩
  have hroot := d7RootSort_exact_seven coloring hdegree oldPosition
  have hnot : ¬ oldPosition.val < 7 := by
    dsimp [oldPosition]
    omega
  have hfalse : decide (oldPosition.val < 7) = false := by simp [hnot]
  rw [hfalse] at hroot
  unfold d7CenterMovedColoring
  exact (by simpa [oldPosition] using hedge.trans hroot)

theorem d7CenterMoved_center_left
    (coloring : Nat -> Bool) (center : Fin 7) (position : Fin 6) :
    coloringEdge 12 (d7CenterMovedColoring coloring center)
        1 (position.val + 2) =
      coloringEdge 12 (rootSortedColoring coloring)
        (center.val + 1)
        (((d7RemainingPositive center).getD position.val 0).val + 1) := by
  have hedge := coloringEdge_permuteColoring
    (d7CenterMovePermutation center) (rootSortedColoring coloring)
    (1 : Vertex) ⟨position.val + 2, by omega⟩
  rw [d7CenterMovePermutation_one,
    d7CenterMovePermutation_left_val center position] at hedge
  unfold d7CenterMovedColoring
  simpa only [Fin.val_mk] using hedge

noncomputable def d7NormalizedInternalDegree
    (coloring : Nat -> Bool) (center : Fin 7) : Nat :=
  (List.finRange 7).countP fun other =>
    decide (other ≠ center) &&
      coloringEdge 12 (rootSortedColoring coloring)
        (center.val + 1) (other.val + 1)

noncomputable def d7CenterLeftCount
    (coloring : Nat -> Bool) (center : Fin 7) : Nat :=
  (List.finRange 6).countP fun position =>
    coloringEdge 12 (d7CenterMovedColoring coloring center)
      1 (position.val + 2)

theorem d7RemainingPositive_lookup_list (center : Fin 7) :
    (List.finRange 6).map
      (fun position => (d7RemainingPositive center).getD position.val 0) =
    d7RemainingPositive center := by
  native_decide +revert

theorem d7CenterLeftCount_eq_internalDegree
    (coloring : Nat -> Bool) (center : Fin 7) :
    d7CenterLeftCount coloring center =
      d7NormalizedInternalDegree coloring center := by
  let edgeAt : Fin 7 -> Bool := fun other =>
    coloringEdge 12 (rootSortedColoring coloring)
      (center.val + 1) (other.val + 1)
  calc
    d7CenterLeftCount coloring center =
        (List.finRange 6).countP (fun position =>
          edgeAt ((d7RemainingPositive center).getD position.val 0)) := by
      unfold d7CenterLeftCount
      apply List.countP_congr
      intro position _hposition
      rw [d7CenterMoved_center_left coloring center position]
    _ = (d7RemainingPositive center).countP edgeAt := by
      rw [← d7RemainingPositive_lookup_list center, List.countP_map]
      rfl
    _ = d7NormalizedInternalDegree coloring center := by
      unfold d7RemainingPositive d7NormalizedInternalDegree
      rw [List.countP_filter]
      apply List.countP_congr
      intro other _hother
      simp only [edgeAt]
      rw [Bool.and_comm]

theorem d7CenterMoved_isRamseyFree_iff
    (coloring : Nat -> Bool) (center : Fin 7) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4 (d7CenterMovedColoring coloring center) := by
  rw [d7CenterMovedColoring]
  exact (rootSort_isRamseyFree_iff coloring).trans
    (isRamseyFree_permute_iff
      (d7CenterMovePermutation center) (rootSortedColoring coloring))

theorem d7CenterMoved_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat -> Bool) (center : Fin 7)
    (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (d7CenterMovedColoring coloring center) motif := by
  rw [d7CenterMovedColoring]
  exact (inducedMotifOccurrence_permute_iff
    (rootSortPermutation coloring) coloring motif).trans
    (inducedMotifOccurrence_permute_iff
      (d7CenterMovePermutation center) (rootSortedColoring coloring) motif)

/-! ## Independent second-centre sort on blocks of sizes six and four -/

abbrev D7SecondPattern := BitVec 10

def d7SecondPatternColor
    (pattern : D7SecondPattern) (position : Fin 10) : Bool :=
  pattern.getLsbD position.val

def d7LeftPatternColor
    (pattern : D7SecondPattern) (position : Fin 6) : Bool :=
  d7SecondPatternColor pattern ⟨position.val, by omega⟩

def d7RightPatternColor
    (pattern : D7SecondPattern) (position : Fin 4) : Bool :=
  d7SecondPatternColor pattern ⟨position.val + 6, by omega⟩

def d7SortedLeft (pattern : D7SecondPattern) : List (Fin 6) :=
  (List.finRange 6).filter (d7LeftPatternColor pattern) ++
    (List.finRange 6).filter
      (fun position => !(d7LeftPatternColor pattern position))

def d7SortedRight (pattern : D7SecondPattern) : List (Fin 4) :=
  (List.finRange 4).filter (d7RightPatternColor pattern) ++
    (List.finRange 4).filter
      (fun position => !(d7RightPatternColor pattern position))

def d7SecondSortedLabels (pattern : D7SecondPattern) : List Nat :=
  [0, 1] ++
    (d7SortedLeft pattern).map (fun position => position.val + 2) ++
    (d7SortedRight pattern).map (fun position => position.val + 8)

def d7LeftCount (pattern : D7SecondPattern) : Nat :=
  (List.finRange 6).countP (d7LeftPatternColor pattern)

def d7RightCount (pattern : D7SecondPattern) : Nat :=
  (List.finRange 4).countP (d7RightPatternColor pattern)

theorem d7LeftCount_le_six (pattern : D7SecondPattern) :
    d7LeftCount pattern ≤ 6 := by
  native_decide +revert

theorem d7RightCount_le_four (pattern : D7SecondPattern) :
    d7RightCount pattern ≤ 4 := by
  native_decide +revert

theorem d7SecondSortedLabels_isPermutation (pattern : D7SecondPattern) :
    isPermutation (d7SecondSortedLabels pattern) 12 = true := by
  native_decide +revert

theorem d7SortedLeft_color
    (pattern : D7SecondPattern) (position : Fin 6) :
    d7LeftPatternColor pattern
        ((d7SortedLeft pattern).getD position.val 0) =
      decide (position.val < d7LeftCount pattern) := by
  native_decide +revert

theorem d7SortedRight_color
    (pattern : D7SecondPattern) (position : Fin 4) :
    d7RightPatternColor pattern
        ((d7SortedRight pattern).getD position.val 0) =
      decide (position.val < d7RightCount pattern) := by
  native_decide +revert

theorem d7SecondSortedLabels_getD_left
    (pattern : D7SecondPattern) (position : Fin 6) :
    (d7SecondSortedLabels pattern).getD (position.val + 2) 12 =
      ((d7SortedLeft pattern).getD position.val 0).val + 2 := by
  native_decide +revert

theorem d7SecondSortedLabels_getD_right
    (pattern : D7SecondPattern) (position : Fin 4) :
    (d7SecondSortedLabels pattern).getD (position.val + 8) 12 =
      ((d7SortedRight pattern).getD position.val 0).val + 8 := by
  native_decide +revert

noncomputable def d7SecondSortPermutationForPattern
    (pattern : D7SecondPattern) : FinPermutation 12 :=
  listPermutationToFin (d7SecondSortedLabels pattern) 12
    (d7SecondSortedLabels_isPermutation pattern)

@[simp] theorem d7SecondSortPermutationForPattern_zero
    (pattern : D7SecondPattern) :
    d7SecondSortPermutationForPattern pattern (0 : Vertex) = 0 := by
  apply Fin.ext
  rw [d7SecondSortPermutationForPattern, listPermutationToFin_apply_val]
  simp [d7SecondSortedLabels]

@[simp] theorem d7SecondSortPermutationForPattern_one
    (pattern : D7SecondPattern) :
    d7SecondSortPermutationForPattern pattern (1 : Vertex) = 1 := by
  apply Fin.ext
  rw [d7SecondSortPermutationForPattern, listPermutationToFin_apply_val]
  simp [d7SecondSortedLabels]

theorem d7SecondSortPermutationForPattern_left_val
    (pattern : D7SecondPattern) (position : Fin 6) :
    (d7SecondSortPermutationForPattern pattern
      ⟨position.val + 2, by omega⟩).val =
        ((d7SortedLeft pattern).getD position.val 0).val + 2 := by
  rw [d7SecondSortPermutationForPattern, listPermutationToFin_apply_val]
  exact d7SecondSortedLabels_getD_left pattern position

theorem d7SecondSortPermutationForPattern_right_val
    (pattern : D7SecondPattern) (position : Fin 4) :
    (d7SecondSortPermutationForPattern pattern
      ⟨position.val + 8, by omega⟩).val =
        ((d7SortedRight pattern).getD position.val 0).val + 8 := by
  rw [d7SecondSortPermutationForPattern, listPermutationToFin_apply_val]
  exact d7SecondSortedLabels_getD_right pattern position

def d7SecondPatternBits (coloring : Nat -> Bool) : List Bool :=
  List.ofFn fun position : Fin 10 =>
    coloringEdge 12 coloring 1 (position.val + 2)

def d7SecondPattern (coloring : Nat -> Bool) : D7SecondPattern :=
  BitVec.cast (by simp [d7SecondPatternBits])
    (BitVec.ofBoolListLE (d7SecondPatternBits coloring))

theorem d7LeftPatternColor_secondPattern
    (coloring : Nat -> Bool) (position : Fin 6) :
    d7LeftPatternColor (d7SecondPattern coloring) position =
      coloringEdge 12 coloring 1 (position.val + 2) := by
  unfold d7LeftPatternColor d7SecondPatternColor d7SecondPattern
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := d7SecondPatternBits coloring) (i := position.val)
    (h := by simp [d7SecondPatternBits]; omega) false]
  change
    (List.ofFn fun position : Fin 10 =>
      coloringEdge 12 coloring 1 (position.val + 2))[position.val]'(by
        simpa using (show position.val < 10 by omega)) = _
  rw [List.getElem_ofFn]

theorem d7RightPatternColor_secondPattern
    (coloring : Nat -> Bool) (position : Fin 4) :
    d7RightPatternColor (d7SecondPattern coloring) position =
      coloringEdge 12 coloring 1 (position.val + 8) := by
  unfold d7RightPatternColor d7SecondPatternColor d7SecondPattern
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := d7SecondPatternBits coloring) (i := position.val + 6)
    (h := by simp [d7SecondPatternBits]; omega) false]
  change
    (List.ofFn fun position : Fin 10 =>
      coloringEdge 12 coloring 1 (position.val + 2))[position.val + 6]'(by
        simp; omega) = _
  rw [List.getElem_ofFn]

noncomputable def d7SecondSortPermutation
    (coloring : Nat -> Bool) : FinPermutation 12 :=
  d7SecondSortPermutationForPattern (d7SecondPattern coloring)

@[simp] theorem d7SecondSortPermutation_zero (coloring : Nat -> Bool) :
    d7SecondSortPermutation coloring (0 : Vertex) = 0 :=
  d7SecondSortPermutationForPattern_zero (d7SecondPattern coloring)

@[simp] theorem d7SecondSortPermutation_one (coloring : Nat -> Bool) :
    d7SecondSortPermutation coloring (1 : Vertex) = 1 :=
  d7SecondSortPermutationForPattern_one (d7SecondPattern coloring)

def d7LeftCountOf (coloring : Nat -> Bool) : Nat :=
  d7LeftCount (d7SecondPattern coloring)

def d7RightCountOf (coloring : Nat -> Bool) : Nat :=
  d7RightCount (d7SecondPattern coloring)

theorem d7SecondSort_left_edge
    (coloring : Nat -> Bool) (position : Fin 6) :
    coloringEdge 12
        (permuteColoring (d7SecondSortPermutation coloring) coloring)
        1 (position.val + 2) =
      decide (position.val < d7LeftCountOf coloring) := by
  have hedge := coloringEdge_permuteColoring
    (d7SecondSortPermutation coloring) coloring (1 : Vertex)
      ⟨position.val + 2, by omega⟩
  unfold d7SecondSortPermutation at hedge
  rw [d7SecondSortPermutationForPattern_one,
    d7SecondSortPermutationForPattern_left_val
      (d7SecondPattern coloring) position] at hedge
  have hedge' : coloringEdge 12
      (permuteColoring
        (d7SecondSortPermutationForPattern (d7SecondPattern coloring))
        coloring) 1 (position.val + 2) =
      coloringEdge 12 coloring 1
        (((d7SortedLeft (d7SecondPattern coloring)).getD
          position.val 0).val + 2) := by
    simpa only [Fin.val_mk] using hedge
  unfold d7SecondSortPermutation
  rw [hedge']
  rw [← d7LeftPatternColor_secondPattern coloring
    ((d7SortedLeft (d7SecondPattern coloring)).getD position.val 0)]
  exact d7SortedLeft_color (d7SecondPattern coloring) position

theorem d7SecondSort_right_edge
    (coloring : Nat -> Bool) (position : Fin 4) :
    coloringEdge 12
        (permuteColoring (d7SecondSortPermutation coloring) coloring)
        1 (position.val + 8) =
      decide (position.val < d7RightCountOf coloring) := by
  have hedge := coloringEdge_permuteColoring
    (d7SecondSortPermutation coloring) coloring (1 : Vertex)
      ⟨position.val + 8, by omega⟩
  unfold d7SecondSortPermutation at hedge
  rw [d7SecondSortPermutationForPattern_one,
    d7SecondSortPermutationForPattern_right_val
      (d7SecondPattern coloring) position] at hedge
  have hedge' : coloringEdge 12
      (permuteColoring
        (d7SecondSortPermutationForPattern (d7SecondPattern coloring))
        coloring) 1 (position.val + 8) =
      coloringEdge 12 coloring 1
        (((d7SortedRight (d7SecondPattern coloring)).getD
          position.val 0).val + 8) := by
    simpa only [Fin.val_mk] using hedge
  unfold d7SecondSortPermutation
  rw [hedge']
  rw [← d7RightPatternColor_secondPattern coloring
    ((d7SortedRight (d7SecondPattern coloring)).getD position.val 0)]
  exact d7SortedRight_color (d7SecondPattern coloring) position

theorem d7SecondSort_isRamseyFree_iff (coloring : Nat -> Bool) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4
        (permuteColoring (d7SecondSortPermutation coloring) coloring) :=
  isRamseyFree_permute_iff (d7SecondSortPermutation coloring) coloring

theorem d7SecondSort_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat -> Bool) (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (permuteColoring (d7SecondSortPermutation coloring) coloring) motif :=
  inducedMotifOccurrence_permute_iff
    (d7SecondSortPermutation coloring) coloring motif

/-! ## The fully normalized coloring and its parameters -/

noncomputable def d7NormalizedColoring
    (coloring : Nat -> Bool) (center : Fin 7) : Nat -> Bool :=
  permuteColoring
    (d7SecondSortPermutation (d7CenterMovedColoring coloring center))
    (d7CenterMovedColoring coloring center)

noncomputable def d7PValue
    (coloring : Nat -> Bool) (center : Fin 7) : Nat :=
  d7LeftCountOf (d7CenterMovedColoring coloring center)

noncomputable def d7QValue
    (coloring : Nat -> Bool) (center : Fin 7) : Nat :=
  d7RightCountOf (d7CenterMovedColoring coloring center)

theorem d7LeftCountOf_semantic (coloring : Nat -> Bool) :
    d7LeftCountOf coloring =
      (List.finRange 6).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 2) := by
  unfold d7LeftCountOf d7LeftCount
  apply List.countP_congr
  intro position _hposition
  rw [d7LeftPatternColor_secondPattern coloring position]

theorem d7PValue_eq_internalDegree
    (coloring : Nat -> Bool) (center : Fin 7) :
    d7PValue coloring center = d7NormalizedInternalDegree coloring center := by
  unfold d7PValue
  rw [d7LeftCountOf_semantic]
  exact d7CenterLeftCount_eq_internalDegree coloring center

theorem d7QValue_le_four (coloring : Nat -> Bool) (center : Fin 7) :
    d7QValue coloring center ≤ 4 :=
  d7RightCount_le_four
    (d7SecondPattern (d7CenterMovedColoring coloring center))

theorem d7QValue_in_zero_to_four
    (coloring : Nat -> Bool) (center : Fin 7) :
    0 ≤ d7QValue coloring center ∧ d7QValue coloring center ≤ 4 :=
  ⟨Nat.zero_le _, d7QValue_le_four coloring center⟩

theorem d7Normalized_root_center
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) :
    coloringEdge 12 (d7NormalizedColoring coloring center) 0 1 = true := by
  have hedge := coloringEdge_permuteColoring
    (d7SecondSortPermutation (d7CenterMovedColoring coloring center))
    (d7CenterMovedColoring coloring center) (0 : Vertex) (1 : Vertex)
  rw [d7SecondSortPermutation_zero, d7SecondSortPermutation_one] at hedge
  unfold d7NormalizedColoring
  exact hedge.trans (d7CenterMoved_root_center coloring hdegree center)

theorem d7Normalized_root_left
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) (position : Fin 6) :
    coloringEdge 12 (d7NormalizedColoring coloring center)
      0 (position.val + 2) = true := by
  let source := d7CenterMovedColoring coloring center
  have hedge := coloringEdge_permuteColoring
    (d7SecondSortPermutation source) source (0 : Vertex)
      ⟨position.val + 2, by omega⟩
  unfold d7SecondSortPermutation at hedge
  rw [d7SecondSortPermutationForPattern_zero,
    d7SecondSortPermutationForPattern_left_val] at hedge
  have hsource := d7CenterMoved_root_left coloring hdegree center
    ((d7SortedLeft (d7SecondPattern source)).getD position.val 0)
  unfold d7NormalizedColoring
  exact (by simpa [source] using hedge.trans hsource)

theorem d7Normalized_root_right
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) (position : Fin 4) :
    coloringEdge 12 (d7NormalizedColoring coloring center)
      0 (position.val + 8) = false := by
  let source := d7CenterMovedColoring coloring center
  have hedge := coloringEdge_permuteColoring
    (d7SecondSortPermutation source) source (0 : Vertex)
      ⟨position.val + 8, by omega⟩
  unfold d7SecondSortPermutation at hedge
  rw [d7SecondSortPermutationForPattern_zero,
    d7SecondSortPermutationForPattern_right_val] at hedge
  have hsource := d7CenterMoved_root_right coloring hdegree center
    ((d7SortedRight (d7SecondPattern source)).getD position.val 0)
  unfold d7NormalizedColoring
  exact (by simpa [source] using hedge.trans hsource)

theorem d7Normalized_center_left
    (coloring : Nat -> Bool) (center : Fin 7) (position : Fin 6) :
    coloringEdge 12 (d7NormalizedColoring coloring center)
        1 (position.val + 2) =
      decide (position.val < d7PValue coloring center) := by
  exact d7SecondSort_left_edge
    (d7CenterMovedColoring coloring center) position

theorem d7Normalized_center_right
    (coloring : Nat -> Bool) (center : Fin 7) (position : Fin 4) :
    coloringEdge 12 (d7NormalizedColoring coloring center)
        1 (position.val + 8) =
      decide (position.val < d7QValue coloring center) := by
  exact d7SecondSort_right_edge
    (d7CenterMovedColoring coloring center) position

theorem d7Normalized_isRamseyFree_iff
    (coloring : Nat -> Bool) (center : Fin 7) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4 (d7NormalizedColoring coloring center) := by
  exact (d7CenterMoved_isRamseyFree_iff coloring center).trans
    (d7SecondSort_isRamseyFree_iff
      (d7CenterMovedColoring coloring center))

theorem d7Normalized_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat -> Bool) (center : Fin 7)
    (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (d7NormalizedColoring coloring center) motif := by
  exact (d7CenterMoved_inducedMotifOccurrence_iff
    coloring center motif).trans
    (d7SecondSort_inducedMotifOccurrence_iff
      (d7CenterMovedColoring coloring center) motif)

/-! ## Exact centre degree decomposition and the nine cases -/

theorem d7RightCountOf_semantic (coloring : Nat -> Bool) :
    d7RightCountOf coloring =
      (List.finRange 4).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 8) := by
  unfold d7RightCountOf d7RightCount
  apply List.countP_congr
  intro position _hposition
  rw [d7RightPatternColor_secondPattern coloring position]

theorem d7TenVertices_split :
    (List.finRange 10).map (fun position => position.val + 2) =
      (List.finRange 6).map (fun position => position.val + 2) ++
      (List.finRange 4).map (fun position => position.val + 8) := by
  native_decide

theorem d7MappedLeft_count (coloring : Nat -> Bool) :
    (List.finRange 6).countP
        ((fun vertex => ramseyEdge 12 coloring (1 : Fin 12).val vertex) ∘
          fun position : Fin 6 => position.val + 2) =
      (List.finRange 6).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 2) := by
  apply List.countP_congr
  intro position _hposition
  have hlt : 1 < position.val + 2 := by omega
  simp [ramseyEdge, coloringEdge, hlt]

theorem d7MappedRight_count (coloring : Nat -> Bool) :
    (List.finRange 4).countP
        ((fun vertex => ramseyEdge 12 coloring (1 : Fin 12).val vertex) ∘
          fun position : Fin 4 => position.val + 8) =
      (List.finRange 4).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 8) := by
  apply List.countP_congr
  intro position _hposition
  have hlt : 1 < position.val + 8 := by omega
  simp [ramseyEdge, coloringEdge, hlt]

theorem d7Center_positive_degree_eq
    (coloring : Nat -> Bool)
    (hrootCenter : coloringEdge 12 coloring 0 1 = true) :
    (positiveNeighbors coloring (1 : Fin 12)).length =
      1 + d7LeftCountOf coloring + d7RightCountOf coloring := by
  rw [d7LeftCountOf_semantic, d7RightCountOf_semantic]
  have hrootEdge : ramseyEdge 12 coloring 1 0 = true := by
    simpa [ramseyEdge, coloringEdge] using hrootCenter
  unfold positiveNeighbors
  rw [← List.countP_eq_length_filter]
  rw [otherVertices_one_eq, d7TenVertices_split]
  simp only [List.countP_cons, List.countP_append, List.countP_map]
  rw [d7MappedLeft_count, d7MappedRight_count]
  simp [hrootEdge]
  omega

theorem d7P_bounds_of_center
    (coloring : Nat -> Bool) (center : Fin 7)
    (hlower : 1 ≤ d7NormalizedInternalDegree coloring center)
    (hupper : d7NormalizedInternalDegree coloring center ≤ 2) :
    1 ≤ d7PValue coloring center ∧ d7PValue coloring center ≤ 2 := by
  rw [d7PValue_eq_internalDegree]
  exact ⟨hlower, hupper⟩

theorem d7P_one_or_two
    (coloring : Nat -> Bool) (center : Fin 7)
    (hlower : 1 ≤ d7NormalizedInternalDegree coloring center)
    (hupper : d7NormalizedInternalDegree coloring center ≤ 2) :
    d7PValue coloring center = 1 ∨ d7PValue coloring center = 2 := by
  have hp := d7P_bounds_of_center coloring center hlower hupper
  omega

theorem d7CenterMoved_degree_eq_one_add_p_add_q
    (coloring : Nat -> Bool)
    (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) :
    (positiveNeighbors (d7CenterMovedColoring coloring center) (1 : Fin 12)).length =
      1 + d7PValue coloring center + d7QValue coloring center := by
  exact d7Center_positive_degree_eq
    (d7CenterMovedColoring coloring center)
    (d7CenterMoved_root_center coloring hdegree center)

theorem d7PQ_ge_two
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) :
    2 ≤ d7PValue coloring center + d7QValue coloring center := by
  let source := d7CenterMovedColoring coloring center
  have hsourceFree : isRamseyFree 12 4 4 source :=
    (d7CenterMoved_isRamseyFree_iff coloring center).mp hfree
  have hminimum := positiveDegree_ge_three hsourceFree (1 : Fin 12)
  have hdecomposition :=
    d7CenterMoved_degree_eq_one_add_p_add_q coloring hdegree center
  change (positiveNeighbors source (1 : Fin 12)).length =
      1 + d7PValue coloring center + d7QValue coloring center
    at hdecomposition
  omega

def D7NineCases (p q : Nat) : Prop :=
  (p = 1 ∧ q = 1) ∨
  (p = 1 ∧ q = 2) ∨
  (p = 1 ∧ q = 3) ∨
  (p = 1 ∧ q = 4) ∨
  (p = 2 ∧ q = 0) ∨
  (p = 2 ∧ q = 1) ∨
  (p = 2 ∧ q = 2) ∨
  (p = 2 ∧ q = 3) ∨
  (p = 2 ∧ q = 4)

theorem d7NineCases_of_bounds {p q : Nat}
    (hpLower : 1 ≤ p) (hpUpper : p ≤ 2)
    (hqUpper : q ≤ 4) (hpq : 2 ≤ p + q) :
    D7NineCases p q := by
  unfold D7NineCases
  omega

def D7TwoCenterBranch (coloring : Nat -> Bool) (p q : Nat) : Prop :=
  coloringEdge 12 coloring 0 1 = true ∧
  (forall position : Fin 6,
    coloringEdge 12 coloring 0 (position.val + 2) = true) ∧
  (forall position : Fin 4,
    coloringEdge 12 coloring 0 (position.val + 8) = false) ∧
  (forall position : Fin 6,
    coloringEdge 12 coloring 1 (position.val + 2) =
      decide (position.val < p)) ∧
  (forall position : Fin 4,
    coloringEdge 12 coloring 1 (position.val + 8) =
      decide (position.val < q))

theorem d7Normalized_branch
    (coloring : Nat -> Bool) (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) :
    D7TwoCenterBranch (d7NormalizedColoring coloring center)
      (d7PValue coloring center) (d7QValue coloring center) := by
  exact ⟨d7Normalized_root_center coloring hdegree center,
    d7Normalized_root_left coloring hdegree center,
    d7Normalized_root_right coloring hdegree center,
    d7Normalized_center_left coloring center,
    d7Normalized_center_right coloring center⟩

theorem d7FinRangeSix_count_threshold (threshold : Nat)
    (hthreshold : threshold ≤ 6) :
    (List.finRange 6).countP
        (fun position => decide (position.val < threshold)) = threshold := by
  have hcases : threshold = 0 ∨ threshold = 1 ∨ threshold = 2 ∨
      threshold = 3 ∨ threshold = 4 ∨ threshold = 5 ∨
      threshold = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

theorem d7FinRangeFour_count_threshold (threshold : Nat)
    (hthreshold : threshold ≤ 4) :
    (List.finRange 4).countP
        (fun position => decide (position.val < threshold)) = threshold := by
  have hcases : threshold = 0 ∨ threshold = 1 ∨ threshold = 2 ∨
      threshold = 3 ∨ threshold = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem d7Branch_center_degree_eq_one_add_p_add_q
    (coloring : Nat -> Bool) (p q : Nat)
    (hbranch : D7TwoCenterBranch coloring p q)
    (hpUpper : p ≤ 6) (hqUpper : q ≤ 4) :
    (positiveNeighbors coloring (1 : Fin 12)).length = 1 + p + q := by
  have hleft : d7LeftCountOf coloring = p := by
    rw [d7LeftCountOf_semantic]
    calc
      (List.finRange 6).countP (fun position =>
          coloringEdge 12 coloring 1 (position.val + 2)) =
          (List.finRange 6).countP (fun position =>
            decide (position.val < p)) := by
              apply List.countP_congr
              intro position _hposition
              rw [hbranch.2.2.2.1 position]
      _ = p := d7FinRangeSix_count_threshold p hpUpper
  have hright : d7RightCountOf coloring = q := by
    rw [d7RightCountOf_semantic]
    calc
      (List.finRange 4).countP (fun position =>
          coloringEdge 12 coloring 1 (position.val + 8)) =
          (List.finRange 4).countP (fun position =>
            decide (position.val < q)) := by
              apply List.countP_congr
              intro position _hposition
              rw [hbranch.2.2.2.2 position]
      _ = q := d7FinRangeFour_count_threshold q hqUpper
  calc
    (positiveNeighbors coloring (1 : Fin 12)).length =
        1 + d7LeftCountOf coloring + d7RightCountOf coloring :=
      d7Center_positive_degree_eq coloring hbranch.1
    _ = 1 + p + q := by rw [hleft, hright]

theorem d7Normalized_center_degree_eq_one_add_p_add_q
    (coloring : Nat -> Bool)
    (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7) :
    (positiveNeighbors (d7NormalizedColoring coloring center)
        (1 : Fin 12)).length =
      1 + d7PValue coloring center + d7QValue coloring center := by
  apply d7Branch_center_degree_eq_one_add_p_add_q
    (d7NormalizedColoring coloring center)
    (d7PValue coloring center) (d7QValue coloring center)
    (d7Normalized_branch coloring hdegree center)
  · simpa [d7PValue, d7LeftCountOf] using
      d7LeftCount_le_six
        (d7SecondPattern (d7CenterMovedColoring coloring center))
  · exact d7QValue_le_four coloring center

theorem d7Normalized_enters_nine_cases
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7)
    (center : Fin 7)
    (hlower : 1 ≤ d7NormalizedInternalDegree coloring center)
    (hupper : d7NormalizedInternalDegree coloring center ≤ 2) :
    D7NineCases (d7PValue coloring center) (d7QValue coloring center) ∧
      D7TwoCenterBranch (d7NormalizedColoring coloring center)
        (d7PValue coloring center) (d7QValue coloring center) := by
  have hp := d7P_bounds_of_center coloring center hlower hupper
  have hq := d7QValue_le_four coloring center
  have hpq := d7PQ_ge_two hfree hdegree center
  exact ⟨d7NineCases_of_bounds hp.1 hp.2 hq hpq,
    d7Normalized_branch coloring hdegree center⟩

/-! A proof-parametric canonical choice, ready to consume MinCenter. -/

def D7LowCenterExists (coloring : Nat -> Bool) : Prop :=
  ∃ center : Fin 7,
    1 ≤ d7NormalizedInternalDegree coloring center ∧
      d7NormalizedInternalDegree coloring center ≤ 2

noncomputable def d7ChosenCenter
    (coloring : Nat -> Bool) (hexists : D7LowCenterExists coloring) : Fin 7 :=
  Classical.choose hexists

theorem d7ChosenCenter_lower
    (coloring : Nat -> Bool) (hexists : D7LowCenterExists coloring) :
    1 ≤ d7NormalizedInternalDegree coloring
      (d7ChosenCenter coloring hexists) :=
  (Classical.choose_spec hexists).1

theorem d7ChosenCenter_upper
    (coloring : Nat -> Bool) (hexists : D7LowCenterExists coloring) :
    d7NormalizedInternalDegree coloring
      (d7ChosenCenter coloring hexists) ≤ 2 :=
  (Classical.choose_spec hexists).2

noncomputable def d7ChosenNormalizedColoring
    (coloring : Nat -> Bool) (hexists : D7LowCenterExists coloring) :
    Nat -> Bool :=
  d7NormalizedColoring coloring (d7ChosenCenter coloring hexists)

theorem d7ChosenNormalized_isRamseyFree_iff
    (coloring : Nat -> Bool) (hexists : D7LowCenterExists coloring) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4 (d7ChosenNormalizedColoring coloring hexists) := by
  exact d7Normalized_isRamseyFree_iff coloring
    (d7ChosenCenter coloring hexists)

theorem d7ChosenNormalized_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat -> Bool)
    (hexists : D7LowCenterExists coloring) (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (d7ChosenNormalizedColoring coloring hexists) motif := by
  exact d7Normalized_inducedMotifOccurrence_iff coloring
    (d7ChosenCenter coloring hexists) motif

theorem d7ChosenNormalized_enters_nine_cases
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7)
    (hexists : D7LowCenterExists coloring) :
    D7NineCases
        (d7PValue coloring (d7ChosenCenter coloring hexists))
        (d7QValue coloring (d7ChosenCenter coloring hexists)) ∧
      D7TwoCenterBranch (d7ChosenNormalizedColoring coloring hexists)
        (d7PValue coloring (d7ChosenCenter coloring hexists))
        (d7QValue coloring (d7ChosenCenter coloring hexists)) := by
  simpa [d7ChosenNormalizedColoring] using
    d7Normalized_enters_nine_cases hfree hdegree
      (d7ChosenCenter coloring hexists)
      (d7ChosenCenter_lower coloring hexists)
      (d7ChosenCenter_upper coloring hexists)

/-! ## The exact nine DIMACS clauses -/

def d7ExtraDimacsClauses : List (List Int) :=
  [[12], [-14], [14, -15], [15, -16], [16, -17],
    [18, -19], [19, -20], [20, -21], [13, 18]]

theorem d7ExtraDimacsClauses_length : d7ExtraDimacsClauses.length = 9 := by
  native_decide

def d7DimacsClause (clause : List Int) : CNF.Clause Nat :=
  clause.map LRATCatcher.dimacsLit

theorem d7DimacsLit_positiveEdge {vertex : Nat}
    (_hlower : 1 < vertex) (_hupper : vertex < 12) :
    LRATCatcher.dimacsLit
        (Int.ofNat (edgeVar 12 1 vertex + 1)) =
      (edgeVar 12 1 vertex, true) := by
  unfold LRATCatcher.dimacsLit
  simp
  omega

theorem d7DimacsLit_negativeEdge {vertex : Nat}
    (_hlower : 1 < vertex) (_hupper : vertex < 12) :
    LRATCatcher.dimacsLit
        (-Int.ofNat (edgeVar 12 1 vertex + 1)) =
      (edgeVar 12 1 vertex, false) := by
  unfold LRATCatcher.dimacsLit
  change
    (edgeVar 12 1 vertex + 1 - 1,
      decide (0 < -Int.ofNat (edgeVar 12 1 vertex + 1))) =
      (edgeVar 12 1 vertex, false)
  have hpositive :
      (0 : Int) < Int.ofNat (edgeVar 12 1 vertex + 1) :=
    Int.natCast_pos.mpr (by omega)
  have hnotPositive :
      ¬(0 : Int) < -Int.ofNat (edgeVar 12 1 vertex + 1) := by
    omega
  have hnonnegative :
      (0 : Int) ≤ Int.ofNat (edgeVar 12 1 vertex) :=
    Int.natCast_nonneg _
  simp
  omega

theorem d7PositiveUnit_eval_true
    (coloring : Nat -> Bool) {vertex : Nat}
    (hlower : 1 < vertex) (hupper : vertex < 12)
    (hcolor : coloring (edgeVar 12 1 vertex) = true) :
    CNF.Clause.eval coloring
      (d7DimacsClause [Int.ofNat (edgeVar 12 1 vertex + 1)]) = true := by
  simp only [d7DimacsClause, List.map_cons, List.map_nil,
    CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  rw [d7DimacsLit_positiveEdge hlower hupper]
  simp [hcolor]

theorem d7NegativeUnit_eval_true
    (coloring : Nat -> Bool) {vertex : Nat}
    (hlower : 1 < vertex) (hupper : vertex < 12)
    (hcolor : coloring (edgeVar 12 1 vertex) = false) :
    CNF.Clause.eval coloring
      (d7DimacsClause [-Int.ofNat (edgeVar 12 1 vertex + 1)]) = true := by
  simp only [d7DimacsClause, List.map_cons, List.map_nil,
    CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  rw [d7DimacsLit_negativeEdge hlower hupper]
  simp [hcolor]

theorem d7PrefixImplication_eval_true
    (coloring : Nat -> Bool) (threshold : Nat)
    {leftVertex rightVertex leftRank rightRank : Nat}
    (hleftLower : 1 < leftVertex) (hleftUpper : leftVertex < 12)
    (hrightLower : 1 < rightVertex) (hrightUpper : rightVertex < 12)
    (hranks : leftRank < rightRank)
    (hleft : coloring (edgeVar 12 1 leftVertex) =
      decide (leftRank < threshold))
    (hright : coloring (edgeVar 12 1 rightVertex) =
      decide (rightRank < threshold)) :
    CNF.Clause.eval coloring (d7DimacsClause
      [Int.ofNat (edgeVar 12 1 leftVertex + 1),
        -Int.ofNat (edgeVar 12 1 rightVertex + 1)]) = true := by
  simp only [d7DimacsClause, List.map_cons, List.map_nil,
    CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  rw [d7DimacsLit_positiveEdge hleftLower hleftUpper,
    d7DimacsLit_negativeEdge hrightLower hrightUpper]
  by_cases hbelow : leftRank < threshold
  · simp [hleft, hbelow]
  · have hrightNotBelow : ¬ rightRank < threshold := by omega
    simp [hright, hrightNotBelow]

theorem d7PositivePair_eval_true
    (coloring : Nat -> Bool) {leftVertex rightVertex : Nat}
    (hleftLower : 1 < leftVertex) (hleftUpper : leftVertex < 12)
    (hrightLower : 1 < rightVertex) (hrightUpper : rightVertex < 12)
    (hsatisfied : coloring (edgeVar 12 1 leftVertex) = true ∨
      coloring (edgeVar 12 1 rightVertex) = true) :
    CNF.Clause.eval coloring (d7DimacsClause
      [Int.ofNat (edgeVar 12 1 leftVertex + 1),
        Int.ofNat (edgeVar 12 1 rightVertex + 1)]) = true := by
  simp only [d7DimacsClause, List.map_cons, List.map_nil,
    CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  rw [d7DimacsLit_positiveEdge hleftLower hleftUpper,
    d7DimacsLit_positiveEdge hrightLower hrightUpper]
  rcases hsatisfied with hleft | hright
  · simp [hleft]
  · simp [hright]

theorem d7Branch_second_left_raw
    {coloring : Nat -> Bool} {p q : Nat}
    (hbranch : D7TwoCenterBranch coloring p q) (position : Fin 6) :
    coloring (edgeVar 12 1 (position.val + 2)) =
      decide (position.val < p) := by
  have hedge := hbranch.2.2.2.1 position
  have hordered : 1 < position.val + 2 := by omega
  simpa [coloringEdge, hordered] using hedge

theorem d7Branch_second_right_raw
    {coloring : Nat -> Bool} {p q : Nat}
    (hbranch : D7TwoCenterBranch coloring p q) (position : Fin 4) :
    coloring (edgeVar 12 1 (position.val + 8)) =
      decide (position.val < q) := by
  have hedge := hbranch.2.2.2.2 position
  have hordered : 1 < position.val + 8 := by omega
  simpa [coloringEdge, hordered] using hedge

theorem d7ExtraClause_eval_true
    (coloring : Nat -> Bool) (p q : Nat)
    (hbranch : D7TwoCenterBranch coloring p q)
    (hpLower : 1 ≤ p) (hpUpper : p ≤ 2)
    (hpq : 2 ≤ p + q) (position : Fin 9) :
    CNF.Clause.eval coloring
      (d7DimacsClause (d7ExtraDimacsClauses.getD position.val [])) = true := by
  have hcases : position.val = 0 ∨ position.val = 1 ∨
      position.val = 2 ∨ position.val = 3 ∨ position.val = 4 ∨
      position.val = 5 ∨ position.val = 6 ∨ position.val = 7 ∨
      position.val = 8 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h <;> simp only [h]
  · have hedge := d7Branch_second_left_raw hbranch (0 : Fin 6)
    have htrue : coloring (edgeVar 12 1 2) = true := by
      simpa [show 0 < p by omega] using hedge
    have hsatisfied := d7PositiveUnit_eval_true coloring
      (vertex := 2) (by omega) (by omega) htrue
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hedge := d7Branch_second_left_raw hbranch (2 : Fin 6)
    have hnot : ¬ 2 < p := by omega
    have hfalse : coloring (edgeVar 12 1 4) = false := by
      simpa [hnot] using hedge
    have hsatisfied := d7NegativeUnit_eval_true coloring
      (vertex := 4) (by omega) (by omega) hfalse
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hsatisfied := d7PrefixImplication_eval_true coloring p
      (leftVertex := 4) (rightVertex := 5)
      (leftRank := 2) (rightRank := 3)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (d7Branch_second_left_raw hbranch (2 : Fin 6))
      (d7Branch_second_left_raw hbranch (3 : Fin 6))
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hsatisfied := d7PrefixImplication_eval_true coloring p
      (leftVertex := 5) (rightVertex := 6)
      (leftRank := 3) (rightRank := 4)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (d7Branch_second_left_raw hbranch (3 : Fin 6))
      (d7Branch_second_left_raw hbranch (4 : Fin 6))
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hsatisfied := d7PrefixImplication_eval_true coloring p
      (leftVertex := 6) (rightVertex := 7)
      (leftRank := 4) (rightRank := 5)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (d7Branch_second_left_raw hbranch (4 : Fin 6))
      (d7Branch_second_left_raw hbranch (5 : Fin 6))
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hsatisfied := d7PrefixImplication_eval_true coloring q
      (leftVertex := 8) (rightVertex := 9)
      (leftRank := 0) (rightRank := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (d7Branch_second_right_raw hbranch (0 : Fin 4))
      (d7Branch_second_right_raw hbranch (1 : Fin 4))
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hsatisfied := d7PrefixImplication_eval_true coloring q
      (leftVertex := 9) (rightVertex := 10)
      (leftRank := 1) (rightRank := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (d7Branch_second_right_raw hbranch (1 : Fin 4))
      (d7Branch_second_right_raw hbranch (2 : Fin 4))
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hsatisfied := d7PrefixImplication_eval_true coloring q
      (leftVertex := 10) (rightVertex := 11)
      (leftRank := 2) (rightRank := 3)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (d7Branch_second_right_raw hbranch (2 : Fin 4))
      (d7Branch_second_right_raw hbranch (3 : Fin 4))
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied
  · have hleft := d7Branch_second_left_raw hbranch (1 : Fin 6)
    have hright := d7Branch_second_right_raw hbranch (0 : Fin 4)
    have hor : coloring (edgeVar 12 1 3) = true ∨
        coloring (edgeVar 12 1 8) = true := by
      by_cases htwo : 1 < p
      · exact Or.inl (by simpa [htwo] using hleft)
      · have hq : 0 < q := by omega
        exact Or.inr (by simpa [hq] using hright)
    have hsatisfied := d7PositivePair_eval_true coloring
      (leftVertex := 3) (rightVertex := 8)
      (by omega) (by omega) (by omega) (by omega) hor
    simpa [d7ExtraDimacsClauses, edgeVar] using hsatisfied

theorem d7ChosenNormalized_satisfies_exact_nine_clauses
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7)
    (hexists : D7LowCenterExists coloring) (position : Fin 9) :
    CNF.Clause.eval (d7ChosenNormalizedColoring coloring hexists)
      (d7DimacsClause (d7ExtraDimacsClauses.getD position.val [])) = true := by
  let center := d7ChosenCenter coloring hexists
  let p := d7PValue coloring center
  let q := d7QValue coloring center
  have hbranch : D7TwoCenterBranch
      (d7ChosenNormalizedColoring coloring hexists) p q := by
    simpa [center, p, q, d7ChosenNormalizedColoring] using
      d7Normalized_branch coloring hdegree center
  have hp := d7P_bounds_of_center coloring center
    (d7ChosenCenter_lower coloring hexists)
    (d7ChosenCenter_upper coloring hexists)
  have hpq := d7PQ_ge_two hfree hdegree center
  exact d7ExtraClause_eval_true
    (d7ChosenNormalizedColoring coloring hexists) p q
    hbranch hp.1 hp.2 hpq position

#print axioms d7CenterMoveLabels_isPermutation
#print axioms d7CenterLeftCount_eq_internalDegree
#print axioms d7CenterMoved_isRamseyFree_iff
#print axioms d7SecondSortedLabels_isPermutation
#print axioms d7PValue_eq_internalDegree
#print axioms d7Normalized_isRamseyFree_iff
#print axioms d7Center_positive_degree_eq
#print axioms d7CenterMoved_degree_eq_one_add_p_add_q
#print axioms d7Normalized_center_degree_eq_one_add_p_add_q
#print axioms d7PQ_ge_two
#print axioms d7ChosenNormalized_isRamseyFree_iff
#print axioms d7ChosenNormalized_inducedMotifOccurrence_iff
#print axioms d7ChosenNormalized_enters_nine_cases
#print axioms d7ChosenNormalized_satisfies_exact_nine_clauses

end LRATCatcher.Tests.R44Cover6DegreeSevenNormalization
