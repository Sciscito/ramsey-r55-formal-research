import LRATCatcher.Tests.R44OrderTwelveRootSymmetryTransport

/-!
  # Two-centre symmetry breaking at order twelve

  After the root has been normalised to have its eight positive neighbours
  at labels `1, ..., 8`, this module fixes vertex `1` as a second centre and
  independently sorts its incident colours in the two root blocks
  `2, ..., 8` and `9, ..., 11`.

  The construction is a genuine permutation of `Fin 12`.  Its finite
  bookkeeping is checked exhaustively over the ten relevant edge bits.
-/

namespace LRATCatcher.Tests.R44OrderTwelveTwoCenterSymmetry

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry

abbrev Vertex := Fin 12
abbrev SecondPattern := BitVec 10

def secondPatternColor (pattern : SecondPattern) (position : Fin 10) : Bool :=
  pattern.getLsbD position.val

def leftPatternColor (pattern : SecondPattern) (position : Fin 7) : Bool :=
  secondPatternColor pattern ⟨position.val, by omega⟩

def rightPatternColor (pattern : SecondPattern) (position : Fin 3) : Bool :=
  secondPatternColor pattern ⟨position.val + 7, by omega⟩

def sortedLeft (pattern : SecondPattern) : List (Fin 7) :=
  (List.finRange 7).filter (leftPatternColor pattern) ++
    (List.finRange 7).filter (fun position => !(leftPatternColor pattern position))

def sortedRight (pattern : SecondPattern) : List (Fin 3) :=
  (List.finRange 3).filter (rightPatternColor pattern) ++
    (List.finRange 3).filter (fun position => !(rightPatternColor pattern position))

def secondSortedLabels (pattern : SecondPattern) : List Nat :=
  [0, 1] ++
    (sortedLeft pattern).map (fun position => position.val + 2) ++
    (sortedRight pattern).map (fun position => position.val + 9)

def leftCount (pattern : SecondPattern) : Nat :=
  (List.finRange 7).countP (leftPatternColor pattern)

def rightCount (pattern : SecondPattern) : Nat :=
  (List.finRange 3).countP (rightPatternColor pattern)

theorem leftCount_le_seven (pattern : SecondPattern) :
    leftCount pattern ≤ 7 := by
  native_decide +revert

theorem rightCount_le_three (pattern : SecondPattern) :
    rightCount pattern ≤ 3 := by
  native_decide +revert

theorem secondSortedLabels_isPermutation (pattern : SecondPattern) :
    isPermutation (secondSortedLabels pattern) 12 = true := by
  native_decide +revert

theorem sortedLeft_color (pattern : SecondPattern) (position : Fin 7) :
    leftPatternColor pattern ((sortedLeft pattern).getD position.val 0) =
      decide (position.val < leftCount pattern) := by
  native_decide +revert

theorem sortedRight_color (pattern : SecondPattern) (position : Fin 3) :
    rightPatternColor pattern ((sortedRight pattern).getD position.val 0) =
      decide (position.val < rightCount pattern) := by
  native_decide +revert

theorem secondSortedLabels_getD_left
    (pattern : SecondPattern) (position : Fin 7) :
    (secondSortedLabels pattern).getD (position.val + 2) 12 =
      ((sortedLeft pattern).getD position.val 0).val + 2 := by
  native_decide +revert

theorem secondSortedLabels_getD_right
    (pattern : SecondPattern) (position : Fin 3) :
    (secondSortedLabels pattern).getD (position.val + 9) 12 =
      ((sortedRight pattern).getD position.val 0).val + 9 := by
  native_decide +revert

noncomputable def secondSortPermutationForPattern
    (pattern : SecondPattern) : FinPermutation 12 :=
  listPermutationToFin (secondSortedLabels pattern) 12
    (secondSortedLabels_isPermutation pattern)

@[simp] theorem secondSortPermutationForPattern_zero
    (pattern : SecondPattern) :
    secondSortPermutationForPattern pattern (0 : Vertex) = 0 := by
  apply Fin.ext
  rw [secondSortPermutationForPattern, listPermutationToFin_apply_val]
  simp [secondSortedLabels]

@[simp] theorem secondSortPermutationForPattern_one
    (pattern : SecondPattern) :
    secondSortPermutationForPattern pattern (1 : Vertex) = 1 := by
  apply Fin.ext
  rw [secondSortPermutationForPattern, listPermutationToFin_apply_val]
  simp [secondSortedLabels]

theorem secondSortPermutationForPattern_left_val
    (pattern : SecondPattern) (position : Fin 7) :
    (secondSortPermutationForPattern pattern
      ⟨position.val + 2, by omega⟩).val =
        ((sortedLeft pattern).getD position.val 0).val + 2 := by
  rw [secondSortPermutationForPattern, listPermutationToFin_apply_val]
  exact secondSortedLabels_getD_left pattern position

theorem secondSortPermutationForPattern_right_val
    (pattern : SecondPattern) (position : Fin 3) :
    (secondSortPermutationForPattern pattern
      ⟨position.val + 9, by omega⟩).val =
        ((sortedRight pattern).getD position.val 0).val + 9 := by
  rw [secondSortPermutationForPattern, listPermutationToFin_apply_val]
  exact secondSortedLabels_getD_right pattern position

def secondPatternBits (coloring : Nat → Bool) : List Bool :=
  List.ofFn fun position : Fin 10 =>
    coloringEdge 12 coloring 1 (position.val + 2)

def secondPattern (coloring : Nat → Bool) : SecondPattern :=
  BitVec.cast (by simp [secondPatternBits])
    (BitVec.ofBoolListLE (secondPatternBits coloring))

theorem leftPatternColor_secondPattern
    (coloring : Nat → Bool) (position : Fin 7) :
    leftPatternColor (secondPattern coloring) position =
      coloringEdge 12 coloring 1 (position.val + 2) := by
  unfold leftPatternColor secondPatternColor secondPattern
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := secondPatternBits coloring) (i := position.val)
    (h := by simp [secondPatternBits]; omega) false]
  change
    (List.ofFn fun position : Fin 10 =>
      coloringEdge 12 coloring 1 (position.val + 2))[position.val]'(by
        simpa using (show position.val < 10 by omega)) = _
  rw [List.getElem_ofFn]

theorem rightPatternColor_secondPattern
    (coloring : Nat → Bool) (position : Fin 3) :
    rightPatternColor (secondPattern coloring) position =
      coloringEdge 12 coloring 1 (position.val + 9) := by
  unfold rightPatternColor secondPatternColor secondPattern
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := secondPatternBits coloring) (i := position.val + 7)
    (h := by simp [secondPatternBits]; omega) false]
  change
    (List.ofFn fun position : Fin 10 =>
      coloringEdge 12 coloring 1 (position.val + 2))[position.val + 7]'(by
        simp; omega) = _
  rw [List.getElem_ofFn]

noncomputable def secondSortPermutation
    (coloring : Nat → Bool) : FinPermutation 12 :=
  secondSortPermutationForPattern (secondPattern coloring)

@[simp] theorem secondSortPermutation_zero (coloring : Nat → Bool) :
    secondSortPermutation coloring (0 : Vertex) = 0 :=
  secondSortPermutationForPattern_zero (secondPattern coloring)

@[simp] theorem secondSortPermutation_one (coloring : Nat → Bool) :
    secondSortPermutation coloring (1 : Vertex) = 1 :=
  secondSortPermutationForPattern_one (secondPattern coloring)

def leftCountOf (coloring : Nat → Bool) : Nat :=
  leftCount (secondPattern coloring)

def rightCountOf (coloring : Nat → Bool) : Nat :=
  rightCount (secondPattern coloring)

theorem secondSort_left_edge (coloring : Nat → Bool)
    (position : Fin 7) :
    coloringEdge 12
        (permuteColoring (secondSortPermutation coloring) coloring)
        1 (position.val + 2) =
      decide (position.val < leftCountOf coloring) := by
  have hedge := coloringEdge_permuteColoring
    (secondSortPermutation coloring) coloring (1 : Vertex)
      ⟨position.val + 2, by omega⟩
  unfold secondSortPermutation at hedge
  rw [secondSortPermutationForPattern_one,
    secondSortPermutationForPattern_left_val
      (secondPattern coloring) position] at hedge
  have hedge' : coloringEdge 12
      (permuteColoring
        (secondSortPermutationForPattern (secondPattern coloring)) coloring)
      1 (position.val + 2) =
        coloringEdge 12 coloring 1
          (((sortedLeft (secondPattern coloring)).getD position.val 0).val + 2) := by
    simpa only [Fin.val_mk] using hedge
  unfold secondSortPermutation
  rw [hedge']
  rw [← leftPatternColor_secondPattern coloring
    ((sortedLeft (secondPattern coloring)).getD position.val 0)]
  exact sortedLeft_color (secondPattern coloring) position

theorem secondSort_right_edge (coloring : Nat → Bool)
    (position : Fin 3) :
    coloringEdge 12
        (permuteColoring (secondSortPermutation coloring) coloring)
        1 (position.val + 9) =
      decide (position.val < rightCountOf coloring) := by
  have hedge := coloringEdge_permuteColoring
    (secondSortPermutation coloring) coloring (1 : Vertex)
      ⟨position.val + 9, by omega⟩
  unfold secondSortPermutation at hedge
  rw [secondSortPermutationForPattern_one,
    secondSortPermutationForPattern_right_val
      (secondPattern coloring) position] at hedge
  have hedge' : coloringEdge 12
      (permuteColoring
        (secondSortPermutationForPattern (secondPattern coloring)) coloring)
      1 (position.val + 9) =
        coloringEdge 12 coloring 1
          (((sortedRight (secondPattern coloring)).getD position.val 0).val + 9) := by
    simpa only [Fin.val_mk] using hedge
  unfold secondSortPermutation
  rw [hedge']
  rw [← rightPatternColor_secondPattern coloring
    ((sortedRight (secondPattern coloring)).getD position.val 0)]
  exact sortedRight_color (secondPattern coloring) position

theorem secondSort_isRamseyFree_iff (coloring : Nat → Bool) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4
        (permuteColoring (secondSortPermutation coloring) coloring) :=
  isRamseyFree_permute_iff (secondSortPermutation coloring) coloring

theorem secondSort_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat → Bool) (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (permuteColoring (secondSortPermutation coloring) coloring) motif :=
  inducedMotifOccurrence_permute_iff
    (secondSortPermutation coloring) coloring motif

#print axioms secondSortedLabels_isPermutation
#print axioms secondSort_left_edge
#print axioms secondSort_right_edge
#print axioms secondSort_isRamseyFree_iff
#print axioms secondSort_inducedMotifOccurrence_iff

end LRATCatcher.Tests.R44OrderTwelveTwoCenterSymmetry
