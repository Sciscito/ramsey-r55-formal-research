import LRATCatcher.Tests.R44OrderTwelveTwoCenterSymmetry
import LRATCatcher.Tests.R44OrderTwelveDegreeBounds

/-!
  # Exhaustive two-centre cases for an eight-positive-degree root

  This module composes the root sort and the block-preserving second-centre
  sort.  For every `R(4,4)`-free coloring whose root has positive degree
  eight, the resulting coloring has parameters `p,q` satisfying

  * `p ≤ 3`,
  * `q ≤ 3`, and
  * `2 ≤ p + q`.

  Hence `(p,q)` belongs to the thirteen cases used by the universal CNF
  generator.  Ramsey freeness and induced motif occurrences are transported
  through the single composed permutation.
-/

namespace LRATCatcher.Tests.R44OrderTwelveTwoCenterCases

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44OrderTwelveTwoCenterSymmetry
open LRATCatcher.Tests.R44OrderTwelveDegreeBounds

abbrev Vertex := Fin 12

def positiveRootDegree (coloring : Nat → Bool) : Nat :=
  (List.finRange 11).countP fun position =>
    coloringEdge 12 coloring 0 (position.val + 1)

theorem rootPattern_count_eq_positiveRootDegree (coloring : Nat → Bool) :
    (List.finRange 11).countP (patternColor (rootPattern coloring)) =
      positiveRootDegree coloring := by
  apply List.countP_congr
  intro position hposition
  rw [patternColor_rootPattern coloring position]

theorem sortedNonRoot_exact_eight (pattern : RootPattern)
    (hdegree : (List.finRange 11).countP (patternColor pattern) = 8)
    (position : Fin 11) :
    patternColor pattern
        ((sortedNonRoot pattern).getD position.val 0) =
      decide (position.val < 8) := by
  native_decide +revert

theorem rootSort_exact_eight (coloring : Nat → Bool)
    (hdegree : positiveRootDegree coloring = 8)
    (position : Fin 11) :
    coloringEdge 12
        (permuteColoring (rootSortPermutation coloring) coloring)
        0 (position.val + 1) =
      decide (position.val < 8) := by
  have hcount :
      (List.finRange 11).countP (patternColor (rootPattern coloring)) = 8 := by
    rw [rootPattern_count_eq_positiveRootDegree, hdegree]
  have hsorted := sortedNonRoot_exact_eight
    (rootPattern coloring) hcount position
  rw [patternColor_rootPattern coloring
    ((sortedNonRoot (rootPattern coloring)).getD position.val 0)] at hsorted
  have hedge := coloringEdge_permuteColoring
    (rootSortPermutation coloring) coloring (0 : Vertex)
      ⟨position.val + 1, by omega⟩
  rw [rootSortPermutation_zero,
    rootSortPermutation_nonRoot_val coloring position] at hedge
  exact (by simpa only [Fin.val_mk] using hedge.trans hsorted)

noncomputable def rootSortedColoring (coloring : Nat → Bool) : Nat → Bool :=
  permuteColoring (rootSortPermutation coloring) coloring

noncomputable def twoCenterColoring (coloring : Nat → Bool) : Nat → Bool :=
  permuteColoring (secondSortPermutation (rootSortedColoring coloring))
    (rootSortedColoring coloring)

noncomputable def twoCenterPermutation (coloring : Nat → Bool) : FinPermutation 12 :=
  (secondSortPermutation (rootSortedColoring coloring)).trans
    (rootSortPermutation coloring)

theorem permuteColoring_trans (left right : FinPermutation 12)
    (coloring : Nat → Bool) (index : Nat) :
    permuteColoring (left.trans right) coloring index =
      permuteColoring left (permuteColoring right coloring) index := by
  unfold permuteColoring FinPermutation.trans
  simp only
  symm
  exact coloringEdge_permuteColoring right coloring _ _

theorem twoCenterColoring_eq_single_permutation (coloring : Nat → Bool) :
    twoCenterColoring coloring =
      permuteColoring (twoCenterPermutation coloring) coloring := by
  funext index
  exact (permuteColoring_trans
    (secondSortPermutation (rootSortedColoring coloring))
    (rootSortPermutation coloring) coloring index).symm

@[simp] theorem twoCenterPermutation_zero (coloring : Nat → Bool) :
    twoCenterPermutation coloring (0 : Vertex) = 0 := by
  simp [twoCenterPermutation, FinPermutation.trans]

@[simp] theorem twoCenterPermutation_one (coloring : Nat → Bool) :
    twoCenterPermutation coloring (1 : Vertex) =
      rootSortPermutation coloring (1 : Vertex) := by
  simp [twoCenterPermutation, FinPermutation.trans]

noncomputable def pValue (coloring : Nat → Bool) : Nat :=
  leftCountOf (rootSortedColoring coloring)

noncomputable def qValue (coloring : Nat → Bool) : Nat :=
  rightCountOf (rootSortedColoring coloring)

theorem qValue_le_three (coloring : Nat → Bool) :
    qValue coloring ≤ 3 :=
  rightCount_le_three (secondPattern (rootSortedColoring coloring))

theorem twoCenter_root_one (coloring : Nat → Bool)
    (hdegree : positiveRootDegree coloring = 8) :
    coloringEdge 12 (twoCenterColoring coloring) 0 1 = true := by
  have hedge := coloringEdge_permuteColoring
    (secondSortPermutation (rootSortedColoring coloring))
    (rootSortedColoring coloring) (0 : Vertex) (1 : Vertex)
  rw [secondSortPermutation_zero, secondSortPermutation_one] at hedge
  have hroot := rootSort_exact_eight coloring hdegree (0 : Fin 11)
  unfold twoCenterColoring
  exact (by simpa only [Fin.val_mk] using hedge.trans hroot)
theorem twoCenter_root_left (coloring : Nat → Bool)
    (hdegree : positiveRootDegree coloring = 8)
    (position : Fin 7) :
    coloringEdge 12 (twoCenterColoring coloring)
      0 (position.val + 2) = true := by
  have hedge := coloringEdge_permuteColoring
    (secondSortPermutation (rootSortedColoring coloring))
    (rootSortedColoring coloring) (0 : Vertex)
      ⟨position.val + 2, by omega⟩
  unfold secondSortPermutation at hedge
  rw [secondSortPermutationForPattern_zero,
    secondSortPermutationForPattern_left_val] at hedge
  let oldPosition : Fin 11 :=
    ⟨((sortedLeft (secondPattern (rootSortedColoring coloring))).getD
      position.val 0).val + 1, by omega⟩
  have hroot := rootSort_exact_eight coloring hdegree oldPosition
  have hlt : oldPosition.val < 8 := by
    dsimp [oldPosition]
    omega
  have hvertexEq : oldPosition.val + 1 =
      ((sortedLeft (secondPattern (rootSortedColoring coloring))).getD
        position.val 0).val + 2 := by
    dsimp [oldPosition]
  have hdecide : decide (oldPosition.val < 8) = true := by simp [hlt]
  rw [hvertexEq, hdecide] at hroot
  have hrootTrue : coloringEdge 12 (rootSortedColoring coloring) 0
      (((sortedLeft (secondPattern (rootSortedColoring coloring))).getD
        position.val 0).val + 2) = true := by
    simpa [rootSortedColoring] using hroot
  unfold twoCenterColoring secondSortPermutation
  exact (by simpa only [Fin.val_mk] using hedge.trans hrootTrue)
theorem twoCenter_root_right (coloring : Nat → Bool)
    (hdegree : positiveRootDegree coloring = 8)
    (position : Fin 3) :
    coloringEdge 12 (twoCenterColoring coloring)
      0 (position.val + 9) = false := by
  have hedge := coloringEdge_permuteColoring
    (secondSortPermutation (rootSortedColoring coloring))
    (rootSortedColoring coloring) (0 : Vertex)
      ⟨position.val + 9, by omega⟩
  unfold secondSortPermutation at hedge
  rw [secondSortPermutationForPattern_zero,
    secondSortPermutationForPattern_right_val] at hedge
  let oldPosition : Fin 11 :=
    ⟨((sortedRight (secondPattern (rootSortedColoring coloring))).getD
      position.val 0).val + 8, by omega⟩
  have hroot := rootSort_exact_eight coloring hdegree oldPosition
  have hnotLt : ¬ oldPosition.val < 8 := by
    dsimp [oldPosition]
    omega
  have hvertexEq : oldPosition.val + 1 =
      ((sortedRight (secondPattern (rootSortedColoring coloring))).getD
        position.val 0).val + 9 := by
    dsimp [oldPosition]
  have hdecide : decide (oldPosition.val < 8) = false := by simp [hnotLt]
  rw [hvertexEq, hdecide] at hroot
  have hrootFalse : coloringEdge 12 (rootSortedColoring coloring) 0
      (((sortedRight (secondPattern (rootSortedColoring coloring))).getD
        position.val 0).val + 9) = false := by
    simpa [rootSortedColoring] using hroot
  unfold twoCenterColoring secondSortPermutation
  exact (by simpa only [Fin.val_mk] using hedge.trans hrootFalse)
theorem twoCenter_second_left (coloring : Nat → Bool)
    (position : Fin 7) :
    coloringEdge 12 (twoCenterColoring coloring)
        1 (position.val + 2) =
      decide (position.val < pValue coloring) :=
  secondSort_left_edge (rootSortedColoring coloring) position

theorem twoCenter_second_right (coloring : Nat → Bool)
    (position : Fin 3) :
    coloringEdge 12 (twoCenterColoring coloring)
        1 (position.val + 9) =
      decide (position.val < qValue coloring) :=
  secondSort_right_edge (rootSortedColoring coloring) position

theorem common_positive_pair_false
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (left right : Nat)
    (hleft : 2 ≤ left) (hordered : left < right) (hright : right < 9)
    (hrootCenter : coloringEdge 12 coloring 0 1 = true)
    (hrootLeft : coloringEdge 12 coloring 0 left = true)
    (hrootRight : coloringEdge 12 coloring 0 right = true)
    (hcenterLeft : coloringEdge 12 coloring 1 left = true)
    (hcenterRight : coloringEdge 12 coloring 1 right = true) :
    coloringEdge 12 coloring left right = false := by
  cases hedge : coloringEdge 12 coloring left right with
  | false => rfl
  | true =>
      exfalso
      apply hfree.1 [0, 1, left, right]
      · simp
      · intro vertex hvertex
        simp at hvertex
        rcases hvertex with rfl | rfl | rfl | rfl <;> omega
      · simp
        omega
      · intro first second hfirst hsecond hlt
        simp at hfirst hsecond
        rcases hfirst with rfl | rfl | rfl | rfl <;>
          rcases hsecond with rfl | rfl | rfl | rfl <;>
          simp_all [coloringEdge] <;> omega

theorem pValue_le_three
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 8) :
    pValue coloring ≤ 3 := by
  by_cases hbound : pValue coloring ≤ 3
  · exact hbound
  exfalso
  have hp : 4 ≤ pValue coloring := by omega
  let normalized := twoCenterColoring coloring
  have hnormalizedFree : isRamseyFree 12 4 4 normalized := by
    have hrootFree : isRamseyFree 12 4 4 (rootSortedColoring coloring) :=
      (rootSort_isRamseyFree_iff coloring).mp hfree
    exact (secondSort_isRamseyFree_iff
      (rootSortedColoring coloring)).mp hrootFree
  have hrootCenter : coloringEdge 12 normalized 0 1 = true :=
    twoCenter_root_one coloring hdegree
  have hrootTwo : coloringEdge 12 normalized 0 2 = true :=
    twoCenter_root_left coloring hdegree (0 : Fin 7)
  have hrootThree : coloringEdge 12 normalized 0 3 = true :=
    twoCenter_root_left coloring hdegree (1 : Fin 7)
  have hrootFour : coloringEdge 12 normalized 0 4 = true :=
    twoCenter_root_left coloring hdegree (2 : Fin 7)
  have hrootFive : coloringEdge 12 normalized 0 5 = true :=
    twoCenter_root_left coloring hdegree (3 : Fin 7)
  have hcenterTwo : coloringEdge 12 normalized 1 2 = true := by
    dsimp [normalized]
    have hlt : 0 < pValue coloring := by omega
    simpa [hlt] using twoCenter_second_left coloring (0 : Fin 7)
  have hcenterThree : coloringEdge 12 normalized 1 3 = true := by
    dsimp [normalized]
    have hlt : 1 < pValue coloring := by omega
    simpa [hlt] using twoCenter_second_left coloring (1 : Fin 7)
  have hcenterFour : coloringEdge 12 normalized 1 4 = true := by
    dsimp [normalized]
    have hlt : 2 < pValue coloring := by omega
    simpa [hlt] using twoCenter_second_left coloring (2 : Fin 7)
  have hcenterFive : coloringEdge 12 normalized 1 5 = true := by
    dsimp [normalized]
    have hlt : 3 < pValue coloring := by omega
    have hedge := twoCenter_second_left coloring ⟨3, by omega⟩
    change coloringEdge 12 (twoCenterColoring coloring) 1 5 =
      decide (3 < pValue coloring) at hedge
    simpa [hlt] using hedge
  have h23 := common_positive_pair_false hnormalizedFree 2 3
    (by omega) (by omega) (by omega) hrootCenter hrootTwo hrootThree
    hcenterTwo hcenterThree
  have h24 := common_positive_pair_false hnormalizedFree 2 4
    (by omega) (by omega) (by omega) hrootCenter hrootTwo hrootFour
    hcenterTwo hcenterFour
  have h25 := common_positive_pair_false hnormalizedFree 2 5
    (by omega) (by omega) (by omega) hrootCenter hrootTwo hrootFive
    hcenterTwo hcenterFive
  have h34 := common_positive_pair_false hnormalizedFree 3 4
    (by omega) (by omega) (by omega) hrootCenter hrootThree hrootFour
    hcenterThree hcenterFour
  have h35 := common_positive_pair_false hnormalizedFree 3 5
    (by omega) (by omega) (by omega) hrootCenter hrootThree hrootFive
    hcenterThree hcenterFive
  have h45 := common_positive_pair_false hnormalizedFree 4 5
    (by omega) (by omega) (by omega) hrootCenter hrootFour hrootFive
    hcenterFour hcenterFive
  apply hnormalizedFree.2 [2, 3, 4, 5]
  · simp
  · simp
  · decide
  · intro first second hfirst hsecond hlt
    simp at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl | rfl <;>
      rcases hsecond with rfl | rfl | rfl | rfl <;>
      simp_all [coloringEdge]

theorem leftCountOf_semantic (coloring : Nat → Bool) :
    leftCountOf coloring =
      (List.finRange 7).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 2) := by
  unfold leftCountOf leftCount
  apply List.countP_congr
  intro position hposition
  rw [leftPatternColor_secondPattern coloring position]

theorem rightCountOf_semantic (coloring : Nat → Bool) :
    rightCountOf coloring =
      (List.finRange 3).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 9) := by
  unfold rightCountOf rightCount
  apply List.countP_congr
  intro position hposition
  rw [rightPatternColor_secondPattern coloring position]

theorem otherVertices_one_eq :
    otherVertices (1 : Fin 12) =
      0 :: (List.finRange 10).map (fun position => position.val + 2) := by
  native_decide

theorem tenVertices_split :
    (List.finRange 10).map (fun position => position.val + 2) =
      (List.finRange 7).map (fun position => position.val + 2) ++
      (List.finRange 3).map (fun position => position.val + 9) := by
  native_decide

theorem mappedLeft_count (coloring : Nat → Bool) :
    (List.finRange 7).countP
        ((fun vertex =>
          LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 12 coloring (1 : Fin 12).val vertex) ∘
          fun position : Fin 7 => position.val + 2) =
      (List.finRange 7).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 2) := by
  apply List.countP_congr
  intro position hposition
  have hlt : 1 < position.val + 2 := by omega
  simp [LRATCatcher.Tests.R55DegreeBounds.ramseyEdge,
    coloringEdge, hlt]

theorem mappedRight_count (coloring : Nat → Bool) :
    (List.finRange 3).countP
        ((fun vertex =>
          LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 12 coloring (1 : Fin 12).val vertex) ∘
          fun position : Fin 3 => position.val + 9) =
      (List.finRange 3).countP fun position =>
        coloringEdge 12 coloring 1 (position.val + 9) := by
  apply List.countP_congr
  intro position hposition
  have hlt : 1 < position.val + 9 := by omega
  simp [LRATCatcher.Tests.R55DegreeBounds.ramseyEdge,
    coloringEdge, hlt]

theorem center_positive_degree_eq (coloring : Nat → Bool)
    (hrootCenter : coloringEdge 12 coloring 0 1 = true) :
    (positiveNeighbors coloring (1 : Fin 12)).length =
      1 + leftCountOf coloring + rightCountOf coloring := by
  rw [leftCountOf_semantic, rightCountOf_semantic]
  have hrootEdge :
      LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 12 coloring 1 0 = true := by
    simpa [LRATCatcher.Tests.R55DegreeBounds.ramseyEdge, coloringEdge] using
      hrootCenter
  unfold positiveNeighbors
  rw [← List.countP_eq_length_filter]
  rw [otherVertices_one_eq, tenVertices_split]
  simp only [List.countP_cons, List.countP_append, List.countP_map]
  rw [mappedLeft_count, mappedRight_count]
  simp [hrootEdge]
  omega
/-- Exact semantic counterpart of the root and second-centre unit clauses
emitted by `generate_two_center_branches.py`. -/
def TwoCenterBranch (coloring : Nat → Bool) (p q : Nat) : Prop :=
  coloringEdge 12 coloring 0 1 = true ∧
  (∀ position : Fin 7,
    coloringEdge 12 coloring 0 (position.val + 2) = true) ∧
  (∀ position : Fin 3,
    coloringEdge 12 coloring 0 (position.val + 9) = false) ∧
  (∀ position : Fin 7,
    coloringEdge 12 coloring 1 (position.val + 2) =
      decide (position.val < p)) ∧
  (∀ position : Fin 3,
    coloringEdge 12 coloring 1 (position.val + 9) =
      decide (position.val < q))

theorem twoCenter_branch (coloring : Nat → Bool)
    (hdegree : positiveRootDegree coloring = 8) :
    TwoCenterBranch (twoCenterColoring coloring)
      (pValue coloring) (qValue coloring) := by
  exact ⟨twoCenter_root_one coloring hdegree,
    twoCenter_root_left coloring hdegree,
    twoCenter_root_right coloring hdegree,
    twoCenter_second_left coloring,
    twoCenter_second_right coloring⟩

/-- The case list is intentionally written in the frozen generator order. -/
def ThirteenCases (p q : Nat) : Prop :=
  (p = 0 ∧ q = 2) ∨
  (p = 0 ∧ q = 3) ∨
  (p = 1 ∧ q = 1) ∨
  (p = 1 ∧ q = 2) ∨
  (p = 1 ∧ q = 3) ∨
  (p = 2 ∧ q = 0) ∨
  (p = 2 ∧ q = 1) ∨
  (p = 2 ∧ q = 2) ∨
  (p = 2 ∧ q = 3) ∨
  (p = 3 ∧ q = 0) ∨
  (p = 3 ∧ q = 1) ∨
  (p = 3 ∧ q = 2) ∨
  (p = 3 ∧ q = 3)

theorem thirteenCases_of_bounds {p q : Nat}
    (hp : p ≤ 3) (hq : q ≤ 3) (hpq : 2 ≤ p + q) :
    ThirteenCases p q := by
  unfold ThirteenCases
  omega
theorem twoCenter_case_bounds
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 8) :
    pValue coloring ≤ 3 ∧ qValue coloring ≤ 3 ∧
      2 ≤ pValue coloring + qValue coloring := by
  have hrootFree : isRamseyFree 12 4 4 (rootSortedColoring coloring) :=
    (rootSort_isRamseyFree_iff coloring).mp hfree
  have hminimum := positiveDegree_ge_three hrootFree (1 : Fin 12)
  have hrootCenter :
      coloringEdge 12 (rootSortedColoring coloring) 0 1 = true := by
    simpa [rootSortedColoring] using
      rootSort_exact_eight coloring hdegree (0 : Fin 11)
  have hdegreeCenter := center_positive_degree_eq
    (rootSortedColoring coloring) hrootCenter
  change (positiveNeighbors (rootSortedColoring coloring) (1 : Fin 12)).length =
    1 + pValue coloring + qValue coloring at hdegreeCenter
  refine ⟨pValue_le_three hfree hdegree, qValue_le_three coloring, ?_⟩
  omega

theorem twoCenter_isRamseyFree_iff (coloring : Nat → Bool) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4 (twoCenterColoring coloring) := by
  rw [twoCenterColoring_eq_single_permutation]
  exact isRamseyFree_permute_iff (twoCenterPermutation coloring) coloring

theorem twoCenter_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat → Bool) (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (twoCenterColoring coloring) motif := by
  rw [twoCenterColoring_eq_single_permutation]
  exact inducedMotifOccurrence_permute_iff
    (twoCenterPermutation coloring) coloring motif

theorem exists_twoCenter_case_permutation
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 8)
    (motifOrder : Nat) (motif : Graph) :
    ∃ (permutation : FinPermutation 12) (p q : Nat),
      permutation (0 : Vertex) = 0 ∧
      p ≤ 3 ∧ q ≤ 3 ∧ 2 ≤ p + q ∧
      ThirteenCases p q ∧
      TwoCenterBranch (permuteColoring permutation coloring) p q ∧
      (isRamseyFree 12 4 4 coloring ↔
        isRamseyFree 12 4 4 (permuteColoring permutation coloring)) ∧
      (InducedMotifOccurrence motifOrder coloring motif ↔
        InducedMotifOccurrence motifOrder
          (permuteColoring permutation coloring) motif) := by
  obtain ⟨hp, hq, hpq⟩ := twoCenter_case_bounds hfree hdegree
  have hcases := thirteenCases_of_bounds hp hq hpq
  have hbranch := twoCenter_branch coloring hdegree
  rw [twoCenterColoring_eq_single_permutation] at hbranch
  refine ⟨twoCenterPermutation coloring, pValue coloring, qValue coloring,
    twoCenterPermutation_zero coloring, hp, hq, hpq, hcases, hbranch, ?_, ?_⟩
  · exact isRamseyFree_permute_iff (twoCenterPermutation coloring) coloring
  · exact inducedMotifOccurrence_permute_iff
      (twoCenterPermutation coloring) coloring motif
#print axioms rootSort_exact_eight
#print axioms pValue_le_three
#print axioms twoCenter_branch
#print axioms thirteenCases_of_bounds
#print axioms twoCenter_case_bounds
#print axioms exists_twoCenter_case_permutation

end LRATCatcher.Tests.R44OrderTwelveTwoCenterCases
