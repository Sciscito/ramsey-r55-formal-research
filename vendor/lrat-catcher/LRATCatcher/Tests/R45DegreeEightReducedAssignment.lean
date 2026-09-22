import LRATCatcher.Tests.R45DegreeEightPilotSemantics
import LRATCatcher.Tests.R45DegreeReduction

/-!
  # The canonical degree-eight assignment on the non-root `K_24`

  A permutation of `Fin 25` puts the root at label zero, its eight red
  neighbours at labels `1,...,8`, and its sixteen blue neighbours at labels
  `9,...,24`.  This module removes the root and transports the ambient
  coloring to the exact `edgeVar 24` convention used by the certified pilot
  leaf.

  The three semantic obligations consumed by
  `no_l22r01_reduced_assignment` are proved directly:

  * the restriction remains `(4,5)`-free;
  * the first block has no red triangle, since adjoining the root would give
    a red `K4`;
  * the second block has no blue `K4`, since adjoining the root would give a
    blue `K5`.
-/

namespace LRATCatcher.Tests.R45DegreeEightReducedAssignment

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-- Ambient vertices at canonical labels `1,...,24`. -/
def nonRootEmbedding (permutation : FinPermutation 25) : Fin 24 -> Fin 25 :=
  fun index => permutation ⟨index.val + 1, by omega⟩

theorem nonRootEmbedding_injective (permutation : FinPermutation 25) :
    Function.Injective (nonRootEmbedding permutation) := by
  intro left right hequal
  apply Fin.ext
  have hpreimage :
      (⟨left.val + 1, by omega⟩ : Fin 25) =
        ⟨right.val + 1, by omega⟩ := by
    apply FinPermutation.injective permutation
    simpa [nonRootEmbedding] using hequal
  have hvalues := congrArg Fin.val hpreimage
  exact Nat.add_right_cancel hvalues

/-- The order-24 finite decoder round-trips the repository's edge indexing. -/
theorem localEdgePair_edgeVar_twentyFour (left right : Fin 24)
    (hordered : left < right) :
    localEdgePair 24 (edgeVar 24 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Pull the ambient coloring back along canonical labels `1,...,24`. -/
def reducedAssignment (permutation : FinPermutation 25)
    (coloring : Nat -> Bool) : Nat -> Bool :=
  inducedColoring 24 (nonRootEmbedding permutation) coloring false

theorem reducedAssignment_edgeVar (permutation : FinPermutation 25)
    (coloring : Nat -> Bool) (left right : Fin 24)
    (hordered : left < right) :
    reducedAssignment permutation coloring
        (edgeVar 24 left.val right.val) =
      ramseyEdge 25 coloring
        (nonRootEmbedding permutation left).val
        (nonRootEmbedding permutation right).val := by
  simpa [reducedAssignment] using
    inducedColoring_edgeVar (nonRootEmbedding permutation) coloring false
      localEdgePair_edgeVar_twentyFour left right hordered

/-- Canonical degree-eight root data after an ambient relabeling. -/
structure CanonicalDegreeEightRoot (coloring : Nat -> Bool)
    (root : Fin 25) (permutation : FinPermutation 25) : Prop where
  root_eq : permutation (0 : Fin 25) = root
  firstEightRed : forall index : Fin 8,
    ramseyEdge 25 coloring root.val
      (permutation ⟨index.val + 1, by omega⟩).val = true
  lastSixteenBlue : forall index : Fin 16,
    ramseyEdge 25 coloring root.val
      (permutation ⟨index.val + 9, by omega⟩).val = false

theorem canonical_root_ne_nonRoot
    {coloring : Nat -> Bool} {root : Fin 25}
    {permutation : FinPermutation 25}
    (canonical : CanonicalDegreeEightRoot coloring root permutation)
    (index : Fin 24) :
    root.val ≠ (nonRootEmbedding permutation index).val := by
  intro hequal
  have hvertices : root = nonRootEmbedding permutation index :=
    Fin.ext hequal
  have himages :
      permutation (0 : Fin 25) =
        permutation ⟨index.val + 1, by omega⟩ := by
    simpa [nonRootEmbedding] using canonical.root_eq.trans hvertices
  have hpreimage := FinPermutation.injective permutation himages
  have hvalues := congrArg Fin.val hpreimage
  simpa using hvalues

/-! ## The full non-root restriction -/

theorem reducedAssignment_isRamseyFree
    {coloring : Nat -> Bool} (permutation : FinPermutation 25)
    (hfree : isRamseyFree 25 4 5 coloring) :
    isRamseyFree 24 4 5 (reducedAssignment permutation coloring) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let embedding := nonRootEmbedding permutation
    let mapped := vertices.map (R45DegreeReduction.embedNat embedding)
    have hinjective : Function.Injective embedding := by
      simpa [embedding] using nonRootEmbedding_injective permutation
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound :
        forall vertex, vertex ∈ mapped -> vertex < 25 := by
      exact mapped_bound embedding hbound
    have hlocal := local_true_related embedding coloring false (by
      simpa [embedding, reducedAssignment] using hall)
    have hmapped := mapped_true_related embedding coloring false
      localEdgePair_edgeVar_twentyFour hbound hlocal
    have hmappedRed :
        R55DegreeBounds.AllDistinctRelated (ramseyEdge 25 coloring) mapped := by
      simpa using hmapped
    apply hfree.1 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedRed left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge
  · intro vertices hlength hbound hnodup hall
    let embedding := nonRootEmbedding permutation
    let mapped := vertices.map (R45DegreeReduction.embedNat embedding)
    have hinjective : Function.Injective embedding := by
      simpa [embedding] using nonRootEmbedding_injective permutation
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound :
        forall vertex, vertex ∈ mapped -> vertex < 25 := by
      exact mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring false (by
      simpa [embedding, reducedAssignment] using hall)
    have hmapped := mapped_false_related embedding coloring false
      localEdgePair_edgeVar_twentyFour hbound hlocal
    have hmappedBlue :
        R55DegreeBounds.AllDistinctRelated
          (fun left right => !(ramseyEdge 25 coloring left right))
          mapped := by
      simpa using hmapped
    apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedBlue left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge

/-! ## Root-induced local exclusions -/

theorem canonical_noRedTriangleLeft
    {coloring : Nat -> Bool} {root : Fin 25}
    {permutation : FinPermutation 25}
    (hfree : isRamseyFree 25 4 5 coloring)
    (canonical : CanonicalDegreeEightRoot coloring root permutation) :
    NoRedTriangleLeft (reducedAssignment permutation coloring) := by
  intro vertices hlength hbound hnodup hall
  let embedding := nonRootEmbedding permutation
  let mapped := vertices.map (R45DegreeReduction.embedNat embedding)
  let forbidden := root.val :: mapped
  have hinjective : Function.Injective embedding := by
    simpa [embedding] using nonRootEmbedding_injective permutation
  have hmappedNodup : mapped.Nodup := by
    exact mapped_nodup embedding hinjective hnodup
  have hmappedBound : forall vertex, vertex ∈ mapped -> vertex < 25 := by
    apply mapped_bound embedding
    intro vertex hvertex
    exact Nat.lt_trans (hbound vertex hvertex) (by omega)
  have hrootNotMapped : root.val ∉ mapped := by
    intro hmem
    obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
    have hindexBound : index < 24 :=
      Nat.lt_trans (hbound index hindex) (by omega)
    have hequal' :
        root.val = (embedding ⟨index, hindexBound⟩).val := by
      simpa [R45DegreeReduction.embedNat, hindexBound] using hequal.symm
    exact canonical_root_ne_nonRoot canonical
      ⟨index, hindexBound⟩ hequal'
  have hforbiddenLength : forbidden.length = 4 := by
    simp [forbidden, mapped, hlength]
  have hforbiddenBound :
      forall vertex, vertex ∈ forbidden -> vertex < 25 := by
    intro vertex hvertex
    simp only [forbidden, List.mem_cons] at hvertex
    rcases hvertex with rfl | hvertex
    · exact root.isLt
    · exact hmappedBound vertex hvertex
  have hforbiddenNodup : forbidden.Nodup := by
    simp only [forbidden, List.nodup_cons]
    exact ⟨hrootNotMapped, hmappedNodup⟩
  have hlocal := local_true_related embedding coloring false (by
    simpa [embedding, reducedAssignment] using hall)
  have hmapped := mapped_true_related embedding coloring false
    localEdgePair_edgeVar_twentyFour
    (fun vertex hvertex =>
      Nat.lt_trans (hbound vertex hvertex) (by omega)) hlocal
  have hmappedRed :
      R55DegreeBounds.AllDistinctRelated (ramseyEdge 25 coloring) mapped := by
    simpa using hmapped
  have hforbiddenRed :
      R55DegreeBounds.AllDistinctRelated (ramseyEdge 25 coloring) forbidden := by
    apply allDistinctRelated_cons
    · exact ramseyEdge_comm 25 coloring
    · exact hmappedRed
    · intro vertex hvertex
      obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
      have hindexEight := hbound index hindex
      have hindexTwentyFour : index < 24 := by omega
      rw [R45DegreeReduction.embedNat_of_lt embedding hindexTwentyFour]
      simpa [embedding, nonRootEmbedding] using
        canonical.firstEightRed ⟨index, hindexEight⟩
  apply hfree.1 forbidden hforbiddenLength hforbiddenBound
    hforbiddenNodup
  intro left right hleft hright hordered
  have hedge := hforbiddenRed left hleft right hright
    (Nat.ne_of_lt hordered)
  simpa [ramseyEdge, hordered] using hedge

theorem canonical_noBlueFourRight
    {coloring : Nat -> Bool} {root : Fin 25}
    {permutation : FinPermutation 25}
    (hfree : isRamseyFree 25 4 5 coloring)
    (canonical : CanonicalDegreeEightRoot coloring root permutation) :
    NoBlueFourRight (reducedAssignment permutation coloring) := by
  intro vertices hlength hbound hnodup hall
  let embedding := nonRootEmbedding permutation
  let mapped := vertices.map (R45DegreeReduction.embedNat embedding)
  let forbidden := root.val :: mapped
  have hinjective : Function.Injective embedding := by
    simpa [embedding] using nonRootEmbedding_injective permutation
  have hlocalBound : forall vertex, vertex ∈ vertices -> vertex < 24 :=
    fun vertex hvertex => (hbound vertex hvertex).2
  have hmappedNodup : mapped.Nodup := by
    exact mapped_nodup embedding hinjective hnodup
  have hmappedBound : forall vertex, vertex ∈ mapped -> vertex < 25 := by
    exact mapped_bound embedding hlocalBound
  have hrootNotMapped : root.val ∉ mapped := by
    intro hmem
    obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
    have hindexBound := hlocalBound index hindex
    have hequal' :
        root.val = (embedding ⟨index, hindexBound⟩).val := by
      simpa [R45DegreeReduction.embedNat, hindexBound] using hequal.symm
    exact canonical_root_ne_nonRoot canonical
      ⟨index, hindexBound⟩ hequal'
  have hforbiddenLength : forbidden.length = 5 := by
    simp [forbidden, mapped, hlength]
  have hforbiddenBound :
      forall vertex, vertex ∈ forbidden -> vertex < 25 := by
    intro vertex hvertex
    simp only [forbidden, List.mem_cons] at hvertex
    rcases hvertex with rfl | hvertex
    · exact root.isLt
    · exact hmappedBound vertex hvertex
  have hforbiddenNodup : forbidden.Nodup := by
    simp only [forbidden, List.nodup_cons]
    exact ⟨hrootNotMapped, hmappedNodup⟩
  have hlocal := local_false_related embedding coloring false (by
    simpa [embedding, reducedAssignment] using hall)
  have hmapped := mapped_false_related embedding coloring false
    localEdgePair_edgeVar_twentyFour hlocalBound hlocal
  have hmappedBlue :
      R55DegreeBounds.AllDistinctRelated
        (fun left right => !(ramseyEdge 25 coloring left right)) mapped := by
    simpa using hmapped
  have hforbiddenBlue :
      R55DegreeBounds.AllDistinctRelated
        (fun left right => !(ramseyEdge 25 coloring left right))
        forbidden := by
    apply allDistinctRelated_cons
    · intro left right
      rw [ramseyEdge_comm 25 coloring left right]
    · exact hmappedBlue
    · intro vertex hvertex
      obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
      have hindexRange := hbound index hindex
      have hindexBound := hindexRange.2
      rw [R45DegreeReduction.embedNat_of_lt embedding hindexBound]
      let localIndex : Fin 16 := ⟨index - 8, by omega⟩
      have hinput :
          (⟨localIndex.val + 9, by omega⟩ : Fin 25) =
            ⟨index + 1, by omega⟩ := by
        apply Fin.ext
        simp only [localIndex, Fin.val_mk]
        omega
      have himage :
          permutation ⟨localIndex.val + 9, by omega⟩ =
            embedding ⟨index, hindexBound⟩ := by
        simpa [embedding, nonRootEmbedding] using congrArg permutation hinput
      have hedge := canonical.lastSixteenBlue localIndex
      rw [himage] at hedge
      simp [hedge]
  apply hfree.2 forbidden hforbiddenLength hforbiddenBound
    hforbiddenNodup
  intro left right hleft hright hordered
  have hedge := hforbiddenBlue left hleft right hright
    (Nat.ne_of_lt hordered)
  simpa [ramseyEdge, hordered] using hedge

/-! ## Package consumed by the certified leaf -/

/-- Exactly the three structural hypotheses needed before adding leaf units. -/
structure ReducedAssignmentSemantics (assignment : Nat -> Bool) : Prop where
  ramseyFree : isRamseyFree 24 4 5 assignment
  noRedTriangleLeft : NoRedTriangleLeft assignment
  noBlueFourRight : NoBlueFourRight assignment

theorem canonical_reducedAssignment_semantics
    {coloring : Nat -> Bool} {root : Fin 25}
    {permutation : FinPermutation 25}
    (hfree : isRamseyFree 25 4 5 coloring)
    (canonical : CanonicalDegreeEightRoot coloring root permutation) :
    ReducedAssignmentSemantics
      (reducedAssignment permutation coloring) where
  ramseyFree := reducedAssignment_isRamseyFree permutation hfree
  noRedTriangleLeft := canonical_noRedTriangleLeft hfree canonical
  noBlueFourRight := canonical_noBlueFourRight hfree canonical

/-- Once catalogue transport supplies the exact `l22/r01` units, the
certified pilot leaf closes the canonical degree-eight branch. -/
theorem no_l22r01_of_canonical_reducedAssignment
    {coloring : Nat -> Bool} {root : Fin 25}
    {permutation : FinPermutation 25}
    (hfree : isRamseyFree 25 4 5 coloring)
    (canonical : CanonicalDegreeEightRoot coloring root permutation)
    (hunits : AllUnitsSatisfied
      (reducedAssignment permutation coloring) l22r01Units) : False := by
  have semantics := canonical_reducedAssignment_semantics hfree canonical
  exact no_l22r01_reduced_assignment
    (reducedAssignment permutation coloring)
    semantics.ramseyFree
    semantics.noRedTriangleLeft
    semantics.noBlueFourRight
    hunits

#print axioms reducedAssignment_isRamseyFree
#print axioms canonical_noRedTriangleLeft
#print axioms canonical_noBlueFourRight
#print axioms no_l22r01_of_canonical_reducedAssignment

end LRATCatcher.Tests.R45DegreeEightReducedAssignment
