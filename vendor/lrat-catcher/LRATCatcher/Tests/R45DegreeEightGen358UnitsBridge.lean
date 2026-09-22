import LRATCatcher.Tests.R35CatalogGraphIsoBridge
import LRATCatcher.Tests.R45DegreeEightCover
import LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-!
  # Semantic `gen358` unit bridge for the degree-eight branch

  A `CoveredByGen358Parent` witness contains two relabelings with a common
  codomain: a strong isomorphism from the source graph to a completion and a
  checked list permutation from the parent labels to that completion.  This
  module turns the checked list into a `FinPermutation 8`, composes it with
  the inverse graph isomorphism, and exposes the resulting parent-to-source
  permutation together with the exact semantics of every fixed parent edge.

  Parent colour `1` means a true/red edge, colour `2` means a false/blue edge,
  and colour `0` is deliberately absent from the witness obligations.  This
  is the convention used by `gen358DirectUnits`.
-/

namespace LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-! ## Reading the checked parent-to-completion list -/

theorem parentCatalogueAgreement_length
    {parentId : Nat} {completion : Graph} {permutation : List Nat}
    (hagreement :
      parentCatalogueAgreement parentId completion permutation = true) :
    completion.length = 8 := by
  simp only [parentCatalogueAgreement, Bool.and_eq_true, beq_iff_eq] at hagreement
  simpa using hagreement.1.1

theorem parentCatalogueAgreement_isPermutation
    {parentId : Nat} {completion : Graph} {permutation : List Nat}
    (hagreement :
      parentCatalogueAgreement parentId completion permutation = true) :
    isPermutation permutation 8 = true := by
  simp only [parentCatalogueAgreement, Bool.and_eq_true, beq_iff_eq] at hagreement
  exact hagreement.1.2

theorem parentCatalogueAgreement_pairs
    {parentId : Nat} {completion : Graph} {permutation : List Nat}
    (hagreement :
      parentCatalogueAgreement parentId completion permutation = true) :
    (LRATCatcher.Ramsey.subsets 8 2).all (fun vertices =>
      match vertices with
      | [left, right] =>
          let colour := ternaryColourAt parentId left right
          colour == 0 ||
            ((colour == 1) ==
              edge completion
                (permutation.getD left 8)
                (permutation.getD right 8))
      | _ => false) = true := by
  simp only [parentCatalogueAgreement, Bool.and_eq_true, beq_iff_eq] at hagreement
  exact hagreement.2

theorem ternaryColourAt_comm (encoded left right : Nat) :
    ternaryColourAt encoded left right =
      ternaryColourAt encoded right left := by
  simp [ternaryColourAt, edgeIndex, Nat.min_comm, Nat.max_comm]

theorem parentCatalogueAgreement_fixed_true_of_gt
    {parentId : Nat} {completion : Graph} {permutation : List Nat}
    (hagreement :
      parentCatalogueAgreement parentId completion permutation = true)
    (high low : Fin 8) (hlow : low.val < high.val)
    (hcolour : ternaryColourAt parentId high.val low.val = 1) :
    edge completion
        (permutation.getD high.val 8)
        (permutation.getD low.val 8) = true := by
  have hpairs := List.all_eq_true.mp
    (parentCatalogueAgreement_pairs hagreement)
    [high.val, low.val]
    (ordered_pair_mem_subsets high.isLt hlow)
  simpa [hcolour] using hpairs

theorem parentCatalogueAgreement_fixed_false_of_gt
    {parentId : Nat} {completion : Graph} {permutation : List Nat}
    (hagreement :
      parentCatalogueAgreement parentId completion permutation = true)
    (high low : Fin 8) (hlow : low.val < high.val)
    (hcolour : ternaryColourAt parentId high.val low.val = 2) :
    edge completion
        (permutation.getD high.val 8)
        (permutation.getD low.val 8) = false := by
  have hpairs := List.all_eq_true.mp
    (parentCatalogueAgreement_pairs hagreement)
    [high.val, low.val]
    (ordered_pair_mem_subsets high.isLt hlow)
  simpa [hcolour] using hpairs

/-! ## Reindexing and composing the two relabelings -/

/-- Transport a finite permutation across an equality of its order. -/
def reindexPermutation {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder) :
    FinPermutation targetOrder := by
  subst targetOrder
  exact permutation

@[simp] theorem reindexPermutation_apply_val
    {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder)
    (vertex : Fin targetOrder) :
    (reindexPermutation horder permutation vertex).val =
      (permutation (Fin.cast horder.symm vertex)).val := by
  subst targetOrder
  rfl

/-- The precise semantic payload needed by the direct `gen358` unit cube.
The permutation sends a parent label to the corresponding source-graph
vertex.  Holes carry no obligation. -/
structure Gen358DirectUnitWitness (graph : Graph) (parentId : Nat) where
  permutation : FinPermutation 8
  fixed_true : ∀ left right : Fin 8, left ≠ right →
    ternaryColourAt parentId left.val right.val = 1 →
    edge graph (permutation left).val (permutation right).val = true
  fixed_false : ∀ left right : Fin 8, left ≠ right →
    ternaryColourAt parentId left.val right.val = 2 →
    edge graph (permutation left).val (permutation right).val = false

namespace Gen358DirectUnitWitness

/-- Combined fixed-colour form: on colours `1` and `2`, adjacency is exactly
the Boolean test for HOL colour `1`. -/
theorem fixed_edge {graph : Graph} {parentId : Nat}
    (witness : Gen358DirectUnitWitness graph parentId)
    (left right : Fin 8) (hne : left ≠ right)
    (hfixed : ternaryColourAt parentId left.val right.val = 1 ∨
      ternaryColourAt parentId left.val right.val = 2) :
    edge graph
        (witness.permutation left).val
        (witness.permutation right).val =
      (ternaryColourAt parentId left.val right.val == 1) := by
  rcases hfixed with htrue | hfalse
  · rw [witness.fixed_true left right hne htrue, htrue]
    decide
  · rw [witness.fixed_false left right hne hfalse, hfalse]
    decide

end Gen358DirectUnitWitness

/-- A well-formed order-eight graph covered by a `gen358` parent admits a concrete
parent-label-to-source permutation satisfying every fixed parent colour.
This is the reusable bridge from catalogue coverage to the one-literal
clauses emitted by `gen358DirectUnits`. -/
theorem coveredByGen358Parent_directUnitWitness
    {graph : Graph} {parentId : Nat}
    (hwellFormed : wellFormedGraph 8 graph = true)
    (hcovered : CoveredByGen358Parent graph parentId) :
    Nonempty (Gen358DirectUnitWitness graph parentId) := by
  obtain ⟨completion, ⟨isomorphism⟩, permutationList, hagreement⟩ := hcovered
  let hlistPermutation :=
    parentCatalogueAgreement_isPermutation hagreement
  let parentToCompletion : FinPermutation 8 :=
    listPermutationToFin permutationList 8 hlistPermutation
  have hisomorphismOrder : isomorphism.order = 8 := by
    calc
      isomorphism.order = completion.length := isomorphism.targetOrder.symm
      _ = 8 := parentCatalogueAgreement_length hagreement
  let sourceToCompletion : FinPermutation 8 :=
    reindexPermutation hisomorphismOrder isomorphism.permutation
  let parentToSource : FinPermutation 8 :=
    parentToCompletion.trans sourceToCompletion.symm
  have hmap (left right : Fin 8) :
      edge graph left.val right.val =
        edge completion
          (sourceToCompletion left).val
          (sourceToCompletion right).val := by
    have hedge := isomorphism.map_edge
      (Fin.cast hisomorphismOrder.symm left)
      (Fin.cast hisomorphismOrder.symm right)
    simpa [sourceToCompletion, hisomorphismOrder] using hedge
  have htransport (left right : Fin 8) :
      edge graph
          (parentToSource left).val
          (parentToSource right).val =
        edge completion
          (parentToCompletion left).val
          (parentToCompletion right).val := by
    have hedge := hmap
      (sourceToCompletion.symm (parentToCompletion left))
      (sourceToCompletion.symm (parentToCompletion right))
    simpa [parentToSource, FinPermutation.trans] using hedge
  have htrueOfGt (high low : Fin 8) (hlow : low.val < high.val)
      (hcolour : ternaryColourAt parentId high.val low.val = 1) :
      edge graph
          (parentToSource high).val
          (parentToSource low).val = true := by
    exact (htransport high low).trans (by
      simpa [parentToCompletion] using
        parentCatalogueAgreement_fixed_true_of_gt
          hagreement high low hlow hcolour)
  have hfalseOfGt (high low : Fin 8) (hlow : low.val < high.val)
      (hcolour : ternaryColourAt parentId high.val low.val = 2) :
      edge graph
          (parentToSource high).val
          (parentToSource low).val = false := by
    exact (htransport high low).trans (by
      simpa [parentToCompletion] using
        parentCatalogueAgreement_fixed_false_of_gt
          hagreement high low hlow hcolour)
  refine ⟨{
    permutation := parentToSource
    fixed_true := ?_
    fixed_false := ?_
  }⟩
  · intro left right hne hcolour
    have hvalues : left.val ≠ right.val := by
      intro hequal
      exact hne (Fin.ext hequal)
    rcases Nat.lt_or_gt_of_ne hvalues with hordered | hreverse
    · calc
        edge graph
            (parentToSource left).val
            (parentToSource right).val =
          edge graph
            (parentToSource right).val
            (parentToSource left).val :=
              wellFormedGraph_edge_comm hwellFormed
                (parentToSource left).isLt
                (parentToSource right).isLt
        _ = true := htrueOfGt right left hordered (by
          rw [ternaryColourAt_comm]
          exact hcolour)
    · exact htrueOfGt left right hreverse hcolour
  · intro left right hne hcolour
    have hvalues : left.val ≠ right.val := by
      intro hequal
      exact hne (Fin.ext hequal)
    rcases Nat.lt_or_gt_of_ne hvalues with hordered | hreverse
    · calc
        edge graph
            (parentToSource left).val
            (parentToSource right).val =
          edge graph
            (parentToSource right).val
            (parentToSource left).val :=
              wellFormedGraph_edge_comm hwellFormed
                (parentToSource left).isLt
                (parentToSource right).isLt
        _ = false := hfalseOfGt right left hordered (by
          rw [ternaryColourAt_comm]
          exact hcolour)
    · exact hfalseOfGt left right hreverse hcolour

/-! ## Exact literal-level unit semantics -/

/-- Every pair emitted by the concrete order-eight upperPairs list is
strictly ordered and in range. -/
theorem upperPairs_eight_ordered
    (pair : Nat × Nat) (hpair : pair ∈ upperPairs 8) :
    pair.1 < pair.2 ∧ pair.2 < 8 := by
  native_decide +revert

namespace Gen358DirectUnitWitness

/-- If an order-24 assignment reads its left block through the witness
permutation, then it satisfies exactly every fixed-color literal emitted by
gen358DirectUnits. Parent holes emit no literal and therefore create no
obligation. -/
theorem allUnitsSatisfied
    {graph : Graph} {parentIndex : Nat}
    (witness : Gen358DirectUnitWitness graph
      (gen358ParentIds.getD parentIndex 0))
    (assignment : Nat → Bool)
    (hassignment : ∀ left right : Fin 8, left < right →
      assignment (edgeVar 24 left.val right.val) =
        edge graph
          (witness.permutation left).val
          (witness.permutation right).val) :
    AllUnitsSatisfied assignment (gen358DirectUnits parentIndex) := by
  intro literal hliteral
  simp only [gen358DirectUnits, List.mem_filterMap] at hliteral
  obtain ⟨pair, hpair, hunit⟩ := hliteral
  obtain ⟨horderedNat, hright⟩ := upperPairs_eight_ordered pair hpair
  let left : Fin 8 := ⟨pair.1, by omega⟩
  let right : Fin 8 := ⟨pair.2, hright⟩
  have hordered : left < right := by
    simpa [left, right] using horderedNat
  let colour := ternaryColourAt
    (gen358ParentIds.getD parentIndex 0) pair.1 pair.2
  have hcolourLt : colour < 3 := by
    dsimp [colour]
    unfold ternaryColourAt
    exact Nat.mod_lt _ (by omega)
  have hcases : colour = 0 ∨ colour = 1 ∨ colour = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · have hzero' : ternaryColourAt
        (gen358ParentIds.getD parentIndex 0) pair.1 pair.2 = 0 := by
      simpa [colour] using hzero
    rw [hzero'] at hunit
    simp at hunit
  · have hequal : edgeUnit pair.1 pair.2 true = literal := by
      have hone' : ternaryColourAt
          (gen358ParentIds.getD parentIndex 0) pair.1 pair.2 = 1 := by
        simpa [colour] using hone
      rw [hone'] at hunit
      exact Option.some.inj hunit
    rw [← hequal]
    apply (edgeUnit_satisfied_iff assignment pair.1 pair.2 true).2
    calc
      assignment (edgeVar 24 pair.1 pair.2) =
          edge graph
            (witness.permutation left).val
            (witness.permutation right).val := by
        simpa [left, right] using hassignment left right hordered
      _ = true := witness.fixed_true left right (by omega) (by
        simpa [colour, left, right] using hone)
  · have hequal : edgeUnit pair.1 pair.2 false = literal := by
      have htwo' : ternaryColourAt
          (gen358ParentIds.getD parentIndex 0) pair.1 pair.2 = 2 := by
        simpa [colour] using htwo
      rw [htwo'] at hunit
      exact Option.some.inj hunit
    rw [← hequal]
    apply (edgeUnit_satisfied_iff assignment pair.1 pair.2 false).2
    calc
      assignment (edgeVar 24 pair.1 pair.2) =
          edge graph
            (witness.permutation left).val
            (witness.permutation right).val := by
        simpa [left, right] using hassignment left right hordered
      _ = false := witness.fixed_false left right (by omega) (by
        simpa [colour, left, right] using htwo)

end Gen358DirectUnitWitness

#print axioms Gen358DirectUnitWitness.allUnitsSatisfied
#print axioms coveredByGen358Parent_directUnitWitness

end LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge
