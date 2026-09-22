import LRATCatcher.Tests.R44RootedDegreeSplit
import LRATCatcher.Tests.R44RootedCanonicalRelabeling
import LRATCatcher.Tests.R44RootedMixedCNFSemantics
import LRATCatcher.Tests.R44RootedGen4416Cover
import LRATCatcher.Tests.R44RootedGraphReduction

/-!
  # Classification of `R(4,4,16)` colorings by `gen4416`

  This module composes the semantic root split, canonical relabeling, the
  certified local-clause classifier, and the checked two-graph cover.
-/

namespace LRATCatcher.Tests.R44Gen4416Classification

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44RootedDegreeSplit
open LRATCatcher.Tests.R44RootedBlockCatalogues
open LRATCatcher.Tests.R44RootedCanonicalRelabeling
open LRATCatcher.Tests.R44RootedGen4416Semantics
open LRATCatcher.Tests.R44RootedMixedClauses
open LRATCatcher.Tests.R44RootedMixedCNFSemantics
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-! ## Semantic converse and color-complement transport -/

/-- The packed-graph semantic predicate recovers Ramsey freeness of the
coloring from which the graph was built. -/
theorem isRamseyFree_of_coloringGraph_r44_validAt
    (order : Nat) (coloring : Nat → Bool)
    (hvalid : R44GraphValidAt order (coloringGraph order coloring)) :
    isRamseyFree order 4 4 coloring := by
  constructor
  · intro vertices hlength hbound hnodup hall
    apply hvalid.2.1 vertices hlength hbound hnodup
    intro left hleft right hright hne
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩]
    rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
    · simpa [coloringEdge, hordered] using
        hall left right hleft hright hordered
    · rw [coloringEdge_comm]
      simpa [coloringEdge, hreverse] using
        hall right left hright hleft hreverse
  · intro vertices hlength hbound hnodup hall
    apply hvalid.2.2 vertices hlength hbound hnodup
    intro left hleft right hright hne
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    change Bool.not (edge (coloringGraph order coloring) left right) = true
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩]
    rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
    · have hedge := hall left right hleft hright hordered
      simpa [coloringEdge, hordered, hedge]
    · rw [coloringEdge_comm]
      have hedge := hall right left hright hleft hreverse
      simpa [coloringEdge, hreverse, hedge]

theorem coloringEdge_complementColoring_of_ne
    (order : Nat) (coloring : Nat → Bool) (left right : Nat)
    (hne : left ≠ right) :
    coloringEdge order (complementColoring coloring) left right =
      !(coloringEdge order coloring left right) := by
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hnotReverse : ¬ right < left := by omega
    simp [coloringEdge, complementColoring, hordered, hnotReverse]
  · have hnotOrdered : ¬ left < right := by omega
    simp [coloringEdge, complementColoring, hreverse, hnotOrdered]

/-- Complement both sides of a strong isomorphism whose source is already
the complemented source coloring.  Loops are handled separately because
packed coloring graphs remain loop-free under color exchange. -/
theorem complementColoringGraph_isomorphic
    (sourceColoring targetColoring : Nat → Bool)
    (hisomorphic : GraphIsomorphicFin
      (coloringGraph 16 (complementColoring sourceColoring))
      (coloringGraph 16 targetColoring)) :
    GraphIsomorphicFin
      (coloringGraph 16 sourceColoring)
      (coloringGraph 16 (complementColoring targetColoring)) := by
  obtain ⟨isomorphism⟩ := hisomorphic
  rcases isomorphism with
    ⟨isoOrder, sourceOrder, targetOrder, permutation, mapEdge⟩
  have horder : isoOrder = 16 := by
    calc
      isoOrder =
          (coloringGraph 16
            (complementColoring sourceColoring)).length :=
        sourceOrder.symm
      _ = 16 := coloringGraph_length 16 _
  subst isoOrder
  refine ⟨{
    order := 16
    sourceOrder := coloringGraph_length 16 sourceColoring
    targetOrder := coloringGraph_length 16
      (complementColoring targetColoring)
    permutation := permutation
    map_edge := ?_
  }⟩
  intro left right
  by_cases hequal : left = right
  · subst right
    simp [edge_coloringGraph]
  · have htargetNe :
        permutation left ≠ permutation right :=
      fun h => hequal (FinPermutation.injective permutation h)
    have hmap := mapEdge left right
    rw [edge_coloringGraph, edge_coloringGraph] at hmap ⊢
    rw [coloringEdge_complementColoring_of_ne
      16 sourceColoring left.val right.val
      (fun h => hequal (Fin.ext h))] at hmap
    rw [coloringEdge_complementColoring_of_ne
      16 targetColoring
      (permutation left).val
      (permutation right).val
      (fun h => htargetNe (Fin.ext h))]
    simpa using congrArg Bool.not hmap

set_option maxHeartbeats 0 in
theorem originalGraph_to_complementGen4416
    (coloring : Nat → Bool) (targetIndex : Nat)
    (hisomorphic : GraphIsomorphicFin
      (coloringGraph 16 (complementColoring coloring))
      (gen4416Graph targetIndex)) :
    GraphIsomorphicFin (coloringGraph 16 coloring)
      (complementGen4416Graph targetIndex) := by
  have htarget : GraphIsomorphicFin
      (coloringGraph 16 (complementColoring coloring))
      (coloringGraph 16
        (ternaryColoring (gen4416GraphIds.getD targetIndex 0))) := by
    simpa [gen4416Graph] using hisomorphic
  have hcomplement := complementColoringGraph_isomorphic
    coloring
    (ternaryColoring (gen4416GraphIds.getD targetIndex 0))
    htarget
  simpa [complementGen4416Graph, complementColoring] using hcomplement

/-! ## Canonical semantic transport and model identification -/

theorem witness_leftIndex_lt_nine
    {coloring : Nat → Bool} (data : RootBlockCatalogueWitness coloring) :
    data.leftIndex < 9 := by
  simpa only [r34Catalogue7_length_eq_nine] using data.leftIndexBound

theorem witness_antiIndex_lt_three
    {coloring : Nat → Bool} (data : RootBlockCatalogueWitness coloring) :
    data.antiIndex < 3 := by
  simpa only [r34Catalogue8_length_eq_three] using data.antiIndexBound

/-- Ramsey freeness crosses the checked canonical-to-oriented graph
isomorphism. -/
theorem witness_canonicalColoring_isRamseyFree
    {coloring : Nat → Bool} (data : RootBlockCatalogueWitness coloring) :
    isRamseyFree 16 4 4
      (canonicalColoring data.leftIndex data.antiIndex (crossMask data)) := by
  have horientedValid : R44GraphValidAt 16
      (coloringGraph 16 (orientedColoring coloring data.flip)) :=
    coloringGraph_r44_validAt 16
      (orientedColoring coloring data.flip) data.orientedFree
  have hcanonicalValid : R44GraphValidAt 16
      (coloringGraph 16
        (canonicalColoring data.leftIndex data.antiIndex (crossMask data))) := by
    exact (r44GraphValidAt_iff_of_graphIsoFin
      (canonicalToOrientedGraphIso data)
      (coloringGraph_wellFormed 16
        (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
      (coloringGraph_wellFormed 16
        (orientedColoring coloring data.flip))).mpr horientedValid
  exact isRamseyFree_of_coloringGraph_r44_validAt 16
    (canonicalColoring data.leftIndex data.antiIndex (crossMask data))
    hcanonicalValid

/-- Matching selectors and all 56 cross bits identify the graph returned by
the LRAT table with the canonical relabeling graph. -/
theorem rootedModelGraph_eq_witness_canonicalGraph
    {coloring : Nat → Bool} (data : RootBlockCatalogueWitness coloring)
    (model : AllowedModel)
    (hleft : model.leftSelector = data.leftIndex)
    (hanti : model.antiSelector = data.antiIndex)
    (hbits : ∀ bit, bit < 56 →
      maskBit model.mask bit = maskBit (crossMask data) bit) :
    rootedModelGraph model =
      coloringGraph 16
        (canonicalColoring data.leftIndex data.antiIndex (crossMask data)) := by
  have hequal := canonicalGraph_eq_of_maskBits_eq
    data.leftIndex data.antiIndex model.mask (crossMask data) hbits
  simpa [rootedModelGraph, canonicalGraph, hleft, hanti] using hequal


/-! ## End-to-end classification -/

/-- Every `R(4,4)`-free coloring on sixteen vertices is strongly isomorphic
to one of the two checked `gen4416` target graphs. -/
theorem ramseyFree_isomorphic_to_gen4416
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 16 4 4 coloring) :
    ∃ targetIndex,
      targetIndex < gen4416GraphIds.length ∧
        GraphIsomorphicFin (coloringGraph 16 coloring)
          (gen4416Graph targetIndex) := by
  have hsplit : OrientedRootSplit coloring := exists_orientedRootSplit hfree
  obtain ⟨data, _hmaskBound, hcanonicalOriented⟩ :=
    orientedRootSplit_has_canonical_relabeling hsplit
  have hleft := witness_leftIndex_lt_nine data
  have hanti := witness_antiIndex_lt_three data
  have hcanonicalFree := witness_canonicalColoring_isRamseyFree data
  have hmixed :
      MixedR44Valid data.leftIndex data.antiIndex (crossMask data) :=
    ramseyFree_mixedR44Valid data.leftIndex data.antiIndex (crossMask data)
      hleft hanti hcanonicalFree
  obtain ⟨model, hmodel, hmodelLeft, hmodelAnti, hbits⟩ :=
    selectedAssignment_forces_allowed_row
      data.leftIndex data.antiIndex (crossMask data) hleft hanti hmixed

  obtain ⟨targetIndex, htarget, hmodelTarget⟩ :=
    allowed_model_covered model hmodel
  have hmodelCanonical :
      rootedModelGraph model =
        coloringGraph 16
          (canonicalColoring data.leftIndex data.antiIndex (crossMask data)) :=
    rootedModelGraph_eq_witness_canonicalGraph data model
      hmodelLeft hmodelAnti hbits

  have hcanonicalTarget : GraphIsomorphicFin
      (coloringGraph 16
        (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
      (gen4416Graph targetIndex) := by
    rw [← hmodelCanonical]
    exact hmodelTarget
  have horientedTarget : GraphIsomorphicFin
      (coloringGraph 16 (orientedColoring coloring data.flip))
      (gen4416Graph targetIndex) :=
    GraphIsomorphicFin.trans
      (GraphIsomorphicFin.symm hcanonicalOriented) hcanonicalTarget

  refine ⟨targetIndex, htarget, ?_⟩
  cases hflip : data.flip
  case false =>
    simpa [orientedColoring, hflip] using horientedTarget
  case true =>
    have hcomplementTarget : GraphIsomorphicFin
        (coloringGraph 16 (complementColoring coloring))
        (gen4416Graph targetIndex) := by
      simpa [orientedColoring, hflip] using horientedTarget
    exact GraphIsomorphicFin.trans
      (originalGraph_to_complementGen4416 coloring targetIndex
        hcomplementTarget)
      (gen4416_self_complementary targetIndex htarget)

#print axioms ramseyFree_isomorphic_to_gen4416

end LRATCatcher.Tests.R44Gen4416Classification
