import LRATCatcher.Tests.R35UpperBound
import LRATCatcher.Tests.R44RootedR34Catalogue

/-!
  # Semantic graph interface for rooted `R(4,4)` reductions

  The exhaustive `R(3,5)` catalogue uses `GraphValidAt`, whose red obstruction
  is a triangle and whose blue obstruction has size five.  A rooted
  `R(4,4,16)` classification therefore needs a separate semantic interface:
  both forbidden configurations have size four.

  This module deliberately contains no classifier data.  It only connects
  Ramsey colorings, packed graphs, and the strong `GraphIsoFin` relation.
-/

namespace LRATCatcher.Tests.R44RootedGraphReduction

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedR34Catalogue

/-- Semantic exclusion of a clique of size four in a packed graph. -/
def NoCliqueFourAt (order : Nat) (graph : Graph) : Prop :=
  ∀ vertices,
    vertices.length = 4 →
    (∀ vertex ∈ vertices, vertex < order) →
    vertices.Nodup →
    ¬AllDistinctRelated (edge graph) vertices

/-- Semantic validity for an `R(4,4)` graph at a fixed order. -/
def R44GraphValidAt (order : Nat) (graph : Graph) : Prop :=
  wellFormedGraph order graph = true ∧
    NoCliqueFourAt order graph ∧
    NoIndependentFourAt order graph

/-! ## Transport along embeddings and finite graph isomorphisms -/

/-- Pulling vertices through an injective edge-preserving map transports the
absence of a clique of size four. -/
theorem noCliqueFourAt_of_embedding
    {order : Nat} {source target : Graph}
    (pull : Nat → Nat)
    (hpullBound : ∀ vertex, vertex < order → pull vertex < order)
    (hpullInjective : Function.Injective pull)
    (hpullEdge : ∀ left, left < order → ∀ right, right < order →
      edge source (pull left) (pull right) = edge target left right)
    (hsource : NoCliqueFourAt order source) :
    NoCliqueFourAt order target := by
  intro vertices hlength hbound hnodup hclique
  let pulled := vertices.map pull
  apply hsource pulled
  · simp [pulled, hlength]
  · intro vertex hvertex
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hvertex
    exact hpullBound original (hbound original horiginal)
  · exact hnodup.map pull
      (fun left right hne hequal => hne (hpullInjective hequal))
  · intro left hleft right hright hne
    obtain ⟨originalLeft, horiginalLeft, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨originalRight, horiginalRight, rfl⟩ := List.mem_map.mp hright
    rw [hpullEdge originalLeft (hbound originalLeft horiginalLeft)
      originalRight (hbound originalRight horiginalRight)]
    exact hclique originalLeft horiginalLeft originalRight horiginalRight
      (fun hequal => hne (congrArg pull hequal))

/-- Semantic clique-four exclusion is invariant under `GraphIsoFin`. -/
theorem noCliqueFourAt_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (hsource : NoCliqueFourAt isomorphism.order source) :
    NoCliqueFourAt isomorphism.order target := by
  refine noCliqueFourAt_of_embedding
    (source := source) (target := target)
    isomorphism.permutation.symm.applyNat ?_ ?_ ?_ hsource
  · exact fun vertex hvertex =>
      FinPermutation.applyNat_lt isomorphism.permutation.symm hvertex
  · exact FinPermutation.applyNat_injective isomorphism.permutation.symm
  · intro left hleft right hright
    have hedge := isomorphism.map_edge
      (isomorphism.permutation.symm ⟨left, hleft⟩)
      (isomorphism.permutation.symm ⟨right, hright⟩)
    rw [FinPermutation.applyNat_of_lt isomorphism.permutation.symm hleft,
      FinPermutation.applyNat_of_lt isomorphism.permutation.symm hright]
    simpa only [FinPermutation.apply_symm_apply] using hedge

/-- Directional transport of semantic `R(4,4)` validity.  Well-formedness of
the target is explicit because `GraphIsoFin` only records in-range adjacency
and cannot exclude stray packed bits outside the target order. -/
theorem r44GraphValidAt_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (htargetWellFormed :
      wellFormedGraph isomorphism.order target = true)
    (hsource : R44GraphValidAt isomorphism.order source) :
    R44GraphValidAt isomorphism.order target := by
  exact ⟨htargetWellFormed,
    noCliqueFourAt_of_graphIsoFin isomorphism hsource.2.1,
    noIndependentFourAt_of_graphIsoFin isomorphism hsource.2.2⟩

/-- With well-formedness supplied on both sides, `R(4,4)` validity is exactly
invariant under a finite graph isomorphism. -/
theorem r44GraphValidAt_iff_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (hsourceWellFormed :
      wellFormedGraph isomorphism.order source = true)
    (htargetWellFormed :
      wellFormedGraph isomorphism.order target = true) :
    R44GraphValidAt isomorphism.order source ↔
      R44GraphValidAt isomorphism.order target := by
  constructor
  · exact r44GraphValidAt_of_graphIsoFin isomorphism htargetWellFormed
  · intro htarget
    exact r44GraphValidAt_of_graphIsoFin isomorphism.symm
      hsourceWellFormed htarget

/-! ## Packing Ramsey colorings -/

/-- A semantic `(4,4)`-free coloring induces a semantically valid packed
`R(4,4)` graph. -/
theorem coloringGraph_r44_validAt
    (order : Nat) (coloring : Nat → Bool)
    (hfree : isRamseyFree order 4 4 coloring) :
    R44GraphValidAt order (coloringGraph order coloring) := by
  refine ⟨coloringGraph_wellFormed order coloring, ?_, ?_⟩
  · intro clique hlength hbound hnodup hclique
    apply hfree.1 clique hlength hbound hnodup
    intro left right hleft hright hordered
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    have hred := hclique left hleft right hright (Nat.ne_of_lt hordered)
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩] at hred
    simpa [coloringEdge, hordered] using hred
  · intro independent hlength hbound hnodup hindependent
    apply hfree.2 independent hlength hbound hnodup
    intro left right hleft hright hordered
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    have hblue := hindependent left hleft right hright
      (Nat.ne_of_lt hordered)
    change Bool.not
      (edge (coloringGraph order coloring) left right) = true at hblue
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩] at hblue
    simpa [coloringEdge, hordered] using hblue

/-! ## Color complementation -/

/-- Pointwise exchange of the two edge colors. -/
def complementColoring (coloring : Nat → Bool) : Nat → Bool :=
  fun index => !(coloring index)

/-- Since both forbidden clique sizes are four, exchanging the two colors
preserves semantic `R(4,4)` freeness. -/
theorem complementColoring_isRamseyFree
    {order : Nat} {coloring : Nat → Bool}
    (hfree : isRamseyFree order 4 4 coloring) :
    isRamseyFree order 4 4 (complementColoring coloring) := by
  constructor
  · intro vertices hlength hbound hnodup hred
    apply hfree.2 vertices hlength hbound hnodup
    intro left right hleft hright hordered
    have hedge := hred left right hleft hright hordered
    simpa [complementColoring] using hedge
  · intro vertices hlength hbound hnodup hblue
    apply hfree.1 vertices hlength hbound hnodup
    intro left right hleft hright hordered
    have hedge := hblue left right hleft hright hordered
    simpa [complementColoring] using hedge

/-- Complementation is an involutive symmetry of semantic `R(4,4)`
freeness. -/
theorem complementColoring_isRamseyFree_iff
    (order : Nat) (coloring : Nat → Bool) :
    isRamseyFree order 4 4 (complementColoring coloring) ↔
      isRamseyFree order 4 4 coloring := by
  constructor
  · intro hcomplement
    have hdouble := complementColoring_isRamseyFree hcomplement
    have hdoubleColoring :
        complementColoring (complementColoring coloring) = coloring := by
      funext index
      simp [complementColoring]
    simpa only [hdoubleColoring] using hdouble
  · exact complementColoring_isRamseyFree

/-- The packed graph of the complemented coloring remains semantically
`R(4,4)` valid. -/
theorem complementColoringGraph_r44_validAt
    (order : Nat) (coloring : Nat → Bool)
    (hfree : isRamseyFree order 4 4 coloring) :
    R44GraphValidAt order
      (coloringGraph order (complementColoring coloring)) :=
  coloringGraph_r44_validAt order (complementColoring coloring)
    (complementColoring_isRamseyFree hfree)

#print axioms noCliqueFourAt_of_graphIsoFin
#print axioms r44GraphValidAt_iff_of_graphIsoFin
#print axioms coloringGraph_r44_validAt
#print axioms complementColoring_isRamseyFree_iff

end LRATCatcher.Tests.R44RootedGraphReduction
