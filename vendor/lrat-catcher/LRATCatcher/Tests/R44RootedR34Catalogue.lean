import LRATCatcher.Tests.R35CatalogCompleteness

/-!
  Certified `R(3,4)` subcatalogues extracted from the exhaustive `R(3,5)`
  catalogues.

  In a rooted `R(4,4,16)` classification, the neighbours and non-neighbours
  of the root have orders seven and eight (up to exchanging the two colours),
  and each side is `R(3,4)`-free.  The generated `R(3,5)` catalogues already
  classify every such graph up to the strong `GraphIsoFin` relation.  It is
  therefore enough to retain exactly the representatives with no independent
  set of size four and prove that this extra check is isomorphism invariant.

  This module supplies that reusable interface.  It does not yet classify the
  ways in which an order-seven representative and an order-eight
  representative can be joined across the root partition.
-/

namespace LRATCatcher.Tests.R44RootedR34Catalogue

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35

/-- Executable check excluding independent sets of size four. -/
def noIndependentFour (graph : Graph) : Bool :=
  (subsets graph.length 4).all fun vertices =>
    !(pairwise (fun left right => !(edge graph left right)) vertices)

/-- Semantic counterpart of `noIndependentFour`. -/
def NoIndependentFourAt (order : Nat) (graph : Graph) : Prop :=
  ∀ vertices,
    vertices.length = 4 →
    (∀ vertex ∈ vertices, vertex < order) →
    vertices.Nodup →
    ¬AllDistinctRelated
      (fun left right => !(edge graph left right)) vertices

/-- The executable size-four check implies its semantic counterpart. -/
theorem noIndependentFour_semantic
    {graph : Graph} (hcheck : noIndependentFour graph = true) :
    NoIndependentFourAt graph.length graph := by
  unfold noIndependentFour at hcheck
  intro vertices hlength hbound hnodup hindependent
  obtain ⟨canonical, hcanonical, hmembership⟩ :=
    subsets_complete graph.length 4 vertices hnodup hbound hlength
  obtain ⟨_, _, hcanonicalNodup⟩ :=
    subsets_valid graph.length 4 canonical hcanonical
  have hcanonicalIndependent :
      AllDistinctRelated
        (fun left right => !(edge graph left right)) canonical := by
    intro left hleft right hright hne
    exact hindependent left ((hmembership left).mp hleft)
      right ((hmembership right).mp hright) hne
  have hpairwise :=
    pairwise_of_allDistinctRelated hcanonicalNodup hcanonicalIndependent
  have hforbidden := List.all_eq_true.mp hcheck canonical hcanonical
  change
    (!(pairwise (fun left right => !(edge graph left right)) canonical)) = true
    at hforbidden
  rw [hpairwise] at hforbidden
  contradiction

/-- The semantic size-four property is accepted by the executable checker. -/
theorem semantic_noIndependentFour
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true)
    (hsemantic : NoIndependentFourAt order graph) :
    noIndependentFour graph = true := by
  have hgraphLength := wellFormedGraph_length graph order hwellFormed
  subst order
  unfold noIndependentFour
  rw [List.all_eq_true]
  intro vertices hvertices
  obtain ⟨hlength, hbound, hnodup⟩ :=
    subsets_valid graph.length 4 vertices hvertices
  cases hpairwise :
      pairwise (fun left right => !(edge graph left right)) vertices
  · rfl
  · exfalso
    apply hsemantic vertices hlength hbound hnodup
    apply allDistinctRelated_of_pairwise hnodup
    · intro left hleft right hright
      exact congrArg Bool.not
        (wellFormedGraph_edge_symmetric
          graph graph.length left right hwellFormed
          (hbound left hleft) (hbound right hright))
    · exact hpairwise

/-- Pulling vertices through an injective edge-preserving map transports the
absence of an independent set of size four. -/
theorem noIndependentFourAt_of_embedding
    {order : Nat} {source target : Graph}
    (pull : Nat → Nat)
    (hpullBound : ∀ vertex, vertex < order → pull vertex < order)
    (hpullInjective : Function.Injective pull)
    (hpullEdge : ∀ left, left < order → ∀ right, right < order →
      edge source (pull left) (pull right) = edge target left right)
    (hsource : NoIndependentFourAt order source) :
    NoIndependentFourAt order target := by
  intro vertices hlength hbound hnodup hrelated
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
    change Bool.not (edge source (pull originalLeft) (pull originalRight)) = true
    rw [hpullEdge originalLeft (hbound originalLeft horiginalLeft)
      originalRight (hbound originalRight horiginalRight)]
    exact hrelated originalLeft horiginalLeft originalRight horiginalRight
      (fun hequal => hne (congrArg pull hequal))

/-- Semantic invariance of the size-four exclusion under `GraphIsoFin`. -/
theorem noIndependentFourAt_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (hsource : NoIndependentFourAt isomorphism.order source) :
    NoIndependentFourAt isomorphism.order target := by
  refine noIndependentFourAt_of_embedding
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

/-- Boolean invariance needed to justify filtering catalogue representatives. -/
theorem noIndependentFour_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (htargetWellFormed : wellFormedGraph target.length target = true)
    (hsource : noIndependentFour source = true) :
    noIndependentFour target = true := by
  have hsourceSemantic := noIndependentFour_semantic hsource
  have hsourceOrder :
      NoIndependentFourAt isomorphism.order source := by
    simpa only [isomorphism.sourceOrder] using hsourceSemantic
  have htargetOrder :=
    noIndependentFourAt_of_graphIsoFin isomorphism hsourceOrder
  have htargetSemantic : NoIndependentFourAt target.length target := by
    simpa only [isomorphism.targetOrder] using htargetOrder
  exact semantic_noIndependentFour htargetWellFormed htargetSemantic

/-- `R(3,4)` validity presented as the certified `R(3,5)` validity plus the
strictly stronger independent-four exclusion.  The redundant independent-five
component makes the existing exhaustive catalogue theorem directly reusable. -/
def R34GraphValidAt (order : Nat) (graph : Graph) : Prop :=
  GraphValidAt order graph ∧ noIndependentFour graph = true

/-- Representatives of order `order` retained from the certified `R(3,5)`
catalogue after the independent-four filter. -/
def r34Catalogue (order : Nat) : List Graph :=
  (catalogues.getD order []).filter noIndependentFour

abbrev r34Catalogue7 : List Graph := r34Catalogue 7
abbrev r34Catalogue8 : List Graph := r34Catalogue 8

/-- The filter isolates the nine order-seven `R(3,4)` isomorphism classes. -/
theorem r34Catalogue7_length_eq_nine : r34Catalogue7.length = 9 := by
  native_decide

/-- The filter isolates the three critical order-eight `R(3,4)` classes. -/
theorem r34Catalogue8_length_eq_three : r34Catalogue8.length = 3 := by
  native_decide

/-- Every retained representative satisfies the full `R(3,4)` interface. -/
theorem r34Catalogue_entry_valid
    (order : Nat) (horder : order < catalogues.length)
    (graph : Graph) (hgraph : graph ∈ r34Catalogue order) :
    R34GraphValidAt order graph := by
  have hfiltered := List.mem_filter.mp hgraph
  exact ⟨catalogue_entry_checked order horder graph hfiltered.1,
    hfiltered.2⟩

/-- Any `R(3,4)` graph at a certified level is strongly isomorphic to one of
the representatives retained by `r34Catalogue`. -/
theorem r34_catalogue_complete
    (order : Nat) (horder : order ≤ extensionWitnesses.length) :
    Complete (R34GraphValidAt order) GraphIsomorphicFin
      (r34Catalogue order) := by
  intro graph hgraph
  obtain ⟨representative, hrepresentative, hisomorphic⟩ :=
    r35_catalogues_complete order horder graph hgraph.1
  have hcatalogueOrder : order < catalogues.length := by
    rw [catalogues_length_eq]
    omega
  have hrepresentativeValid :=
    catalogue_entry_checked order hcatalogueOrder
      representative hrepresentative
  obtain ⟨isomorphism⟩ := hisomorphic
  have hrepresentativeNoIndependentFour :
      noIndependentFour representative = true := by
    apply noIndependentFour_of_graphIsoFin isomorphism
    · have hlength : representative.length = order :=
        wellFormedGraph_length representative order hrepresentativeValid.1
      simpa only [hlength] using hrepresentativeValid.1
    · exact hgraph.2
  refine ⟨representative, ?_, ⟨isomorphism⟩⟩
  exact List.mem_filter.mpr
    ⟨hrepresentative, hrepresentativeNoIndependentFour⟩

/-- Exhaustive order-seven `R(3,4)` representatives for the smaller side of
a rooted order-sixteen classification. -/
theorem r34_catalogue_seven_complete :
    Complete (R34GraphValidAt 7) GraphIsomorphicFin r34Catalogue7 := by
  apply r34_catalogue_complete 7
  rw [extensionWitnesses_length_eq_fourteen]
  omega

/-- Exhaustive order-eight `R(3,4)` representatives for the larger side of
a rooted order-sixteen classification. -/
theorem r34_catalogue_eight_complete :
    Complete (R34GraphValidAt 8) GraphIsomorphicFin r34Catalogue8 := by
  apply r34_catalogue_complete 8
  rw [extensionWitnesses_length_eq_fourteen]
  omega

#print axioms noIndependentFour_of_graphIsoFin
#print axioms r34Catalogue7_length_eq_nine
#print axioms r34Catalogue8_length_eq_three
#print axioms r34_catalogue_seven_complete
#print axioms r34_catalogue_eight_complete

end LRATCatcher.Tests.R44RootedR34Catalogue
