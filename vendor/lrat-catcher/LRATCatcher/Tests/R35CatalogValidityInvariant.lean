import LRATCatcher.Tests.R35CatalogGraphIso
import LRATCatcher.Tests.R35CatalogDecomposition

/-!
  Invariance of the R(3,5)-free predicate under the strong finite graph
  isomorphisms used by the catalogue completeness proof.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-! ## Semantic form of the finite validity check -/

def AllDistinctRelated
    (relation : Nat → Nat → Bool) (vertices : List Nat) : Prop :=
  ∀ left, left ∈ vertices → ∀ right, right ∈ vertices →
    left ≠ right → relation left right = true

def SemanticallyValidGraph (order : Nat) (graph : Graph) : Prop :=
  (∀ vertices,
    vertices.length = 3 →
    (∀ vertex ∈ vertices, vertex < order) →
    vertices.Nodup →
    ¬AllDistinctRelated (edge graph) vertices) ∧
  (∀ vertices,
    vertices.length = 5 →
    (∀ vertex ∈ vertices, vertex < order) →
    vertices.Nodup →
    ¬AllDistinctRelated (fun left right => !(edge graph left right)) vertices)

theorem pairwise_of_allDistinctRelated
    {relation : Nat → Nat → Bool} {vertices : List Nat}
    (hnodup : vertices.Nodup)
    (hall : AllDistinctRelated relation vertices) :
    pairwise relation vertices = true := by
  induction vertices with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    rw [List.nodup_cons] at hnodup
    simp only [pairwise, Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro vertex hvertex
      apply hall head (by simp) vertex (by simp [hvertex])
      intro hequal
      subst vertex
      exact hnodup.1 hvertex
    · apply inductionHypothesis hnodup.2
      intro left hleft right hright hne
      exact hall left (by simp [hleft]) right (by simp [hright]) hne

theorem allDistinctRelated_of_pairwise
    {relation : Nat → Nat → Bool} {vertices : List Nat}
    (hnodup : vertices.Nodup)
    (hsymmetric : ∀ left, left ∈ vertices → ∀ right, right ∈ vertices →
      relation left right = relation right left)
    (hpairwise : pairwise relation vertices = true) :
    AllDistinctRelated relation vertices := by
  induction vertices with
  | nil =>
    intro left hleft
    simp at hleft
  | cons head tail inductionHypothesis =>
    rw [List.nodup_cons] at hnodup
    simp only [pairwise, Bool.and_eq_true] at hpairwise
    have hhead := List.all_eq_true.mp hpairwise.1
    have htail := inductionHypothesis hnodup.2
      (fun left hleft right hright =>
        hsymmetric left (by simp [hleft]) right (by simp [hright]))
      hpairwise.2
    intro left hleft right hright hne
    simp only [List.mem_cons] at hleft hright
    rcases hleft with rfl | hleft
    · rcases hright with rfl | hright
      · exact absurd rfl hne
      · exact hhead right hright
    · rcases hright with rfl | hright
      · rw [hsymmetric left (by simp [hleft]) right (by simp)]
        exact hhead left hleft
      · exact htail left hleft right hright hne

theorem validGraph_semantic
    {graph : Graph} (hvalid : validGraph graph = true) :
    SemanticallyValidGraph graph.length graph := by
  unfold validGraph at hvalid
  rw [Bool.and_eq_true] at hvalid
  constructor
  · intro vertices hlength hbound hnodup hclique
    obtain ⟨canonical, hcanonical, hmembership⟩ :=
      subsets_complete graph.length 3 vertices hnodup hbound hlength
    obtain ⟨_, _, hcanonicalNodup⟩ :=
      subsets_valid graph.length 3 canonical hcanonical
    have hcanonicalClique : AllDistinctRelated (edge graph) canonical := by
      intro left hleft right hright hne
      exact hclique left ((hmembership left).mp hleft)
        right ((hmembership right).mp hright) hne
    have hpairwise :=
      pairwise_of_allDistinctRelated hcanonicalNodup hcanonicalClique
    have hforbidden := List.all_eq_true.mp hvalid.1 canonical hcanonical
    change (!(pairwise (edge graph) canonical)) = true at hforbidden
    rw [hpairwise] at hforbidden
    contradiction
  · intro vertices hlength hbound hnodup hindependent
    obtain ⟨canonical, hcanonical, hmembership⟩ :=
      subsets_complete graph.length 5 vertices hnodup hbound hlength
    obtain ⟨_, _, hcanonicalNodup⟩ :=
      subsets_valid graph.length 5 canonical hcanonical
    have hcanonicalIndependent :
        AllDistinctRelated
          (fun left right => !(edge graph left right)) canonical := by
      intro left hleft right hright hne
      exact hindependent left ((hmembership left).mp hleft)
        right ((hmembership right).mp hright) hne
    have hpairwise :=
      pairwise_of_allDistinctRelated hcanonicalNodup hcanonicalIndependent
    have hforbidden := List.all_eq_true.mp hvalid.2 canonical hcanonical
    change
      (!(pairwise (fun left right => !(edge graph left right)) canonical)) = true
      at hforbidden
    rw [hpairwise] at hforbidden
    contradiction

theorem semantic_validGraph
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true)
    (hsemantic : SemanticallyValidGraph order graph) :
    validGraph graph = true := by
  have hgraphLength := wellFormedGraph_length graph order hwellFormed
  subst order
  unfold validGraph
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hlength, hbound, hnodup⟩ :=
      subsets_valid graph.length 3 vertices hvertices
    cases hpairwise : pairwise (edge graph) vertices
    · rfl
    · exfalso
      apply hsemantic.1 vertices hlength hbound hnodup
      apply allDistinctRelated_of_pairwise hnodup
      · intro left hleft right hright
        exact wellFormedGraph_edge_symmetric
          graph graph.length left right hwellFormed
          (hbound left hleft) (hbound right hright)
      · exact hpairwise
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hlength, hbound, hnodup⟩ :=
      subsets_valid graph.length 5 vertices hvertices
    cases hpairwise : pairwise
        (fun left right => !(edge graph left right)) vertices
    · rfl
    · exfalso
      apply hsemantic.2 vertices hlength hbound hnodup
      apply allDistinctRelated_of_pairwise hnodup
      · intro left hleft right hright
        exact congrArg Bool.not
          (wellFormedGraph_edge_symmetric
            graph graph.length left right hwellFormed
            (hbound left hleft) (hbound right hright))
      · exact hpairwise

/-! ## Transport through a finite graph isomorphism -/

namespace FinPermutation

/-- Extend a permutation of `Fin order` to the naturals, fixing every value
outside its finite domain. -/
def applyNat {order : Nat}
    (permutation : FinPermutation order) (vertex : Nat) : Nat :=
  if hvertex : vertex < order then
    (permutation ⟨vertex, hvertex⟩).val
  else
    vertex

@[simp] theorem applyNat_of_lt {order vertex : Nat}
    (permutation : FinPermutation order) (hvertex : vertex < order) :
    permutation.applyNat vertex = (permutation ⟨vertex, hvertex⟩).val := by
  simp [applyNat, hvertex]

theorem applyNat_lt {order vertex : Nat}
    (permutation : FinPermutation order) (hvertex : vertex < order) :
    permutation.applyNat vertex < order := by
  rw [applyNat_of_lt permutation hvertex]
  exact (permutation ⟨vertex, hvertex⟩).isLt

theorem applyNat_injective {order : Nat}
    (permutation : FinPermutation order) :
    Function.Injective permutation.applyNat := by
  intro left right hequal
  by_cases hleft : left < order
  · by_cases hright : right < order
    · rw [applyNat_of_lt permutation hleft,
        applyNat_of_lt permutation hright] at hequal
      have hfin :
          permutation ⟨left, hleft⟩ = permutation ⟨right, hright⟩ :=
        Fin.ext hequal
      exact congrArg Fin.val (permutation.injective hfin)
    · simp only [applyNat, dif_pos hleft, dif_neg hright] at hequal
      have himage : (permutation ⟨left, hleft⟩).val < order :=
        (permutation ⟨left, hleft⟩).isLt
      omega
  · by_cases hright : right < order
    · simp only [applyNat, dif_neg hleft, dif_pos hright] at hequal
      have himage : (permutation ⟨right, hright⟩).val < order :=
        (permutation ⟨right, hright⟩).isLt
      omega
    · simpa [applyNat, hleft, hright] using hequal

end FinPermutation

theorem semanticallyValidGraph_of_embedding
    {order : Nat} {source target : Graph}
    (pull : Nat → Nat)
    (hpullBound : ∀ vertex, vertex < order → pull vertex < order)
    (hpullInjective : Function.Injective pull)
    (hpullEdge : ∀ left, left < order → ∀ right, right < order →
      edge source (pull left) (pull right) = edge target left right)
    (hsource : SemanticallyValidGraph order source) :
    SemanticallyValidGraph order target := by
  constructor
  · intro vertices hlength hbound hnodup hrelated
    let pulled := vertices.map pull
    apply hsource.1 pulled
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
      exact hrelated originalLeft horiginalLeft originalRight horiginalRight
        (fun hequal => hne (congrArg pull hequal))
  · intro vertices hlength hbound hnodup hrelated
    let pulled := vertices.map pull
    apply hsource.2 pulled
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

theorem semanticallyValidGraph_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (hsource : SemanticallyValidGraph isomorphism.order source) :
    SemanticallyValidGraph isomorphism.order target := by
  refine semanticallyValidGraph_of_embedding
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

/-- Directional invariance of the executable R(3,5)-free check. -/
theorem validGraph_of_graphIsoFin
    {source target : Graph} (isomorphism : GraphIsoFin source target)
    (_hsourceWellFormed : wellFormedGraph source.length source = true)
    (htargetWellFormed : wellFormedGraph target.length target = true)
    (hsourceValid : validGraph source = true) :
    validGraph target = true := by
  have hsourceSemantic := validGraph_semantic hsourceValid
  have hsourceOrder : SemanticallyValidGraph isomorphism.order source := by
    simpa only [isomorphism.sourceOrder] using hsourceSemantic
  have htargetOrder :=
    semanticallyValidGraph_of_graphIsoFin isomorphism hsourceOrder
  have htargetSemantic : SemanticallyValidGraph target.length target := by
    simpa only [isomorphism.targetOrder] using htargetOrder
  exact semantic_validGraph htargetWellFormed htargetSemantic

end LRATCatcher.Tests.R35
