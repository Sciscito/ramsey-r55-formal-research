import LRATCatcher.Tests.R35CatalogCertificate

/-!
  Generic one-vertex decomposition lemmas for the `R(3,5,n)` catalogue
  representation.  A graph is a list of packed adjacency rows.  Removing its
  last vertex means taking the first `n` rows and truncating each to `n` bits;
  the row at index `n` is the neighbourhood mask of the removed vertex.

  These lemmas are independent of the generated catalogue data.  They form
  the indexing bridge needed by the later induction from the finite extension
  certificate to abstract exhaustivity up to isomorphism.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-- Pointwise equality on a list transports through Boolean `List.all`. -/
theorem listAll_congr_on
    (vertices : List Nat) (first second : Nat → Bool)
    (hequal : ∀ vertex ∈ vertices, first vertex = second vertex) :
    vertices.all first = vertices.all second := by
  induction vertices with
  | nil => rfl
  | cons head tail induction =>
    simp only [List.all_cons]
    rw [hequal head (by simp)]
    have htail := induction (fun vertex hvertex =>
      hequal vertex (by simp [hvertex]))
    rw [htail]

/-- Pointwise equality on a list transports through the local `pairwise`. -/
theorem pairwise_congr_on
    (vertices : List Nat) (first second : Nat → Nat → Bool)
    (hequal : ∀ left ∈ vertices, ∀ right ∈ vertices,
      first left right = second left right) :
    pairwise first vertices = pairwise second vertices := by
  induction vertices with
  | nil => rfl
  | cons head tail induction =>
    simp only [pairwise]
    rw [listAll_congr_on tail (first head) (second head)]
    · apply congrArg (fun value => _ && value)
      apply induction
      intro left hleft right hright
      exact hequal left (by simp [hleft]) right (by simp [hright])
    · intro right hright
      exact hequal head (by simp) right (by simp [hright])

/-- The graph induced by the first `order` vertices. -/
def initialParent (graph : Graph) (order : Nat) : Graph :=
  (graph.take order).map fun row => row % (2 ^ order)

/-- The adjacency row of the vertex removed after `initialParent`. -/
def finalVertexMask (graph : Graph) (order : Nat) : Nat :=
  graph.getD order 0

/-- The order field checked by `wellFormedGraph` is propositionally usable. -/
theorem wellFormedGraph_length
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph order graph = true) :
    graph.length = order := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq] at hwellFormed
  exact hwellFormed.1.1

/-- Extract the per-row bounds and loop checks from well-formedness. -/
theorem wellFormedGraph_row_check
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph order graph = true) :
    (List.range order).all (fun vertex =>
      decide (graph.getD vertex 0 < 2 ^ order) &&
        !(edge graph vertex vertex)) = true := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq] at hwellFormed
  exact hwellFormed.1.2

/-- Every stored row is bounded by the checked graph order. -/
theorem wellFormedGraph_row_bound
    (graph : Graph) (order vertex : Nat)
    (hwellFormed : wellFormedGraph order graph = true)
    (hvertex : vertex < order) :
    graph.getD vertex 0 < 2 ^ order := by
  have hrows := wellFormedGraph_row_check graph order hwellFormed
  rw [List.all_eq_true] at hrows
  have hrow := hrows vertex (by simpa using hvertex)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  exact hrow.1

/-- Every diagonal adjacency bit is false. -/
theorem wellFormedGraph_noLoop
    (graph : Graph) (order vertex : Nat)
    (hwellFormed : wellFormedGraph order graph = true)
    (hvertex : vertex < order) :
    edge graph vertex vertex = false := by
  have hrows := wellFormedGraph_row_check graph order hwellFormed
  rw [List.all_eq_true] at hrows
  have hrow := hrows vertex (by simpa using hvertex)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  cases hedge : edge graph vertex vertex <;> simp [hedge] at hrow ⊢

/-- Extract the pair-symmetry portion of the Boolean well-formedness check. -/
theorem wellFormedGraph_pair_check
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph order graph = true) :
    (subsets order 2).all (fun vertices =>
      match vertices with
      | [left, right] => edge graph left right == edge graph right left
      | _ => false) = true := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq] at hwellFormed
  exact hwellFormed.2

/-- The Boolean pair check implies ordinary adjacency symmetry in range. -/
theorem wellFormedGraph_edge_symmetric
    (graph : Graph) (order left right : Nat)
    (hwellFormed : wellFormedGraph order graph = true)
    (hleft : left < order) (hright : right < order) :
    edge graph left right = edge graph right left := by
  by_cases hequal : left = right
  · subst right
    rfl
  · have hnodup : [left, right].Nodup := by
      simp [hequal]
    have hbound : ∀ vertex ∈ [left, right], vertex < order := by
      intro vertex hvertex
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvertex
      rcases hvertex with rfl | rfl
      · exact hleft
      · exact hright
    obtain ⟨vertices, hvertices, hmembership⟩ :=
      subsets_complete order 2 [left, right] hnodup hbound rfl
    have hchecked := wellFormedGraph_pair_check graph order hwellFormed
    rw [List.all_eq_true] at hchecked
    have hpair := hchecked vertices hvertices
    obtain ⟨hlength, _, _⟩ := subsets_valid order 2 vertices hvertices
    cases vertices with
    | nil => simp at hlength
    | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second rest =>
        cases rest with
        | cons third rest => simp at hlength
        | nil =>
          have hpairsymmetric :
              edge graph first second = edge graph second first := by
            simpa only [beq_iff_eq] using hpair
          have hleftMember : left = first ∨ left = second := by
            have := (hmembership left).2 (by simp)
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using this
          have hrightMember : right = first ∨ right = second := by
            have := (hmembership right).2 (by simp)
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using this
          rcases hleftMember with hleftFirst | hleftSecond <;>
            rcases hrightMember with hrightFirst | hrightSecond
          · subst left
            subst right
            rfl
          · subst left
            subst right
            exact hpairsymmetric
          · subst left
            subst right
            exact hpairsymmetric.symm
          · subst left
            subst right
            rfl

/-- Parent rows are the corresponding original rows truncated to `order` bits. -/
theorem initialParent_getD
    (graph : Graph) (order vertex : Nat) (hvertex : vertex < order) :
    (initialParent graph order).getD vertex 0 =
      graph.getD vertex 0 % (2 ^ order) := by
  simp only [initialParent, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_take_of_lt hvertex]
  cases graph[vertex]? <;> simp

/-- Truncating parent rows preserves every adjacency bit still in range. -/
theorem initialParent_edge
    (graph : Graph) (order left right : Nat)
    (hleft : left < order) (hright : right < order) :
    edge (initialParent graph order) left right = edge graph left right := by
  simp only [edge, initialParent_getD graph order left hleft]
  simp [Nat.testBit_mod_two_pow, hright]

/-- Pairwise edge checks on old vertices are unchanged in the parent. -/
theorem pairwise_initialParent_edge
    (graph : Graph) (order : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < order) :
    pairwise (edge graph) vertices =
      pairwise (edge (initialParent graph order)) vertices := by
  apply pairwise_congr_on
  intro left hleft right hright
  exact (initialParent_edge graph order left right
    (hbound left hleft) (hbound right hright)).symm

/-- Pairwise non-edge checks on old vertices are unchanged in the parent. -/
theorem pairwise_initialParent_nonedge
    (graph : Graph) (order : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < order) :
    pairwise (fun left right => !(edge graph left right)) vertices =
      pairwise
        (fun left right => !(edge (initialParent graph order) left right))
        vertices := by
  apply pairwise_congr_on
  intro left hleft right hright
  rw [initialParent_edge graph order left right
    (hbound left hleft) (hbound right hright)]

/-- A clique check after adding the final vertex factors into mask and parent checks. -/
theorem pairwise_cons_finalVertex
    (graph : Graph) (order : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < order) :
    pairwise (edge graph) (order :: vertices) =
      (vertices.all (finalVertexMask graph order).testBit &&
        pairwise (edge (initialParent graph order)) vertices) := by
  simp only [pairwise]
  have hall :
      vertices.all (edge graph order) =
        vertices.all (finalVertexMask graph order).testBit := by
    apply listAll_congr_on
    intro vertex _
    rfl
  rw [hall, pairwise_initialParent_edge graph order vertices hbound]

/-- The analogous factorization for an independent-set check. -/
theorem pairwise_cons_finalVertex_nonedge
    (graph : Graph) (order : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < order) :
    pairwise (fun left right => !(edge graph left right)) (order :: vertices) =
      (vertices.all (fun vertex => !(finalVertexMask graph order).testBit vertex) &&
        pairwise
          (fun left right => !(edge (initialParent graph order) left right))
          vertices) := by
  simp only [pairwise]
  have hall :
      vertices.all (fun vertex => !(edge graph order vertex)) =
        vertices.all
          (fun vertex => !(finalVertexMask graph order).testBit vertex) := by
    apply listAll_congr_on
    intro vertex _
    rfl
  rw [hall, pairwise_initialParent_nonedge graph order vertices hbound]

/-- A graph of order `n+1` has an `n`-row initial parent. -/
theorem initialParent_length
    (graph : Graph) (order : Nat) (hlength : graph.length = order + 1) :
    (initialParent graph order).length = order := by
  simp [initialParent, hlength]

/--
The final-vertex row is a genuine `order`-bit mask.  The row bound excludes
bits above `order`, while the no-loop check excludes bit `order` itself.
This is exactly the range fact needed for membership in `List.range
(2 ^ parent.length)` inside `validPairs`.
-/
theorem finalVertexMask_lt_two_pow
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true) :
    finalVertexMask graph order < 2 ^ order := by
  apply Nat.lt_pow_two_of_testBit
  intro bit hbit
  rcases Nat.eq_or_lt_of_le hbit with hequal | habove
  · subst bit
    have hloop := wellFormedGraph_noLoop
      graph (order + 1) order hwellFormed (by omega)
    simpa only [finalVertexMask, edge] using hloop
  · apply Nat.testBit_lt_two_pow
    have hrowBound := wellFormedGraph_row_bound
      graph (order + 1) order hwellFormed (by omega)
    exact Nat.lt_of_lt_of_le hrowBound
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))

/-- Deleting the final vertex preserves the catalogue well-formedness invariant. -/
theorem initialParent_wellFormed
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true) :
    wellFormedGraph order (initialParent graph order) = true := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · constructor
    · exact initialParent_length graph order
        (wellFormedGraph_length graph (order + 1) hwellFormed)
    · rw [List.all_eq_true]
      intro vertex hvertex
      have hvertexLt : vertex < order := by simpa using hvertex
      have hrowBound :
          (initialParent graph order).getD vertex 0 < 2 ^ order := by
        rw [initialParent_getD graph order vertex hvertexLt]
        exact Nat.mod_lt _ (Nat.two_pow_pos order)
      have hnoLoop :
          edge (initialParent graph order) vertex vertex = false := by
        rw [initialParent_edge graph order vertex vertex hvertexLt hvertexLt]
        exact wellFormedGraph_noLoop
          graph (order + 1) vertex hwellFormed (by omega)
      rw [Bool.and_eq_true]
      constructor
      · exact decide_eq_true hrowBound
      · simp [hnoLoop]
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hlength, hbound, _⟩ := subsets_valid order 2 vertices hvertices
    cases vertices with
    | nil => simp at hlength
    | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second rest =>
        cases rest with
        | cons third rest => simp at hlength
        | nil =>
          have hfirst : first < order := hbound first (by simp)
          have hsecond : second < order := hbound second (by simp)
          have horiginal := wellFormedGraph_edge_symmetric
            graph (order + 1) first second hwellFormed (by omega) (by omega)
          have hparent :
              edge (initialParent graph order) first second =
                edge (initialParent graph order) second first := by
            rw [initialParent_edge graph order first second hfirst hsecond]
            rw [initialParent_edge graph order second first hsecond hfirst]
            exact horiginal
          simpa only [beq_iff_eq] using hparent

/--
If the full graph is `R(3,5)`-valid, then the canonical final-vertex mask is
one of the valid extensions of its parent.  This closes the semantic bridge
to the pairs enumerated by `validPairs`.
-/
theorem finalVertex_validExtension
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true)
    (hvalid : validGraph graph = true) :
    validExtension
      (initialParent graph order)
      (finalVertexMask graph order) = true := by
  have hlength := wellFormedGraph_length graph (order + 1) hwellFormed
  have hparentLength := initialParent_length graph order hlength
  have hvalidParts := hvalid
  simp only [validGraph, Bool.and_eq_true] at hvalidParts
  obtain ⟨hnoTriangles, hnoIndependentFive⟩ := hvalidParts
  rw [List.all_eq_true] at hnoTriangles hnoIndependentFive
  simp only [validExtension, Bool.and_eq_true]
  rw [hparentLength]
  constructor
  · rw [List.all_eq_true]
    intro vertices hvertices
    have hfullVertices : order :: vertices ∈ subsets graph.length 3 := by
      rw [hlength]
      simp only [subsets, List.mem_append, List.mem_map]
      exact Or.inl ⟨vertices, hvertices, rfl⟩
    have hfullCheck := hnoTriangles (order :: vertices) hfullVertices
    obtain ⟨_, hbound, _⟩ := subsets_valid order 2 vertices hvertices
    rw [pairwise_cons_finalVertex graph order vertices hbound] at hfullCheck
    exact hfullCheck
  · rw [List.all_eq_true]
    intro vertices hvertices
    have hfullVertices : order :: vertices ∈ subsets graph.length 5 := by
      rw [hlength]
      simp only [subsets, List.mem_append, List.mem_map]
      exact Or.inl ⟨vertices, hvertices, rfl⟩
    have hfullCheck := hnoIndependentFive (order :: vertices) hfullVertices
    obtain ⟨_, hbound, _⟩ := subsets_valid order 4 vertices hvertices
    rw [pairwise_cons_finalVertex_nonedge graph order vertices hbound] at hfullCheck
    exact hfullCheck

/-- Restricting a valid `R(3,5)` graph to its initial parent preserves validity. -/
theorem initialParent_validGraph
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true)
    (hvalid : validGraph graph = true) :
    validGraph (initialParent graph order) = true := by
  have hlength := wellFormedGraph_length graph (order + 1) hwellFormed
  have hparentLength := initialParent_length graph order hlength
  have hvalidParts := hvalid
  simp only [validGraph, Bool.and_eq_true] at hvalidParts
  obtain ⟨hnoTriangles, hnoIndependentFive⟩ := hvalidParts
  rw [List.all_eq_true] at hnoTriangles hnoIndependentFive
  simp only [validGraph, Bool.and_eq_true]
  rw [hparentLength]
  constructor
  · rw [List.all_eq_true]
    intro vertices hvertices
    have hfullVertices : vertices ∈ subsets graph.length 3 := by
      rw [hlength]
      simp only [subsets, List.mem_append, List.mem_map]
      exact Or.inr hvertices
    have hfullCheck := hnoTriangles vertices hfullVertices
    obtain ⟨_, hbound, _⟩ := subsets_valid order 3 vertices hvertices
    rw [pairwise_initialParent_edge graph order vertices hbound] at hfullCheck
    exact hfullCheck
  · rw [List.all_eq_true]
    intro vertices hvertices
    have hfullVertices : vertices ∈ subsets graph.length 5 := by
      rw [hlength]
      simp only [subsets, List.mem_append, List.mem_map]
      exact Or.inr hvertices
    have hfullCheck := hnoIndependentFive vertices hfullVertices
    obtain ⟨_, hbound, _⟩ := subsets_valid order 5 vertices hvertices
    rw [pairwise_initialParent_nonedge graph order vertices hbound] at hfullCheck
    exact hfullCheck

/--
Reconstruct every adjacency bit of a graph of order `n+1` from its initial
parent and final-vertex mask.  Symmetry is required only when the final vertex
occurs as the right endpoint, because its stored row supplies the opposite
orientation.
-/
theorem extensionEdge_initialParent
    (graph : Graph) (order left right : Nat)
    (hlength : graph.length = order + 1)
    (hleft : left < order + 1) (hright : right < order + 1)
    (hsymmetric :
      ∀ first second,
        first < order + 1 → second < order + 1 →
          edge graph first second = edge graph second first) :
    extensionEdge
        (initialParent graph order)
        (finalVertexMask graph order)
        left right =
      edge graph left right := by
  have hparentLength : (initialParent graph order).length = order :=
    initialParent_length graph order hlength
  simp only [extensionEdge, hparentLength]
  by_cases hleftNew : left = order
  · subst left
    simp [finalVertexMask, edge]
  · by_cases hrightNew : right = order
    · subst right
      simp only [beq_iff_eq, hleftNew, ↓reduceIte, finalVertexMask, edge]
      exact hsymmetric order left (by omega) hleft
    · have hleftParent : left < order := by omega
      have hrightParent : right < order := by omega
      simp only [beq_iff_eq, hleftNew, hrightNew, ↓reduceIte]
      exact initialParent_edge graph order left right hleftParent hrightParent

/--
The reconstruction theorem specialized to the Boolean well-formedness
predicate used for every decoded graph6 catalogue entry.
-/
theorem extensionEdge_initialParent_of_wellFormed
    (graph : Graph) (order left right : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true)
    (hleft : left < order + 1) (hright : right < order + 1) :
    extensionEdge
        (initialParent graph order)
        (finalVertexMask graph order)
        left right =
      edge graph left right := by
  apply extensionEdge_initialParent graph order left right
  · exact wellFormedGraph_length graph (order + 1) hwellFormed
  · exact hleft
  · exact hright
  · intro first second hfirst hsecond
    exact wellFormedGraph_edge_symmetric
      graph (order + 1) first second hwellFormed hfirst hsecond

/--
Proof-carrying decomposition of decoded graph6 data at its final vertex.
`edge_eq` states extensional equality on the complete `(order+1)`-vertex
domain, which is the form needed to transport clique predicates.
-/
structure FinalVertexDecomposition (graph : Graph) (order : Nat) where
  parent : Graph
  mask : Nat
  parent_length : parent.length = order
  parent_wellFormed : wellFormedGraph order parent = true
  mask_bound : mask < 2 ^ order
  edge_eq : ∀ left right,
    left < order + 1 → right < order + 1 →
      extensionEdge parent mask left right = edge graph left right

/-- Every well-formed decoded graph6 graph admits its canonical decomposition. -/
def decomposeFinalVertex
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true) :
    FinalVertexDecomposition graph order where
  parent := initialParent graph order
  mask := finalVertexMask graph order
  parent_length :=
    initialParent_length graph order
      (wellFormedGraph_length graph (order + 1) hwellFormed)
  parent_wellFormed := initialParent_wellFormed graph order hwellFormed
  mask_bound := finalVertexMask_lt_two_pow graph order hwellFormed
  edge_eq := fun left right hleft hright =>
    extensionEdge_initialParent_of_wellFormed
      graph order left right hwellFormed hleft hright

/-- The extracted mask occurs in the exact finite range enumerated by `validPairs`. -/
theorem finalVertexMask_mem_range
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true) :
    finalVertexMask graph order ∈
      List.range (2 ^ (initialParent graph order).length) := by
  rw [List.mem_range]
  rw [initialParent_length graph order
    (wellFormedGraph_length graph (order + 1) hwellFormed)]
  exact finalVertexMask_lt_two_pow graph order hwellFormed

/-- A decomposition carrying the two Ramsey-validity facts used by induction. -/
structure ValidFinalVertexDecomposition (graph : Graph) (order : Nat) where
  decomposition : FinalVertexDecomposition graph order
  parent_valid : validGraph decomposition.parent = true
  extension_valid :
    validExtension decomposition.parent decomposition.mask = true

/-- Construct the complete proof-carrying decomposition of a valid graph. -/
def decomposeValidFinalVertex
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true)
    (hvalid : validGraph graph = true) :
    ValidFinalVertexDecomposition graph order where
  decomposition := decomposeFinalVertex graph order hwellFormed
  parent_valid := initialParent_validGraph graph order hwellFormed hvalid
  extension_valid := finalVertex_validExtension graph order hwellFormed hvalid

end LRATCatcher.Tests.R35
