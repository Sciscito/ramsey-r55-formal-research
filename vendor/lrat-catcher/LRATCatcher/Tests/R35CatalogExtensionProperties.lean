import LRATCatcher.Tests.R35CatalogDecomposition
import LRATCatcher.Tests.R35CatalogExtensionBridge
import LRATCatcher.Tests.R35CatalogGraphIso

/-!
  Structural properties of the materialized one-vertex extension.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-- Adding one vertex preserves symmetry of the adjacency relation whenever
the parent passed the independent well-formedness checker. -/
theorem extensionEdge_symmetric_of_wellFormed
    (parent : Graph) (order mask left right : Nat)
    (hparent : wellFormedGraph order parent = true)
    (hleft : left < order + 1) (hright : right < order + 1) :
    extensionEdge parent mask left right =
      extensionEdge parent mask right left := by
  have hlength : parent.length = order :=
    wellFormedGraph_length parent order hparent
  simp only [extensionEdge, hlength, beq_iff_eq]
  by_cases hl : left = order
  · subst left
    by_cases hr : right = order <;> simp [hr]
  · by_cases hr : right = order
    · subst right
      simp [hl]
    · simp only [hl, hr, ↓reduceIte]
      exact wellFormedGraph_edge_symmetric
        parent order left right hparent (by omega) (by omega)

/-- The materialized extension always has the expected well-formed adjacency
matrix when the parent is well formed and the mask is in range. -/
theorem extensionGraph_wellFormed
    (parent : Graph) (order mask : Nat)
    (hparent : wellFormedGraph order parent = true)
    (hmask : mask < 2 ^ order) :
    wellFormedGraph (order + 1) (extensionGraph parent mask) = true := by
  have hlength : parent.length = order :=
    wellFormedGraph_length parent order hparent
  subst order
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact extensionGraph_length parent mask
  · rw [List.all_eq_true]
    intro vertex hvertexMem
    have hvertex : vertex < parent.length + 1 := by
      simpa using hvertexMem
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply decide_eq_true
      by_cases hv : vertex = parent.length
      · subst vertex
        rw [extensionGraph_getD_new]
        exact Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_lt_pow_right (by decide) (by omega))
      · have hvold : vertex < parent.length := by omega
        rw [extensionGraph_getD_old parent mask vertex hvold]
        apply Nat.or_lt_two_pow
        · exact Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_lt_pow_right (by decide) (by omega))
        · split
          · exact Nat.pow_lt_pow_right (by decide) (by omega)
          · exact Nat.two_pow_pos _
    · by_cases hv : vertex = parent.length
      · subst vertex
        simp only [edge]
        rw [extensionGraph_getD_new]
        simp [Nat.testBit_mod_two_pow]
      · have hvold : vertex < parent.length := by omega
        have hnoloop := wellFormedGraph_noLoop
          parent parent.length vertex hparent hvold
        change (parent.getD vertex 0).testBit vertex = false at hnoloop
        rw [← List.getElem_eq_getD
          (l := parent) (i := vertex) (h := hvold) 0] at hnoloop
        have hlengthNe : parent.length ≠ vertex := by omega
        simp only [edge]
        rw [extensionGraph_getD_old parent mask vertex hvold]
        cases hm : mask.testBit vertex <;>
          simp [Nat.testBit_or, Nat.testBit_mod_two_pow, hvold,
            hnoloop, hlengthNe]
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hverticesLength, hbound, hnodup⟩ :=
      subsets_valid (parent.length + 1) 2 vertices hvertices
    match vertices with
    | [] => simp at hverticesLength
    | [_] => simp at hverticesLength
    | [left, right] =>
        have hleft : left < parent.length + 1 := hbound left (by simp)
        have hright : right < parent.length + 1 := hbound right (by simp)
        have hne : left ≠ right := by simpa using hnodup
        have hforward := edge_extensionGraph parent mask left right
          hleft hright hne
        have hbackward := edge_extensionGraph parent mask right left
          hright hleft hne.symm
        rw [beq_iff_eq, hforward, hbackward]
        exact extensionEdge_symmetric_of_wellFormed
          parent parent.length mask left right hparent hleft hright
    | _ :: _ :: _ :: _ => simp at hverticesLength

/-- On old vertices, materialization preserves every adjacency bit, including
the diagonal. -/
theorem edge_extensionGraph_old
    (parent : Graph) (mask left right : Nat)
    (hleft : left < parent.length) (hright : right < parent.length) :
    edge (extensionGraph parent mask) left right = edge parent left right := by
  have hrightNe : parent.length ≠ right := by omega
  simp only [edge, extensionGraph_getD_old parent mask left hleft]
  cases hm : mask.testBit left <;>
    simp [Nat.testBit_or, Nat.testBit_mod_two_pow, hright,
      hrightNe]

/-- The new vertex's row is precisely the bounded part of `mask`. -/
theorem edge_extensionGraph_new_left
    (parent : Graph) (mask vertex : Nat)
    (hvertex : vertex < parent.length) :
    edge (extensionGraph parent mask) parent.length vertex =
      mask.testBit vertex := by
  change ((extensionGraph parent mask).getD parent.length 0).testBit vertex = _
  rw [extensionGraph_getD_new]
  simp [Nat.testBit_mod_two_pow, hvertex]

theorem pairwise_extensionGraph_old
    (parent : Graph) (mask : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < parent.length) :
    pairwise (edge (extensionGraph parent mask)) vertices =
      pairwise (edge parent) vertices := by
  apply pairwise_congr_on
  intro left hleft right hright
  exact edge_extensionGraph_old parent mask left right
    (hbound left hleft) (hbound right hright)

theorem pairwise_extensionGraph_old_nonedge
    (parent : Graph) (mask : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < parent.length) :
    pairwise (fun left right => !(edge (extensionGraph parent mask) left right))
        vertices =
      pairwise (fun left right => !(edge parent left right)) vertices := by
  apply pairwise_congr_on
  intro left hleft right hright
  rw [edge_extensionGraph_old parent mask left right
    (hbound left hleft) (hbound right hright)]

theorem pairwise_cons_extensionGraph
    (parent : Graph) (mask : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < parent.length) :
    pairwise (edge (extensionGraph parent mask))
        (parent.length :: vertices) =
      (vertices.all mask.testBit && pairwise (edge parent) vertices) := by
  simp only [pairwise]
  rw [listAll_congr_on vertices
    (edge (extensionGraph parent mask) parent.length) mask.testBit]
  · rw [pairwise_extensionGraph_old parent mask vertices hbound]
  · intro vertex hvertex
    exact edge_extensionGraph_new_left parent mask vertex
      (hbound vertex hvertex)

theorem pairwise_cons_extensionGraph_nonedge
    (parent : Graph) (mask : Nat) (vertices : List Nat)
    (hbound : ∀ vertex ∈ vertices, vertex < parent.length) :
    pairwise
        (fun left right => !(edge (extensionGraph parent mask) left right))
        (parent.length :: vertices) =
      (vertices.all (fun vertex => !(mask.testBit vertex)) &&
        pairwise (fun left right => !(edge parent left right)) vertices) := by
  simp only [pairwise]
  rw [listAll_congr_on vertices
    (fun vertex => !(edge (extensionGraph parent mask) parent.length vertex))
    (fun vertex => !(mask.testBit vertex))]
  · rw [pairwise_extensionGraph_old_nonedge parent mask vertices hbound]
  · intro vertex hvertex
    rw [edge_extensionGraph_new_left parent mask vertex
      (hbound vertex hvertex)]

/-- A valid parent and a valid one-vertex mask materialize to a valid graph.
This is the construction-side converse of `decomposeValidFinalVertex`. -/
theorem extensionGraph_validGraph
    (parent : Graph) (mask : Nat)
    (hparentValid : validGraph parent = true)
    (hextensionValid : validExtension parent mask = true) :
    validGraph (extensionGraph parent mask) = true := by
  simp only [validGraph, Bool.and_eq_true] at hparentValid ⊢
  simp only [validExtension, Bool.and_eq_true] at hextensionValid
  obtain ⟨hparentTriangles, hparentIndependent⟩ := hparentValid
  obtain ⟨hextensionTriangles, hextensionIndependent⟩ := hextensionValid
  rw [List.all_eq_true] at hparentTriangles hparentIndependent hextensionTriangles hextensionIndependent
  simp only [extensionGraph_length]
  constructor
  · rw [List.all_eq_true]
    intro vertices hvertices
    simp only [subsets, List.mem_append, List.mem_map] at hvertices
    rcases hvertices with ⟨oldVertices, holdVertices, rfl⟩ | holdVertices
    · have hcheck := hextensionTriangles oldVertices holdVertices
      obtain ⟨_, hbound, _⟩ :=
        subsets_valid parent.length 2 oldVertices holdVertices
      rw [pairwise_cons_extensionGraph parent mask oldVertices hbound]
      exact hcheck
    · have hcheck := hparentTriangles vertices holdVertices
      obtain ⟨_, hbound, _⟩ :=
        subsets_valid parent.length 3 vertices holdVertices
      rw [pairwise_extensionGraph_old parent mask vertices hbound]
      exact hcheck
  · rw [List.all_eq_true]
    intro vertices hvertices
    simp only [subsets, List.mem_append, List.mem_map] at hvertices
    rcases hvertices with ⟨oldVertices, holdVertices, rfl⟩ | holdVertices
    · have hcheck := hextensionIndependent oldVertices holdVertices
      obtain ⟨_, hbound, _⟩ :=
        subsets_valid parent.length 4 oldVertices holdVertices
      rw [pairwise_cons_extensionGraph_nonedge parent mask oldVertices hbound]
      exact hcheck
    · have hcheck := hparentIndependent vertices holdVertices
      obtain ⟨_, hbound, _⟩ :=
        subsets_valid parent.length 5 vertices holdVertices
      rw [pairwise_extensionGraph_old_nonedge parent mask vertices hbound]
      exact hcheck

/-- The canonical last-vertex decomposition is isomorphic to the original
graph through the identity permutation on vertices. -/
theorem graphIsomorphicFin_decomposeFinalVertex
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph (order + 1) graph = true) :
    GraphIsomorphicFin graph
      (extensionGraph
        (initialParent graph order)
        (finalVertexMask graph order)) := by
  let parent := initialParent graph order
  let mask := finalVertexMask graph order
  have hsourceLength : graph.length = order + 1 :=
    wellFormedGraph_length graph (order + 1) hwellFormed
  have hparentWellFormed : wellFormedGraph order parent = true :=
    initialParent_wellFormed graph order hwellFormed
  have hparentLength : parent.length = order :=
    initialParent_length graph order hsourceLength
  have hmaskBound : mask < 2 ^ order :=
    finalVertexMask_lt_two_pow graph order hwellFormed
  have htargetWellFormed :
      wellFormedGraph (order + 1) (extensionGraph parent mask) = true :=
    extensionGraph_wellFormed parent order mask hparentWellFormed hmaskBound
  refine ⟨{
    order := order + 1
    sourceOrder := hsourceLength
    targetOrder := by
      change (extensionGraph parent mask).length = order + 1
      rw [extensionGraph_length, hparentLength]
    permutation := FinPermutation.refl (order + 1)
    map_edge := ?_
  }⟩
  intro left right
  simp only [FinPermutation.refl_apply]
  by_cases hequal : left = right
  · subst right
    have hsourceLoop := wellFormedGraph_noLoop
      graph (order + 1) left.val hwellFormed left.isLt
    have htargetLoop := wellFormedGraph_noLoop
      (extensionGraph parent mask) (order + 1) left.val
      htargetWellFormed left.isLt
    rw [hsourceLoop, htargetLoop]
  · have hvaluesNe : left.val ≠ right.val := by
      intro hvalues
      exact hequal (Fin.ext hvalues)
    have hextension := edge_extensionGraph
      parent mask left.val right.val
      (by omega)
      (by omega)
      hvaluesNe
    have hreconstruction := extensionEdge_initialParent_of_wellFormed
      graph order left.val right.val hwellFormed left.isLt right.isLt
    change edge graph left.val right.val =
      edge (extensionGraph parent mask) left.val right.val
    exact (hextension.trans hreconstruction).symm

end LRATCatcher.Tests.R35
