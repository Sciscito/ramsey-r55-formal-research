import LRATCatcher.Tests.R35CatalogCompletenessCore

/-!
  Bridge between the extension-oriented certificate checker and the concrete
  `GraphIso` vocabulary used by the catalogue-completeness development.

  `isExtensionIsomorphism` checks the graph obtained by adjoining one vertex
  only through its edge relation.  This file materializes that relation as an
  adjacency-row graph and proves that every successful extension witness is a
  `GraphIso` witness for the materialized graph.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-- Materialize the graph obtained by adjoining one vertex to `parent`.

The old rows are truncated to the old order, then receive the new vertex bit
specified by `mask`.  The final row is the mask, also truncated to the old
order.  Truncation makes the construction insensitive to irrelevant high bits
in the input representation. -/
def extensionGraph (parent : Graph) (mask : Nat) : Graph :=
  let order := parent.length
  (parent.mapIdx fun vertex row =>
    (row % 2 ^ order) |||
      if mask.testBit vertex then 2 ^ order else 0) ++
    [mask % 2 ^ order]

@[simp] theorem extensionGraph_length (parent : Graph) (mask : Nat) :
    (extensionGraph parent mask).length = parent.length + 1 := by
  simp [extensionGraph]

@[simp] theorem extensionGraph_getD_old
    (parent : Graph) (mask vertex : Nat) (hvertex : vertex < parent.length) :
    (extensionGraph parent mask).getD vertex 0 =
      (parent.getD vertex 0 % 2 ^ parent.length) |||
        if mask.testBit vertex then 2 ^ parent.length else 0 := by
  rw [← List.getElem_eq_getD
    (l := extensionGraph parent mask) (i := vertex)
    (h := by simp; omega) 0]
  rw [← List.getElem_eq_getD
    (l := parent) (i := vertex) (h := hvertex) 0]
  simp [extensionGraph, hvertex]

@[simp] theorem extensionGraph_getD_new (parent : Graph) (mask : Nat) :
    (extensionGraph parent mask).getD parent.length 0 =
      mask % 2 ^ parent.length := by
  rw [← List.getElem_eq_getD
    (l := extensionGraph parent mask) (i := parent.length)
    (h := by simp) 0]
  simp [extensionGraph]

/-- The materialized adjacency relation is exactly `extensionEdge` on every
pair of distinct in-range vertices. -/
theorem edge_extensionGraph
    (parent : Graph) (mask left right : Nat)
    (hleft : left < parent.length + 1)
    (hright : right < parent.length + 1)
    (hne : left ≠ right) :
    edge (extensionGraph parent mask) left right =
      extensionEdge parent mask left right := by
  by_cases hl : left = parent.length
  · subst left
    have hr : right < parent.length := by omega
    change
      ((extensionGraph parent mask).getD parent.length 0).testBit right = _
    rw [extensionGraph_getD_new]
    simp [extensionEdge, hr, Nat.testBit_mod_two_pow]
  · have hl' : left < parent.length := by omega
    by_cases hr : right = parent.length
    · subst right
      change
        ((extensionGraph parent mask).getD left 0).testBit parent.length = _
      rw [extensionGraph_getD_old parent mask left hl']
      cases hm : mask.testBit left <;>
        simp [extensionEdge, hl, hm, Nat.testBit_mod_two_pow,
          Nat.testBit_or]
    · have hr' : right < parent.length := by omega
      have hnr : parent.length ≠ right := by omega
      change ((extensionGraph parent mask).getD left 0).testBit right = _
      rw [extensionGraph_getD_old parent mask left hl']
      cases hm : mask.testBit left <;>
        simp [extensionEdge, edge, hl, hr, hr', hnr, Nat.testBit_mod_two_pow,
          Nat.testBit_or]

/-- A successful extension-certificate permutation is a successful concrete
graph-isomorphism permutation for the materialized extension. -/
theorem isGraphIsomorphism_extensionGraph_of_isExtensionIsomorphism
    (parent target : Graph) (mask : Nat) (permutation : List Nat)
    (hiso :
      isExtensionIsomorphism parent mask target permutation = true) :
    isGraphIsomorphism (extensionGraph parent mask) target permutation = true := by
  unfold isExtensionIsomorphism at hiso
  unfold isGraphIsomorphism
  simp only [extensionGraph_length]
  rw [Bool.and_eq_true] at hiso ⊢
  refine ⟨hiso.1, ?_⟩
  have hall := hiso.2
  rw [List.all_eq_true] at hall ⊢
  intro vertices hvertices
  have hchecked := hall vertices hvertices
  have hvalid := subsets_valid (parent.length + 1) 2 vertices hvertices
  match vertices with
  | [] => simp at hvalid
  | [_] => simp at hvalid
  | [left, right] =>
      have hleft : left < parent.length + 1 := hvalid.2.1 left (by simp)
      have hright : right < parent.length + 1 := hvalid.2.1 right (by simp)
      have hne : left ≠ right := by
        simpa using hvalid.2.2
      simpa [edge_extensionGraph parent mask left right hleft hright hne] using hchecked
  | _ :: _ :: _ :: _ => simp at hvalid

/-- Propositional bridge used by the transition-completeness theorem. -/
theorem graphIso_extensionGraph_of_isExtensionIsomorphism
    (parent target : Graph) (mask : Nat) (permutation : List Nat)
    (hiso :
      isExtensionIsomorphism parent mask target permutation = true) :
    GraphIso (extensionGraph parent mask) target := by
  exact ⟨permutation,
    isGraphIsomorphism_extensionGraph_of_isExtensionIsomorphism
      parent target mask permutation hiso⟩

/-- Transition-table coverage stated directly with `GraphIso`, ready to be
passed to the generic `step_complete` theorem. -/
theorem checked_transition_covers_graphIso_member
    (parents targets : List Graph) (witnesses : List ExtensionWitness)
    (representative : Graph) (mask : Nat)
    (hcheck : checkTransition parents targets witnesses = true)
    (hrepresentative : representative ∈ parents)
    (hmask : mask < 2 ^ representative.length)
    (hvalid : validExtension representative mask = true) :
    ∃ target, target ∈ targets ∧
      GraphIso (extensionGraph representative mask) target := by
  obtain ⟨target, htarget, permutation, hiso⟩ :=
    checked_transition_covers_member
      parents targets witnesses representative mask hcheck
      hrepresentative hmask hvalid
  exact ⟨target, htarget,
    graphIso_extensionGraph_of_isExtensionIsomorphism
      representative target mask permutation hiso⟩

end LRATCatcher.Tests.R35
