import LRATCatcher.Tests.R35CatalogCompletenessCore

/-!
  Algebraic graph isomorphisms for the R(3,5,n) catalogue proof.

  The generated certificate stores permutations as `List Nat`.  For semantic
  composition it is safer to work with an actual finite bijection and require
  preservation of every ordered adjacency pair.  This avoids an important
  pitfall of the Boolean `GraphIso`: its checker visits one orientation of each
  unordered pair, so transitivity would otherwise require separate matrix-
  symmetry hypotheses.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-! ## Finite permutations -/

/-- A small dependency-free permutation type for `Fin n`. -/
structure FinPermutation (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ vertex, invFun (toFun vertex) = vertex
  right_inv : ∀ vertex, toFun (invFun vertex) = vertex

namespace FinPermutation

instance (n : Nat) : CoeFun (FinPermutation n) (fun _ => Fin n → Fin n) :=
  ⟨FinPermutation.toFun⟩

def refl (n : Nat) : FinPermutation n where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def symm {n : Nat} (permutation : FinPermutation n) : FinPermutation n where
  toFun := permutation.invFun
  invFun := permutation.toFun
  left_inv := permutation.right_inv
  right_inv := permutation.left_inv

/-- `left.trans right` applies `left` first and `right` second. -/
def trans {n : Nat}
    (left right : FinPermutation n) : FinPermutation n where
  toFun := fun vertex => right (left vertex)
  invFun := fun vertex => left.invFun (right.invFun vertex)
  left_inv := by
    intro vertex
    rw [right.left_inv, left.left_inv]
  right_inv := by
    intro vertex
    rw [left.right_inv, right.right_inv]

theorem injective {n : Nat} (permutation : FinPermutation n) :
    Function.Injective permutation := by
  intro left right hequal
  have := congrArg permutation.invFun hequal
  simpa only [permutation.left_inv] using this

theorem surjective {n : Nat} (permutation : FinPermutation n) :
    Function.Surjective permutation := by
  intro target
  exact ⟨permutation.invFun target, permutation.right_inv target⟩

@[simp] theorem refl_apply {n : Nat} (vertex : Fin n) :
    refl n vertex = vertex := rfl

@[simp] theorem symm_apply_apply {n : Nat}
    (permutation : FinPermutation n) (vertex : Fin n) :
    permutation.symm (permutation vertex) = vertex :=
  permutation.left_inv vertex

@[simp] theorem apply_symm_apply {n : Nat}
    (permutation : FinPermutation n) (vertex : Fin n) :
    permutation (permutation.symm vertex) = vertex :=
  permutation.right_inv vertex

end FinPermutation

/-! ## Strong semantic graph isomorphism -/

/-- A finite graph isomorphism that checks every ordered adjacency pair. -/
structure GraphIsoFin (source target : Graph) where
  order : Nat
  sourceOrder : source.length = order
  targetOrder : target.length = order
  permutation : FinPermutation order
  map_edge : ∀ left right : Fin order,
    edge source left.val right.val =
      edge target (permutation left).val (permutation right).val

namespace GraphIsoFin

def refl (graph : Graph) : GraphIsoFin graph graph := by
  refine ⟨graph.length, rfl, rfl, FinPermutation.refl graph.length, ?_⟩
  intro left right
  rfl

def symm {source target : Graph}
    (isomorphism : GraphIsoFin source target) :
    GraphIsoFin target source := by
  rcases isomorphism with
    ⟨order, sourceOrder, targetOrder, permutation, mapEdge⟩
  refine ⟨order, targetOrder, sourceOrder, permutation.symm, ?_⟩
  intro left right
  have h := (mapEdge (permutation.symm left) (permutation.symm right)).symm
  simpa only [FinPermutation.apply_symm_apply] using h

def trans {source middle target : Graph}
    (left : GraphIsoFin source middle)
    (right : GraphIsoFin middle target) :
    GraphIsoFin source target := by
  rcases left with
    ⟨leftOrder, sourceOrder, middleOrderLeft, leftPermutation, leftMap⟩
  rcases right with
    ⟨rightOrder, middleOrderRight, targetOrder, rightPermutation, rightMap⟩
  have ordersEqual : leftOrder = rightOrder :=
    middleOrderLeft.symm.trans middleOrderRight
  cases ordersEqual
  refine ⟨leftOrder, sourceOrder, targetOrder,
    leftPermutation.trans rightPermutation, ?_⟩
  intro first second
  exact (leftMap first second).trans
    (rightMap (leftPermutation first) (leftPermutation second))

theorem same_length {source target : Graph}
    (isomorphism : GraphIsoFin source target) :
    source.length = target.length :=
  isomorphism.sourceOrder.trans isomorphism.targetOrder.symm

theorem edge_eq {source target : Graph}
    (isomorphism : GraphIsoFin source target)
    (left right : Fin isomorphism.order) :
    edge source left.val right.val =
      edge target
        (isomorphism.permutation left).val
        (isomorphism.permutation right).val :=
  isomorphism.map_edge left right

end GraphIsoFin

/-- Propositional wrapper used by `Complete` and `step_complete`. -/
def GraphIsomorphicFin (source target : Graph) : Prop :=
  Nonempty (GraphIsoFin source target)

namespace GraphIsomorphicFin

theorem refl (graph : Graph) : GraphIsomorphicFin graph graph :=
  ⟨GraphIsoFin.refl graph⟩

theorem symm {source target : Graph}
    (isomorphism : GraphIsomorphicFin source target) :
    GraphIsomorphicFin target source := by
  obtain ⟨witness⟩ := isomorphism
  exact ⟨witness.symm⟩

theorem trans {source middle target : Graph}
    (left : GraphIsomorphicFin source middle)
    (right : GraphIsomorphicFin middle target) :
    GraphIsomorphicFin source target := by
  obtain ⟨leftWitness⟩ := left
  obtain ⟨rightWitness⟩ := right
  exact ⟨leftWitness.trans rightWitness⟩

end GraphIsomorphicFin

/-- The strong finite graph-isomorphism relation is an equivalence relation. -/
theorem graphIsoFin_equivalence : Equivalence GraphIsomorphicFin :=
  ⟨GraphIsomorphicFin.refl, GraphIsomorphicFin.symm,
    GraphIsomorphicFin.trans⟩

/-! ## Direct facts about the generated list-based relation -/

theorem range_getD_eq {order vertex : Nat} (hvertex : vertex < order) :
    (List.range order).getD vertex order = vertex := by
  have hindex : vertex < (List.range order).length := by
    simpa using hvertex
  calc
    (List.range order).getD vertex order = (List.range order)[vertex] :=
      (List.getElem_eq_getD (l := List.range order) (i := vertex)
        (h := hindex) order).symm
    _ = vertex := List.getElem_range hindex

theorem listPermutation_refl (order : Nat) :
    isPermutation (List.range order) order = true := by
  simp [isPermutation, List.count_range]

/-- Identity for the original Boolean-witness relation.  Unlike symmetry and
transitivity, this requires no matrix-symmetry side condition. -/
theorem graphIso_refl (graph : Graph) : GraphIso graph graph := by
  refine ⟨List.range graph.length, ?_⟩
  simp only [isGraphIsomorphism, Bool.and_eq_true]
  refine ⟨⟨by simp, listPermutation_refl graph.length⟩, ?_⟩
  rw [List.all_eq_true]
  intro vertices hvertices
  obtain ⟨hlength, hbound, _⟩ :=
    subsets_valid graph.length 2 vertices hvertices
  cases vertices with
  | nil => simp at hlength
  | cons left tail =>
    cases tail with
    | nil => simp at hlength
    | cons right rest =>
      cases rest with
      | nil =>
        have hleft : left < graph.length := hbound left (by simp)
        have hright : right < graph.length := hbound right (by simp)
        change
          (edge graph left right ==
            edge graph
              ((List.range graph.length).getD left graph.length)
              ((List.range graph.length).getD right graph.length)) = true
        rw [range_getD_eq hleft, range_getD_eq hright]
        simp
      | cons third rest => simp at hlength

end LRATCatcher.Tests.R35
