import LRATCatcher.Tests.R35CatalogGraphIso

/-!
  Bridge from the generated list-based permutation witnesses to the semantic
  `FinPermutation`/`GraphIsoFin` layer.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-! ## A checked list permutation really is a permutation of `range n` -/

theorem isPermutation_length
    {permutation : List Nat} {order : Nat}
    (hpermutation : isPermutation permutation order = true) :
    permutation.length = order := by
  unfold isPermutation at hpermutation
  rw [Bool.and_eq_true] at hpermutation
  exact beq_iff_eq.mp hpermutation.1

theorem isPermutation_count
    {permutation : List Nat} {order target : Nat}
    (hpermutation : isPermutation permutation order = true)
    (htarget : target < order) :
    permutation.count target = 1 := by
  unfold isPermutation at hpermutation
  rw [Bool.and_eq_true] at hpermutation
  have hcount := List.all_eq_true.mp hpermutation.2
    target (List.mem_range.mpr htarget)
  exact beq_iff_eq.mp hcount

/-- The Boolean checker excludes out-of-range entries as a consequence of its
length and exact-count conditions. -/
theorem isPermutation_perm_range
    {permutation : List Nat} {order : Nat}
    (hpermutation : isPermutation permutation order = true) :
    permutation.Perm (List.range order) := by
  let inside := permutation.filter fun value => decide (value < order)
  have hinsidePerm : inside.Perm (List.range order) := by
    rw [List.perm_iff_count]
    intro value
    by_cases hvalue : value < order
    · have hpredicate : decide (value < order) = true := by simp [hvalue]
      have hfiltered : inside.count value = permutation.count value := by
        exact List.count_filter hpredicate
      rw [hfiltered, isPermutation_count hpermutation hvalue,
        List.count_range, if_pos hvalue]
    · have hnotmem : value ∉ inside := by
        intro hmem
        have hpredicate := (List.mem_filter.mp hmem).2
        simp [hvalue] at hpredicate
      rw [List.count_eq_zero.mpr hnotmem, List.count_range, if_neg hvalue]
  have hinsideLength : inside.length = order := by
    simpa using hinsidePerm.length_eq
  have hpermutationLength := isPermutation_length hpermutation
  have hinsideEq : inside = permutation :=
    List.filter_sublist.eq_of_length
      (hinsideLength.trans hpermutationLength.symm)
  simpa [hinsideEq] using hinsidePerm

theorem isPermutation_nodup
    {permutation : List Nat} {order : Nat}
    (hpermutation : isPermutation permutation order = true) :
    permutation.Nodup :=
  (isPermutation_perm_range hpermutation).symm.nodup List.nodup_range

theorem permutation_getD_lt
    {permutation : List Nat} {order index : Nat}
    (hpermutation : isPermutation permutation order = true)
    (hindex : index < order) :
    permutation.getD index order < order := by
  have hlength := isPermutation_length hpermutation
  have hindexList : index < permutation.length := by simpa [hlength] using hindex
  have hmem : permutation.getD index order ∈ permutation := by
    rw [← List.getElem_eq_getD (l := permutation) (i := index)
      (h := hindexList) order]
    exact List.getElem_mem hindexList
  have hrange := (isPermutation_perm_range hpermutation).mem_iff.mp hmem
  exact List.mem_range.mp hrange

/-- Action on `Fin order` represented by a checked list. -/
def listPermutationApply
    (permutation : List Nat) (order : Nat)
    (hpermutation : isPermutation permutation order = true) :
    Fin order → Fin order := fun vertex =>
  ⟨permutation.getD vertex.val order,
    permutation_getD_lt hpermutation vertex.isLt⟩

@[simp] theorem listPermutationApply_val
    (permutation : List Nat) (order : Nat)
    (hpermutation : isPermutation permutation order = true)
    (vertex : Fin order) :
    (listPermutationApply permutation order hpermutation vertex).val =
      permutation.getD vertex.val order := rfl

theorem listPermutationApply_bijective
    (permutation : List Nat) (order : Nat)
    (hpermutation : isPermutation permutation order = true) :
    Function.Injective (listPermutationApply permutation order hpermutation) ∧
      Function.Surjective
        (listPermutationApply permutation order hpermutation) := by
  constructor
  · intro left right hequal
    apply Fin.ext
    have hlength := isPermutation_length hpermutation
    have hleft : left.val < permutation.length := by
      simp [hlength, left.isLt]
    have hright : right.val < permutation.length := by
      simp [hlength, right.isLt]
    apply (List.getD_inj hleft hright
      (isPermutation_nodup hpermutation)).mp
    exact congrArg Fin.val hequal
  · intro target
    have htargetRange : target.val ∈ List.range order :=
      List.mem_range.mpr target.isLt
    have htargetMem : target.val ∈ permutation :=
      (isPermutation_perm_range hpermutation).mem_iff.mpr htargetRange
    obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem htargetMem
    have hlength := isPermutation_length hpermutation
    let source : Fin order := ⟨index, by simpa [hlength] using hindex⟩
    refine ⟨source, Fin.ext ?_⟩
    change permutation.getD index order = target.val
    calc
      permutation.getD index order = permutation[index] :=
        (List.getElem_eq_getD (l := permutation) (i := index)
          (h := hindex) order).symm
      _ = target.val := hvalue

namespace FinPermutation

/-- Build a finite permutation from a bijective endofunction. -/
noncomputable def ofBijective {order : Nat}
    (function : Fin order → Fin order)
    (hbijective : Function.Injective function ∧ Function.Surjective function) :
    FinPermutation order where
  toFun := function
  invFun := fun target => Classical.choose (hbijective.2 target)
  left_inv := fun vertex =>
    hbijective.1 (Classical.choose_spec (hbijective.2 (function vertex)))
  right_inv := fun target => Classical.choose_spec (hbijective.2 target)

end FinPermutation

/-- Canonical semantic permutation extracted from a generated list witness. -/
noncomputable def listPermutationToFin
    (permutation : List Nat) (order : Nat)
    (hpermutation : isPermutation permutation order = true) :
    FinPermutation order :=
  FinPermutation.ofBijective
    (listPermutationApply permutation order hpermutation)
    (listPermutationApply_bijective permutation order hpermutation)

@[simp] theorem listPermutationToFin_apply_val
    (permutation : List Nat) (order : Nat)
    (hpermutation : isPermutation permutation order = true)
    (vertex : Fin order) :
    (listPermutationToFin permutation order hpermutation vertex).val =
      permutation.getD vertex.val order := by
  rfl

/-! ## Ordered pairs and well-formed adjacency matrices -/

theorem singleton_mem_subsets
    {order vertex : Nat} (hvertex : vertex < order) :
    [vertex] ∈ subsets order 1 := by
  induction order with
  | zero => omega
  | succ order inductionHypothesis =>
    simp only [subsets, List.mem_append, List.mem_map]
    by_cases htop : vertex = order
    · left
      refine ⟨[], by simp, ?_⟩
      simp [htop]
    · right
      exact inductionHypothesis (by omega)

theorem ordered_pair_mem_subsets
    {order high low : Nat}
    (hhigh : high < order) (hlow : low < high) :
    [high, low] ∈ subsets order 2 := by
  induction order generalizing high low with
  | zero => omega
  | succ order inductionHypothesis =>
    simp only [subsets, List.mem_append, List.mem_map]
    by_cases htop : high = order
    · left
      refine ⟨[low], singleton_mem_subsets (by omega), ?_⟩
      simp [htop]
    · right
      exact inductionHypothesis (by omega) hlow

theorem graphIsoBridge_wellFormedGraph_length
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true) :
    graph.length = order := by
  unfold wellFormedGraph at hwellFormed
  rw [Bool.and_eq_true] at hwellFormed
  have hhead := hwellFormed.1
  rw [Bool.and_eq_true] at hhead
  exact beq_iff_eq.mp hhead.1

theorem wellFormedGraph_rows
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true) :
    (List.range order).all (fun vertex =>
      decide (graph.getD vertex 0 < 2 ^ order) &&
        !(edge graph vertex vertex)) = true := by
  unfold wellFormedGraph at hwellFormed
  rw [Bool.and_eq_true] at hwellFormed
  have hhead := hwellFormed.1
  rw [Bool.and_eq_true] at hhead
  exact hhead.2

theorem wellFormedGraph_pairs
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true) :
    (subsets order 2).all (fun vertices =>
      match vertices with
      | [left, right] => edge graph left right == edge graph right left
      | _ => false) = true := by
  unfold wellFormedGraph at hwellFormed
  rw [Bool.and_eq_true] at hwellFormed
  exact hwellFormed.2

theorem wellFormedGraph_loop_false
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true)
    {vertex : Nat} (hvertex : vertex < order) :
    edge graph vertex vertex = false := by
  have hrow := List.all_eq_true.mp (wellFormedGraph_rows hwellFormed)
    vertex (List.mem_range.mpr hvertex)
  change
    (decide (graph.getD vertex 0 < 2 ^ order) &&
      !(edge graph vertex vertex)) = true at hrow
  rw [Bool.and_eq_true] at hrow
  have hloop := hrow.2
  cases hedge : edge graph vertex vertex
  · rfl
  · simp [hedge] at hloop

theorem wellFormedGraph_edge_comm_of_gt
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true)
    {high low : Nat} (hhigh : high < order) (hlow : low < high) :
    edge graph high low = edge graph low high := by
  have hpairs := List.all_eq_true.mp (wellFormedGraph_pairs hwellFormed)
    [high, low] (ordered_pair_mem_subsets hhigh hlow)
  change (edge graph high low == edge graph low high) = true at hpairs
  exact beq_iff_eq.mp hpairs

theorem wellFormedGraph_edge_comm
    {order : Nat} {graph : Graph}
    (hwellFormed : wellFormedGraph order graph = true)
    {left right : Nat} (hleft : left < order) (hright : right < order) :
    edge graph left right = edge graph right left := by
  by_cases hequal : left = right
  · subst right
    rfl
  by_cases hless : left < right
  · exact (wellFormedGraph_edge_comm_of_gt hwellFormed hright hless).symm
  · exact wellFormedGraph_edge_comm_of_gt hwellFormed hleft (by omega)

/-! ## Reading the Boolean graph-isomorphism witness -/

theorem isGraphIsomorphism_sameOrder
    {source target : Graph} {permutation : List Nat}
    (hisomorphism :
      isGraphIsomorphism source target permutation = true) :
    target.length = source.length := by
  unfold isGraphIsomorphism at hisomorphism
  rw [Bool.and_eq_true] at hisomorphism
  have hhead := hisomorphism.1
  rw [Bool.and_eq_true] at hhead
  exact beq_iff_eq.mp hhead.1

theorem isGraphIsomorphism_isPermutation
    {source target : Graph} {permutation : List Nat}
    (hisomorphism :
      isGraphIsomorphism source target permutation = true) :
    isPermutation permutation source.length = true := by
  unfold isGraphIsomorphism at hisomorphism
  rw [Bool.and_eq_true] at hisomorphism
  have hhead := hisomorphism.1
  rw [Bool.and_eq_true] at hhead
  exact hhead.2

theorem isGraphIsomorphism_pairs
    {source target : Graph} {permutation : List Nat}
    (hisomorphism :
      isGraphIsomorphism source target permutation = true) :
    (subsets source.length 2).all (fun vertices =>
      match vertices with
      | [left, right] =>
          edge source left right ==
            edge target
              (permutation.getD left source.length)
              (permutation.getD right source.length)
      | _ => false) = true := by
  unfold isGraphIsomorphism at hisomorphism
  rw [Bool.and_eq_true] at hisomorphism
  exact hisomorphism.2

theorem isGraphIsomorphism_edge_of_gt
    {source target : Graph} {permutation : List Nat}
    (hisomorphism :
      isGraphIsomorphism source target permutation = true)
    {high low : Nat}
    (hhigh : high < source.length) (hlow : low < high) :
    edge source high low =
      edge target
        (permutation.getD high source.length)
        (permutation.getD low source.length) := by
  have hpairs := List.all_eq_true.mp
    (isGraphIsomorphism_pairs hisomorphism)
    [high, low] (ordered_pair_mem_subsets hhigh hlow)
  change
    (edge source high low ==
      edge target
        (permutation.getD high source.length)
        (permutation.getD low source.length)) = true at hpairs
  exact beq_iff_eq.mp hpairs

/-! ## Full bridge -/

/-- Upgrade a generated list witness to the strong semantic isomorphism.

Both well-formedness assumptions use the common source order.  The checked
list witness independently proves that the target has this same order.
-/
noncomputable def isGraphIsomorphism_toGraphIsoFin
    {source target : Graph} {permutation : List Nat}
    (hisomorphism : isGraphIsomorphism source target permutation = true)
    (hsource : wellFormedGraph source.length source = true)
    (htarget : wellFormedGraph source.length target = true) :
    GraphIsoFin source target := by
  let hpermutation := isGraphIsomorphism_isPermutation hisomorphism
  let finitePermutation :=
    listPermutationToFin permutation source.length hpermutation
  refine ⟨source.length, rfl,
    (graphIsoBridge_wellFormedGraph_length htarget), finitePermutation, ?_⟩
  intro left right
  by_cases hequal : left.val = right.val
  · have hvertices : left = right := Fin.ext hequal
    subst right
    rw [wellFormedGraph_loop_false hsource left.isLt]
    exact wellFormedGraph_loop_false htarget
      (finitePermutation left).isLt |>.symm
  · by_cases hgreater : right.val < left.val
    · exact isGraphIsomorphism_edge_of_gt hisomorphism
        left.isLt hgreater
    · have hless : left.val < right.val := by omega
      calc
        edge source left.val right.val =
            edge source right.val left.val :=
          wellFormedGraph_edge_comm hsource left.isLt right.isLt
        _ = edge target
            (permutation.getD right.val source.length)
            (permutation.getD left.val source.length) :=
          isGraphIsomorphism_edge_of_gt hisomorphism right.isLt hless
        _ = edge target
            (permutation.getD left.val source.length)
            (permutation.getD right.val source.length) :=
          wellFormedGraph_edge_comm htarget
            (permutation_getD_lt hpermutation right.isLt)
            (permutation_getD_lt hpermutation left.isLt)

/-- Propositional bridge used by the catalogue induction. -/
theorem graphIso_toGraphIsomorphicFin
    {source target : Graph}
    (hisomorphism : GraphIso source target)
    (hsource : wellFormedGraph source.length source = true)
    (htarget : wellFormedGraph source.length target = true) :
    GraphIsomorphicFin source target := by
  obtain ⟨permutation, hpermutation⟩ := hisomorphism
  exact ⟨isGraphIsomorphism_toGraphIsoFin hpermutation hsource htarget⟩

/-- Ergonomic variant where each well-formedness certificate is stated at its
own graph's length; the list isomorphism supplies equality of the orders. -/
theorem graphIso_toGraphIsomorphicFin_selfOrder
    {source target : Graph}
    (hisomorphism : GraphIso source target)
    (hsource : wellFormedGraph source.length source = true)
    (htarget : wellFormedGraph target.length target = true) :
    GraphIsomorphicFin source target := by
  obtain ⟨permutation, hpermutation⟩ := hisomorphism
  have hsameOrder := isGraphIsomorphism_sameOrder hpermutation
  have htargetAtSource : wellFormedGraph source.length target = true := by
    rw [← hsameOrder]
    exact htarget
  exact ⟨isGraphIsomorphism_toGraphIsoFin
    hpermutation hsource htargetAtSource⟩

end LRATCatcher.Tests.R35
