import LRATCatcher.Tests.R35CatalogGraphIso
import LRATCatcher.Tests.R35CatalogExtensionBridge

/-!
  Strong bridge from the generated list-permutation extension witnesses to
  `GraphIsoFin`, whose permutation is a genuine bijection of `Fin n` and whose
  edge law covers every ordered pair.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey
open scoped List

/-! ## Recovering a genuine finite permutation -/

/-- The Boolean list-permutation checker really says that its list is a
permutation of `List.range order`. -/
theorem list_perm_range_of_isPermutation :
    ∀ (order : Nat) (permutation : List Nat),
      isPermutation permutation order = true →
        permutation ~ List.range order := by
  intro order
  induction order with
  | zero =>
      intro permutation hpermutation
      simp only [isPermutation, Bool.and_eq_true, beq_iff_eq] at hpermutation
      have hempty : permutation = [] :=
        List.eq_nil_of_length_eq_zero hpermutation.1
      subst permutation
      exact List.Perm.refl []
  | succ order inductionHypothesis =>
      intro permutation hpermutation
      simp only [isPermutation, Bool.and_eq_true, beq_iff_eq] at hpermutation
      have hall := hpermutation.2
      rw [List.all_eq_true] at hall
      have hcount : permutation.count order = 1 := by
        exact beq_iff_eq.mp (hall order (by simp))
      have hmember : order ∈ permutation := by
        apply List.count_pos_iff.mp
        omega
      have herasedPermutation :
          isPermutation (permutation.erase order) order = true := by
        simp only [isPermutation, Bool.and_eq_true, beq_iff_eq]
        constructor
        · rw [List.length_erase_of_mem hmember, hpermutation.1]
          omega
        · rw [List.all_eq_true]
          intro target htarget
          have htargetLt : target < order := by simpa using htarget
          have htargetCount : permutation.count target = 1 := by
            exact beq_iff_eq.mp (hall target (by simp; omega))
          have hne : target ≠ order := by omega
          simp [List.count_erase_of_ne hne, htargetCount]
      have herased :=
        inductionHypothesis (permutation.erase order) herasedPermutation
      have hfront : permutation ~ order :: permutation.erase order :=
        List.perm_cons_erase hmember
      have hmiddle :
          order :: permutation.erase order ~ order :: List.range order :=
        herased.cons order
      have hback : order :: List.range order ~ List.range (order + 1) := by
        rw [List.range_succ]
        exact (List.perm_append_singleton order (List.range order)).symm
      exact hfront.trans (hmiddle.trans hback)

/-- The value list of a checked permutation, viewed as a function on `Fin`. -/
def finMapOfListPermutation
    {order : Nat} (permutation : List Nat)
    (hpermutation : permutation ~ List.range order) : Fin order → Fin order :=
  fun vertex =>
    let hlength : permutation.length = order := by
      simpa using hpermutation.length_eq
    let hindex : vertex.val < permutation.length := by
      rw [hlength]
      exact vertex.isLt
    ⟨permutation[vertex.val], by
      have hmember : permutation[vertex.val] ∈ permutation :=
        List.getElem_mem hindex
      have hrange : permutation[vertex.val] ∈ List.range order :=
        hpermutation.mem_iff.mp hmember
      simpa using hrange⟩

@[simp] theorem finMapOfListPermutation_val
    {order : Nat} (permutation : List Nat)
    (hpermutation : permutation ~ List.range order) (vertex : Fin order) :
    (finMapOfListPermutation permutation hpermutation vertex).val =
      permutation.getD vertex.val order := by
  let hlength : permutation.length = order := by
    simpa using hpermutation.length_eq
  have hindex : vertex.val < permutation.length := by
    rw [hlength]
    exact vertex.isLt
  rw [← List.getElem_eq_getD
    (l := permutation) (i := vertex.val) (h := hindex) order]
  rfl

/-- Package a bijective finite function in the local permutation structure. -/
noncomputable def finPermutationOfBijective
    {order : Nat} (function : Fin order → Fin order)
    (hbijective :
      Function.Injective function ∧ Function.Surjective function) :
    FinPermutation order where
  toFun := function
  invFun := fun target => Classical.choose (hbijective.2 target)
  left_inv := by
    intro vertex
    apply hbijective.1
    exact Classical.choose_spec (hbijective.2 (function vertex))
  right_inv := by
    intro vertex
    exact Classical.choose_spec (hbijective.2 vertex)

/-- Turn the generated list representation into a genuine `FinPermutation`. -/
noncomputable def finPermutationOfListPermutation
    {order : Nat} (permutation : List Nat)
    (hpermutation : permutation ~ List.range order) : FinPermutation order := by
  let function := finMapOfListPermutation permutation hpermutation
  have hlength : permutation.length = order := by
    simpa using hpermutation.length_eq
  have hnodup : permutation.Nodup :=
    hpermutation.nodup_iff.mpr List.nodup_range
  have hinjective : Function.Injective function := by
    intro left right hequal
    apply Fin.ext
    apply (List.getElem_inj hnodup).mp
    exact congrArg Fin.val hequal
  have hsurjective : Function.Surjective function := by
    intro target
    have hrange : target.val ∈ List.range order := by simp
    have hmember : target.val ∈ permutation :=
      hpermutation.mem_iff.mpr hrange
    obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hmember
    have hindexOrder : index < order := by simpa [hlength] using hindex
    refine ⟨⟨index, hindexOrder⟩, ?_⟩
    apply Fin.ext
    exact hvalue
  exact finPermutationOfBijective function ⟨hinjective, hsurjective⟩

@[simp] theorem finPermutationOfListPermutation_apply_val
    {order : Nat} (permutation : List Nat)
    (hpermutation : permutation ~ List.range order) (vertex : Fin order) :
    (finPermutationOfListPermutation permutation hpermutation vertex).val =
      permutation.getD vertex.val order := by
  exact finMapOfListPermutation_val permutation hpermutation vertex

/-! ## Symmetry and loop facts supplied by well-formedness -/

private theorem strongBridge_wellFormed_row_check
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph order graph = true) :
    (List.range order).all (fun vertex =>
      decide (graph.getD vertex 0 < 2 ^ order) &&
        !(edge graph vertex vertex)) = true := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq] at hwellFormed
  exact hwellFormed.1.2

private theorem strongBridge_wellFormed_noLoop
    (graph : Graph) (order vertex : Nat)
    (hwellFormed : wellFormedGraph order graph = true)
    (hvertex : vertex < order) :
    edge graph vertex vertex = false := by
  have hrows := strongBridge_wellFormed_row_check graph order hwellFormed
  rw [List.all_eq_true] at hrows
  have hrow := hrows vertex (by simpa using hvertex)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  cases hedge : edge graph vertex vertex <;> simp [hedge] at hrow ⊢

private theorem strongBridge_wellFormed_pair_check
    (graph : Graph) (order : Nat)
    (hwellFormed : wellFormedGraph order graph = true) :
    (subsets order 2).all (fun vertices =>
      match vertices with
      | [left, right] => edge graph left right == edge graph right left
      | _ => false) = true := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq] at hwellFormed
  exact hwellFormed.2

private theorem strongBridge_wellFormed_symmetric
    (graph : Graph) (order left right : Nat)
    (hwellFormed : wellFormedGraph order graph = true)
    (hleft : left < order) (hright : right < order) :
    edge graph left right = edge graph right left := by
  by_cases hequal : left = right
  · subst right
    rfl
  · have hnodup : [left, right].Nodup := by simp [hequal]
    have hbound : ∀ vertex ∈ [left, right], vertex < order := by
      intro vertex hvertex
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvertex
      rcases hvertex with rfl | rfl
      · exact hleft
      · exact hright
    obtain ⟨vertices, hvertices, hmembership⟩ :=
      subsets_complete order 2 [left, right] hnodup hbound rfl
    have hchecked :=
      strongBridge_wellFormed_pair_check graph order hwellFormed
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
          · subst left; subst right; rfl
          · subst left; subst right; exact hpairsymmetric
          · subst left; subst right; exact hpairsymmetric.symm
          · subst left; subst right; rfl

theorem extensionGraph_noLoop_of_parent_wellFormed
    (parent : Graph) (mask vertex : Nat)
    (hparent : wellFormedGraph parent.length parent = true)
    (hvertex : vertex < parent.length + 1) :
    edge (extensionGraph parent mask) vertex vertex = false := by
  by_cases hnew : vertex = parent.length
  · subst vertex
    change
      ((extensionGraph parent mask).getD parent.length 0).testBit
        parent.length = false
    rw [extensionGraph_getD_new]
    simp [Nat.testBit_mod_two_pow]
  · have hold : vertex < parent.length := by omega
    have hne : parent.length ≠ vertex := by omega
    have hparentLoop := strongBridge_wellFormed_noLoop
      parent parent.length vertex hparent hold
    have hparentLoop' : parent[vertex].testBit vertex = false := by
      rw [List.getElem_eq_getD (l := parent) (i := vertex) (h := hold) 0]
      exact hparentLoop
    change ((extensionGraph parent mask).getD vertex 0).testBit vertex = false
    rw [extensionGraph_getD_old parent mask vertex hold]
    cases hmask : mask.testBit vertex <;>
      simp [hold, hne, hparentLoop', Nat.testBit_mod_two_pow, Nat.testBit_or]

theorem extensionGraph_symmetric_of_parent_wellFormed
    (parent : Graph) (mask left right : Nat)
    (hparent : wellFormedGraph parent.length parent = true)
    (hleft : left < parent.length + 1)
    (hright : right < parent.length + 1) :
    edge (extensionGraph parent mask) left right =
      edge (extensionGraph parent mask) right left := by
  by_cases hequal : left = right
  · subst right
    rfl
  · rw [edge_extensionGraph parent mask left right hleft hright hequal]
    rw [edge_extensionGraph parent mask right left hright hleft (Ne.symm hequal)]
    unfold extensionEdge
    by_cases hleftNew : left = parent.length
    · subst left
      have hrightOld : right < parent.length := by omega
      have hrightNew : ¬ right = parent.length := Ne.symm hequal
      simp [hrightNew]
    · by_cases hrightNew : right = parent.length
      · subst right
        have hleftOld : left < parent.length := by omega
        simp [hleftNew]
      · have hleftOld : left < parent.length := by omega
        have hrightOld : right < parent.length := by omega
        simp only [beq_iff_eq, hleftNew, hrightNew, ↓reduceIte]
        exact strongBridge_wellFormed_symmetric
          parent parent.length left right hparent hleftOld hrightOld

/-! ## Strong extension witness -/

/-- A checked extension isomorphism upgrades to a genuine finite graph
isomorphism once the parent and target adjacency matrices are known to be
well formed. -/
noncomputable def graphIsoFin_extensionGraph_of_isExtensionIsomorphism
    (parent target : Graph) (mask : Nat) (permutation : List Nat)
    (hparent : wellFormedGraph parent.length parent = true)
    (htarget : wellFormedGraph (parent.length + 1) target = true)
    (hiso :
      isExtensionIsomorphism parent mask target permutation = true) :
    GraphIsoFin (extensionGraph parent mask) target := by
  simp only [isExtensionIsomorphism, Bool.and_eq_true] at hiso
  have htargetLength : target.length = parent.length + 1 :=
    beq_iff_eq.mp hiso.1.1
  have hlistPermutation : permutation ~ List.range (parent.length + 1) :=
    list_perm_range_of_isPermutation
      (parent.length + 1) permutation hiso.1.2
  let finitePermutation :=
    finPermutationOfListPermutation permutation hlistPermutation
  refine
    { order := parent.length + 1
      sourceOrder := extensionGraph_length parent mask
      targetOrder := htargetLength
      permutation := finitePermutation
      map_edge := ?_ }
  intro left right
  by_cases hequal : left = right
  · subst right
    have hsourceLoop := extensionGraph_noLoop_of_parent_wellFormed
      parent mask left.val hparent left.isLt
    have htargetLoop := strongBridge_wellFormed_noLoop
      target (parent.length + 1) (finitePermutation left).val
      htarget (finitePermutation left).isLt
    exact hsourceLoop.trans htargetLoop.symm
  · have hvalueNe : left.val ≠ right.val := by
      intro hvalues
      exact hequal (Fin.ext hvalues)
    have hnodup : [left.val, right.val].Nodup := by simp [hvalueNe]
    have hbound :
        ∀ vertex ∈ [left.val, right.val], vertex < parent.length + 1 := by
      intro vertex hvertex
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvertex
      rcases hvertex with rfl | rfl
      · exact left.isLt
      · exact right.isLt
    obtain ⟨vertices, hvertices, hmembership⟩ :=
      subsets_complete (parent.length + 1) 2
        [left.val, right.val] hnodup hbound rfl
    have hall := hiso.2
    rw [List.all_eq_true] at hall
    have hchecked := hall vertices hvertices
    obtain ⟨hlength, hpairsBound, hpairsNodup⟩ :=
      subsets_valid (parent.length + 1) 2 vertices hvertices
    cases vertices with
    | nil => simp at hlength
    | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second rest =>
        cases rest with
        | cons third rest => simp at hlength
        | nil =>
          have hfirst : first < parent.length + 1 :=
            hpairsBound first (by simp)
          have hsecond : second < parent.length + 1 :=
            hpairsBound second (by simp)
          have hfirstNeSecond : first ≠ second := by
            simpa using hpairsNodup
          have hchecked' :
              edge (extensionGraph parent mask) first second =
                edge target
                  (permutation.getD first (parent.length + 1))
                  (permutation.getD second (parent.length + 1)) := by
            have hraw := beq_iff_eq.mp hchecked
            rw [edge_extensionGraph parent mask first second
              hfirst hsecond hfirstNeSecond]
            exact hraw
          have hleftMember : left.val = first ∨ left.val = second := by
            have := (hmembership left.val).2 (by simp)
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using this
          have hrightMember : right.val = first ∨ right.val = second := by
            have := (hmembership right.val).2 (by simp)
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using this
          rcases hleftMember with hleftFirst | hleftSecond <;>
            rcases hrightMember with hrightFirst | hrightSecond
          · exfalso
            exact hvalueNe (hleftFirst.trans hrightFirst.symm)
          · subst first
            subst second
            simpa [finitePermutation,
              finPermutationOfListPermutation_apply_val] using hchecked'
          · subst second
            subst first
            have hsourceSymmetric :=
              extensionGraph_symmetric_of_parent_wellFormed
                parent mask left.val right.val hparent left.isLt right.isLt
            have htargetSymmetric := strongBridge_wellFormed_symmetric
              target (parent.length + 1)
              (finitePermutation right).val (finitePermutation left).val
              htarget (finitePermutation right).isLt
              (finitePermutation left).isLt
            have hcheckedFinite :
                edge (extensionGraph parent mask) right.val left.val =
                  edge target
                    (finitePermutation right).val
                    (finitePermutation left).val := by
              simpa [finitePermutation,
                finPermutationOfListPermutation_apply_val] using hchecked'
            have horiented :=
              hsourceSymmetric.trans
                (hcheckedFinite.trans htargetSymmetric)
            exact horiented
          · exfalso
            exact hvalueNe (hleftSecond.trans hrightSecond.symm)

/-- Propositional form of the strong bridge. -/
theorem graphIsomorphicFin_extensionGraph_of_isExtensionIsomorphism
    (parent target : Graph) (mask : Nat) (permutation : List Nat)
    (hparent : wellFormedGraph parent.length parent = true)
    (htarget : wellFormedGraph (parent.length + 1) target = true)
    (hiso :
      isExtensionIsomorphism parent mask target permutation = true) :
    GraphIsomorphicFin (extensionGraph parent mask) target := by
  exact ⟨graphIsoFin_extensionGraph_of_isExtensionIsomorphism
    parent target mask permutation hparent htarget hiso⟩

end LRATCatcher.Tests.R35
