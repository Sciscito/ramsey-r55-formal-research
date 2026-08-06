import LRATCatcher.Tests.R35CatalogCertificate

/-!
  Semantic scaffolding for turning the checked R(3,5,n) extension tables into
  a genuine completeness theorem.

  The computational certificate proves that every valid one-vertex extension
  of every listed representative has a checked isomorphism to a representative
  at the next order.  The generic `step_complete` theorem below isolates the
  remaining mathematical ingredient: deleting the last vertex of an arbitrary
  graph, transporting an isomorphism of its parent across the extension, and
  composing graph isomorphisms.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-! ## Generic semantic induction -/

/-- Every valid object is isomorphic to an object in `catalogue`. -/
def Complete {α : Type} (valid : α → Prop) (iso : α → α → Prop)
    (catalogue : List α) : Prop :=
  ∀ object, valid object →
    ∃ representative, representative ∈ catalogue ∧ iso object representative

/-- Generic one-vertex-extension induction.

`liftParentIso` is the substantive graph-theoretic lemma: after an arbitrary
large object is decomposed as an extension of `parent`, an isomorphism from
`parent` to a catalogue representative can be lifted by transporting the new
vertex's neighbourhood mask.  The lifted extension must satisfy the exact
predicate consumed by the checked transition table.
-/
theorem step_complete
    {Small Large Mask : Type}
    (smallValid : Small → Prop) (largeValid : Large → Prop)
    (smallIso : Small → Small → Prop) (largeIso : Large → Large → Prop)
    (validExtension : Small → Mask → Prop)
    (parents : List Small) (targets : List Large)
    (extend : Small → Mask → Large)
    (parentComplete : Complete smallValid smallIso parents)
    (decompose : ∀ object, largeValid object →
      ∃ parent mask, smallValid parent ∧ largeIso object (extend parent mask))
    (liftParentIso : ∀ object parent representative mask,
      largeValid object →
      largeIso object (extend parent mask) →
      smallIso parent representative →
      ∃ transportedMask,
        validExtension representative transportedMask ∧
        largeIso object (extend representative transportedMask))
    (transitionComplete : ∀ representative,
      representative ∈ parents → ∀ mask,
      validExtension representative mask →
      ∃ target, target ∈ targets ∧
        largeIso (extend representative mask) target)
    (isoTrans : ∀ left middle right,
      largeIso left middle → largeIso middle right → largeIso left right) :
    Complete largeValid largeIso targets := by
  intro object hvalid
  obtain ⟨parent, mask, hparentValid, hdecompose⟩ := decompose object hvalid
  obtain ⟨representative, hrepresentative, hparentIso⟩ :=
    parentComplete parent hparentValid
  obtain ⟨transportedMask, htransportedValid, hlifted⟩ :=
    liftParentIso object parent representative mask hvalid hdecompose hparentIso
  obtain ⟨target, htarget, htransition⟩ :=
    transitionComplete representative hrepresentative transportedMask
      htransportedValid
  exact ⟨target, htarget, isoTrans object _ target hlifted htransition⟩

/-! ## Concrete semantic vocabulary for the generated graph tables -/

/-- Checked adjacency-matrix isomorphism between two materialized graphs. -/
def isGraphIsomorphism
    (source target : Graph) (permutation : List Nat) : Bool :=
  let order := source.length
  target.length == order &&
    isPermutation permutation order &&
    (subsets order 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          edge source left right ==
            edge target
              (permutation.getD left order)
              (permutation.getD right order)
      | _ => false

/-- Propositional graph isomorphism, with the concrete permutation retained as
an independently checkable witness. -/
def GraphIso (source target : Graph) : Prop :=
  ∃ permutation, isGraphIsomorphism source target permutation = true

/-- Semantic completeness statement intended for each generated catalogue. -/
def CatalogueComplete (order : Nat) (catalogue : List Graph) : Prop :=
  ∀ graph,
    wellFormedGraph order graph = true →
    validGraph graph = true →
    ∃ representative,
      representative ∈ catalogue ∧ GraphIso graph representative

/-! ## Extracting transition coverage from the Boolean certificate -/

theorem mem_validPairs
    (parents : List Graph) (parentIndex mask : Nat)
    (hparent : parentIndex < parents.length)
    (hmask : mask < 2 ^ (parents.getD parentIndex []).length)
    (hvalid : validExtension (parents.getD parentIndex []) mask = true) :
    (parentIndex, mask) ∈ validPairs parents := by
  simp only [validPairs, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter]
  exact ⟨parentIndex, hparent, mask, ⟨hmask, hvalid⟩, rfl⟩

/-- Equal-length zipping does not drop an element of the left list. -/
theorem exists_mem_zip_of_mem_left
    {α β : Type} {left : List α} {right : List β} {value : α}
    (hvalue : value ∈ left) (hlength : left.length = right.length) :
    ∃ paired, (value, paired) ∈ left.zip right := by
  have hmapped : value ∈ (left.zip right).map Prod.fst := by
    rw [List.map_fst_zip (Nat.le_of_eq hlength)]
    exact hvalue
  obtain ⟨pair, hpair, hpfirst⟩ := List.mem_map.mp hmapped
  rcases pair with ⟨first, second⟩
  simp only at hpfirst
  subst first
  exact ⟨second, hpair⟩

/-- A successful generated transition check yields an explicit checked target
for every valid mask of every indexed parent representative. -/
theorem checked_transition_covers
    (parents targets : List Graph) (witnesses : List ExtensionWitness)
    (parentIndex mask : Nat)
    (hcheck : checkTransition parents targets witnesses = true)
    (hparent : parentIndex < parents.length)
    (hmask : mask < 2 ^ (parents.getD parentIndex []).length)
    (hvalid : validExtension (parents.getD parentIndex []) mask = true) :
    ∃ targetIndex permutation,
      targetIndex < targets.length ∧
      isExtensionIsomorphism
        (parents.getD parentIndex []) mask
        (targets.getD targetIndex []) permutation = true := by
  simp only [checkTransition, Bool.and_eq_true] at hcheck
  let pairs := validPairs parents
  have hpair : (parentIndex, mask) ∈ pairs := by
    exact mem_validPairs parents parentIndex mask hparent hmask hvalid
  obtain ⟨witness, hzipped⟩ :=
    exists_mem_zip_of_mem_left hpair (beq_iff_eq.mp hcheck.1)
  have hwitness := List.all_eq_true.mp hcheck.2
    ((parentIndex, mask), witness) hzipped
  unfold checkWitness at hwitness
  change
    (((witness.parent == parentIndex && witness.mask == mask) &&
        decide (witness.target < targets.length)) &&
      isExtensionIsomorphism
        (parents.getD witness.parent []) witness.mask
        (targets.getD witness.target []) witness.permutation) = true
    at hwitness
  rw [Bool.and_eq_true] at hwitness
  have htargetAnd := hwitness.1
  have hiso := hwitness.2
  rw [Bool.and_eq_true] at htargetAnd
  have hfieldsAnd := htargetAnd.1
  rw [Bool.and_eq_true] at hfieldsAnd
  have hwp := hfieldsAnd.1
  have hwm := hfieldsAnd.2
  have htarget : witness.target < targets.length :=
    of_decide_eq_true htargetAnd.2
  have hwp' : witness.parent = parentIndex := by
    exact beq_iff_eq.mp hwp
  have hwm' : witness.mask = mask := by
    exact beq_iff_eq.mp hwm
  subst parentIndex
  subst mask
  exact ⟨witness.target, witness.permutation, htarget, hiso⟩

/-- Membership-oriented form of `checked_transition_covers`, matching the
`transitionComplete` hypothesis of `step_complete`. -/
theorem checked_transition_covers_member
    (parents targets : List Graph) (witnesses : List ExtensionWitness)
    (representative : Graph) (mask : Nat)
    (hcheck : checkTransition parents targets witnesses = true)
    (hrepresentative : representative ∈ parents)
    (hmask : mask < 2 ^ representative.length)
    (hvalid : validExtension representative mask = true) :
    ∃ target, target ∈ targets ∧
      ∃ permutation,
        isExtensionIsomorphism representative mask target permutation = true := by
  obtain ⟨parentIndex, hparent, hget⟩ :=
    List.getElem_of_mem hrepresentative
  have hgetD : parents.getD parentIndex [] = representative := by
    rw [← List.getElem_eq_getD (l := parents) (i := parentIndex)
      (h := hparent) []]
    exact hget
  have hmask' : mask < 2 ^ (parents.getD parentIndex []).length := by
    rw [hgetD]
    exact hmask
  have hvalid' :
      validExtension (parents.getD parentIndex []) mask = true := by
    rw [hgetD]
    exact hvalid
  obtain ⟨targetIndex, permutation, htarget, hiso⟩ :=
    checked_transition_covers parents targets witnesses parentIndex mask hcheck
      hparent hmask' hvalid'
  have htargetMem : targets.getD targetIndex [] ∈ targets := by
    rw [← List.getElem_eq_getD (l := targets) (i := targetIndex)
      (h := htarget) []]
    exact List.getElem_mem htarget
  rw [hgetD] at hiso
  exact ⟨targets.getD targetIndex [], htargetMem, permutation, hiso⟩

/-- Project the machine-checked global audit onto one concrete transition. -/
theorem catalogue_transition_checked (order : Nat)
    (horder : order < extensionWitnesses.length) :
    checkTransition
      (catalogues.getD order [])
      (catalogues.getD (order + 1) [])
      (extensionWitnesses.getD order []) = true := by
  have hchecked := r35_catalogue_extensions_checked
  unfold checkCatalogues at hchecked
  rw [Bool.and_eq_true] at hchecked
  exact List.all_eq_true.mp hchecked.2 order (List.mem_range.mpr horder)

end LRATCatcher.Tests.R35
