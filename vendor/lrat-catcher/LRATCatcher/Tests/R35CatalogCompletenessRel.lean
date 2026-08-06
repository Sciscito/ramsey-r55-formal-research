import LRATCatcher.Tests.R35CatalogCompletenessCore

/-!
  A relational form of the catalogue-completeness induction.

  The checked certificate describes a one-vertex extension by a relation
  (`isExtensionIsomorphism`) between a parent/mask pair and a target graph.
  Keeping that relation abstract avoids having to materialize an intermediate
  adjacency-list graph merely to compose two isomorphisms.
-/

namespace LRATCatcher.Tests.R35

/-- Generic one-step completeness induction driven by a checked extension
relation rather than by a materialized `extend` function. -/
theorem step_complete_rel
    {Small Large Mask : Type}
    (smallValid : Small → Prop) (largeValid : Large → Prop)
    (smallIso : Small → Small → Prop) (largeIso : Large → Large → Prop)
    (validExtension : Small → Mask → Prop)
    (parentRel : Large → Small → Mask → Prop)
    (extensionRel : Small → Mask → Large → Prop)
    (parents : List Small) (targets : List Large)
    (parentComplete : Complete smallValid smallIso parents)
    (decompose : ∀ object, largeValid object →
      ∃ parent : Small, ∃ mask : Mask,
        smallValid parent ∧ parentRel object parent mask)
    (liftParentIso : ∀ (object : Large) (parent representative : Small)
        (mask : Mask),
      largeValid object →
      parentRel object parent mask →
      smallIso parent representative →
      ∃ transportedMask,
        validExtension representative transportedMask ∧
        ∀ target, extensionRel representative transportedMask target →
          largeIso object target)
    (transitionComplete : ∀ representative : Small,
      representative ∈ parents → ∀ mask : Mask,
      validExtension representative mask →
      ∃ target, target ∈ targets ∧
        extensionRel representative mask target) :
    Complete largeValid largeIso targets := by
  intro object hvalid
  obtain ⟨parent, mask, hparentValid, hparentRel⟩ := decompose object hvalid
  obtain ⟨representative, hrepresentative, hparentIso⟩ :=
    parentComplete parent hparentValid
  obtain ⟨transportedMask, htransportedValid, hlift⟩ :=
    liftParentIso object parent representative mask hvalid hparentRel hparentIso
  obtain ⟨target, htarget, htransition⟩ :=
    transitionComplete representative hrepresentative transportedMask
      htransportedValid
  exact ⟨target, htarget, hlift target htransition⟩

/-- Exact propositional predicate consumed by the generated transition table.
The bound is part of the predicate because `validPairs` enumerates precisely
the masks in `List.range (2 ^ parent.length)`. -/
def CertifiedExtension (parent : Graph) (mask : Nat) : Prop :=
  mask < 2 ^ parent.length ∧ validExtension parent mask = true

/-- A parent/mask pair is related to a target when the certificate retains a
concrete permutation accepted by the independent Boolean checker. -/
def CheckedExtensionRel (parent : Graph) (mask : Nat) (target : Graph) : Prop :=
  ∃ permutation,
    isExtensionIsomorphism parent mask target permutation = true

/-- The global native-checked certificate supplies exactly the transition
hypothesis required by `step_complete_rel` at every recorded order. -/
theorem catalogue_checked_transition_complete
    (order : Nat) (horder : order < extensionWitnesses.length)
    (representative : Graph)
    (hrepresentative : representative ∈ catalogues.getD order [])
    (mask : Nat) (hmask : CertifiedExtension representative mask) :
    ∃ target,
      target ∈ catalogues.getD (order + 1) [] ∧
      CheckedExtensionRel representative mask target := by
  obtain ⟨hbound, hvalid⟩ := hmask
  exact checked_transition_covers_member
    (catalogues.getD order [])
    (catalogues.getD (order + 1) [])
    (extensionWitnesses.getD order [])
    representative mask
    (catalogue_transition_checked order horder)
    hrepresentative hbound hvalid

end LRATCatcher.Tests.R35
