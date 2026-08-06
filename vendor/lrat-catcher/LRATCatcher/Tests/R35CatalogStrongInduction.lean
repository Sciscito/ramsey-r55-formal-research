import LRATCatcher.Tests.R35CatalogFacts
import LRATCatcher.Tests.R35CatalogExtensionProperties
import LRATCatcher.Tests.R35CatalogExtensionStrongBridge
import LRATCatcher.Tests.R35CatalogCompletenessRel

/-!
  Concrete strong-isomorphism induction for the checked R(3,5) catalogues.

  All computational and structural ingredients are assembled here.  The
  single explicit hypothesis of `catalogue_step_complete_of_mask_transport`
  is the remaining mathematical transport lemma for neighbourhood masks.
-/

namespace LRATCatcher.Tests.R35

/-- A graph satisfies the exact two Boolean invariants used by a catalogue
level of the given order. -/
def GraphValidAt (order : Nat) (graph : Graph) : Prop :=
  wellFormedGraph order graph = true ∧ validGraph graph = true

/-- Every valid graph at `order` is strongly isomorphic to a listed
representative. -/
def StrongCatalogueComplete (order : Nat) (catalogue : List Graph) : Prop :=
  Complete (GraphValidAt order) GraphIsomorphicFin catalogue

/-- The native-checked transition certificate, strengthened to the genuinely
transitive finite-isomorphism relation. -/
theorem catalogue_checked_transition_complete_strong
    (order : Nat) (horder : order < extensionWitnesses.length)
    (representative : Graph)
    (hrepresentative : representative ∈ catalogues.getD order [])
    (mask : Nat) (hmask : CertifiedExtension representative mask) :
    ∃ target,
      target ∈ catalogues.getD (order + 1) [] ∧
      GraphIsomorphicFin (extensionGraph representative mask) target := by
  obtain ⟨hmaskBound, hmaskValid⟩ := hmask
  obtain ⟨target, htarget, permutation, hisomorphism⟩ :=
    checked_transition_covers_member
      (catalogues.getD order [])
      (catalogues.getD (order + 1) [])
      (extensionWitnesses.getD order [])
      representative mask
      (catalogue_transition_checked order horder)
      hrepresentative hmaskBound hmaskValid
  have hcatalogueOrder : order < catalogues.length := by
    rw [catalogues_length_eq]
    omega
  have htargetOrder : order + 1 < catalogues.length := by
    rw [catalogues_length_eq]
    omega
  have hrepresentativeChecked :=
    catalogue_entry_checked order hcatalogueOrder representative hrepresentative
  have htargetChecked :=
    catalogue_entry_checked (order + 1) htargetOrder target htarget
  have hrepresentativeLength : representative.length = order :=
    wellFormedGraph_length representative order hrepresentativeChecked.1
  have hrepresentativeSelf :
      wellFormedGraph representative.length representative = true := by
    rw [hrepresentativeLength]
    exact hrepresentativeChecked.1
  have htargetAtRepresentativeOrder :
      wellFormedGraph (representative.length + 1) target = true := by
    rw [hrepresentativeLength]
    exact htargetChecked.1
  exact ⟨target, htarget,
    graphIsomorphicFin_extensionGraph_of_isExtensionIsomorphism
      representative target mask permutation
      hrepresentativeSelf htargetAtRepresentativeOrder hisomorphism⟩

/-- The base catalogue is complete: a well-formed graph of order zero is the
empty graph, which is strongly isomorphic to itself. -/
theorem strongCatalogueComplete_zero :
    StrongCatalogueComplete 0 (catalogues.getD 0 []) := by
  intro graph hvalid
  have hlength : graph.length = 0 :=
    wellFormedGraph_length graph 0 hvalid.1
  have hgraph : graph = [] := List.eq_nil_of_length_eq_zero hlength
  subst graph
  refine ⟨[], ?_, GraphIsomorphicFin.refl []⟩
  rw [catalogue_zero_eq]
  simp

/-- One certified catalogue step, reduced to neighbourhood-mask transport.

The transport hypothesis is now the only non-computational missing link: an
isomorphism of valid parents must carry a bounded valid mask to a bounded
valid mask, and extend to an isomorphism after adding the new vertex.
-/
theorem catalogue_step_complete_of_mask_transport
    (order : Nat) (horder : order < extensionWitnesses.length)
    (hcomplete :
      StrongCatalogueComplete order (catalogues.getD order []))
    (transportMask : ∀ parent representative mask,
      GraphValidAt order parent →
      GraphValidAt order representative →
      GraphIsomorphicFin parent representative →
      CertifiedExtension parent mask →
      ∃ transportedMask,
        CertifiedExtension representative transportedMask ∧
        GraphIsomorphicFin
          (extensionGraph parent mask)
          (extensionGraph representative transportedMask)) :
    StrongCatalogueComplete (order + 1)
      (catalogues.getD (order + 1) []) := by
  intro graph hgraph
  let decomposition :=
    decomposeValidFinalVertex graph order hgraph.1 hgraph.2
  let parent := decomposition.decomposition.parent
  let mask := decomposition.decomposition.mask
  have hparentValidAt : GraphValidAt order parent := by
    exact ⟨decomposition.decomposition.parent_wellFormed,
      decomposition.parent_valid⟩
  obtain ⟨representative, hrepresentative, hparentIso⟩ :=
    hcomplete parent hparentValidAt
  have hcatalogueOrder : order < catalogues.length := by
    rw [catalogues_length_eq]
    omega
  have hrepresentativeValidAt : GraphValidAt order representative :=
    catalogue_entry_checked order hcatalogueOrder
      representative hrepresentative
  have hmaskCertified : CertifiedExtension parent mask := by
    refine ⟨?_, decomposition.extension_valid⟩
    rw [decomposition.decomposition.parent_length]
    exact decomposition.decomposition.mask_bound
  obtain ⟨transportedMask, htransportedCertified, htransportIso⟩ :=
    transportMask parent representative mask hparentValidAt
      hrepresentativeValidAt hparentIso hmaskCertified
  obtain ⟨target, htarget, htransitionIso⟩ :=
    catalogue_checked_transition_complete_strong
      order horder representative hrepresentative
      transportedMask htransportedCertified
  have hdecompositionIso :
      GraphIsomorphicFin graph (extensionGraph parent mask) := by
    exact graphIsomorphicFin_decomposeFinalVertex graph order hgraph.1
  exact ⟨target, htarget,
    GraphIsomorphicFin.trans
      (GraphIsomorphicFin.trans hdecompositionIso htransportIso)
      htransitionIso⟩

/-- Iterate the checked step from the empty graph through every transition in
the generated certificate.  Once mask transport is supplied, completeness of
all recorded catalogue levels follows without further assumptions. -/
theorem catalogueCompleteness_upto_of_mask_transport
    (transportMask : ∀ order parent representative mask,
      GraphValidAt order parent →
      GraphValidAt order representative →
      GraphIsomorphicFin parent representative →
      CertifiedExtension parent mask →
      ∃ transportedMask,
        CertifiedExtension representative transportedMask ∧
        GraphIsomorphicFin
          (extensionGraph parent mask)
          (extensionGraph representative transportedMask)) :
    ∀ order, order ≤ extensionWitnesses.length →
      StrongCatalogueComplete order (catalogues.getD order []) := by
  intro order
  induction order with
  | zero =>
      intro _
      exact strongCatalogueComplete_zero
  | succ order induction =>
      intro hbound
      apply catalogue_step_complete_of_mask_transport order (by omega)
      · exact induction (by omega)
      · exact transportMask order

end LRATCatcher.Tests.R35
