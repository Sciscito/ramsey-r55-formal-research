import LRATCatcher.Tests.R35CatalogStrongInduction
import LRATCatcher.Tests.R35CatalogMaskTransport
import LRATCatcher.Tests.R35CatalogExtensionRoundTrip
import LRATCatcher.Tests.R35CatalogValidityInvariant

/-!
  End-to-end semantic completeness of the checked R(3,5,n) catalogues.

  This module discharges the final neighbourhood-mask transport hypothesis and
  instantiates the certified induction through every generated level.
-/

namespace LRATCatcher.Tests.R35

/-- Transporting a bounded valid mask along a strong parent isomorphism
preserves both its validity and the isomorphism class of the extension. -/
theorem certifiedMaskTransport
    (order : Nat) (parent representative : Graph) (mask : Nat)
    (hparent : GraphValidAt order parent)
    (hrepresentative : GraphValidAt order representative)
    (hisomorphic : GraphIsomorphicFin parent representative)
    (hmask : CertifiedExtension parent mask) :
    ∃ transported,
      CertifiedExtension representative transported ∧
      GraphIsomorphicFin
        (extensionGraph parent mask)
        (extensionGraph representative transported) := by
  obtain ⟨isomorphism⟩ := hisomorphic
  let transported := transportedMask isomorphism mask
  have hparentLength : parent.length = order :=
    wellFormedGraph_length parent order hparent.1
  have hrepresentativeLength : representative.length = order :=
    wellFormedGraph_length representative order hrepresentative.1
  have hparentSelf : wellFormedGraph parent.length parent = true := by
    rw [hparentLength]
    exact hparent.1
  have hrepresentativeSelf :
      wellFormedGraph representative.length representative = true := by
    rw [hrepresentativeLength]
    exact hrepresentative.1
  have htransportedBound : transported < 2 ^ representative.length := by
    exact transportedMask_lt_targetLength isomorphism mask
  have hsourceWellFormed :
      wellFormedGraph (parent.length + 1) (extensionGraph parent mask) = true :=
    extensionGraph_wellFormed
      parent parent.length mask hparentSelf hmask.1
  have htargetWellFormed :
      wellFormedGraph (representative.length + 1)
        (extensionGraph representative transported) = true :=
    extensionGraph_wellFormed representative representative.length transported
      hrepresentativeSelf htransportedBound
  have hsourceValid : validGraph (extensionGraph parent mask) = true :=
    extensionGraph_validGraph parent mask hparent.2 hmask.2
  let extensionIsomorphism :
      GraphIsoFin
        (extensionGraph parent mask)
        (extensionGraph representative transported) :=
    graphIsoFin_extensionGraph_transportedMask isomorphism mask
  have htargetValid :
      validGraph (extensionGraph representative transported) = true := by
    apply validGraph_of_graphIsoFin extensionIsomorphism
    · simpa only [extensionGraph_length] using hsourceWellFormed
    · simpa only [extensionGraph_length] using htargetWellFormed
    · exact hsourceValid
  have htransportedValid :
      validExtension representative transported = true :=
    validExtension_of_extensionGraph_valid
      representative transported hrepresentativeSelf
      htransportedBound htargetValid
  exact ⟨transported, ⟨htransportedBound, htransportedValid⟩,
    ⟨extensionIsomorphism⟩⟩

/-- Every catalogue level covered by the generated transition certificate is
semantically exhaustive up to strong finite graph isomorphism. -/
theorem r35_catalogues_complete :
    ∀ order, order ≤ extensionWitnesses.length →
      StrongCatalogueComplete order (catalogues.getD order []) :=
  catalogueCompleteness_upto_of_mask_transport certifiedMaskTransport

/-- The checked certificate contains transitions 0→1 through 9→10. -/
theorem extensionWitnesses_length_eq_ten :
    extensionWitnesses.length = 10 := by
  native_decide

/-- Main result: the generated order-10 R(3,5) catalogue is exhaustive, not
merely extension-closed for its listed representatives. -/
theorem r35_catalogue_order_ten_complete :
    StrongCatalogueComplete 10 (catalogues.getD 10 []) := by
  apply r35_catalogues_complete 10
  rw [extensionWitnesses_length_eq_ten]
  exact Nat.le_refl 10

#print axioms r35_catalogue_order_ten_complete

end LRATCatcher.Tests.R35
