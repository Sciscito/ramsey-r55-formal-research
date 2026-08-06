import LRATCatcher.Tests.R35CatalogCompletenessCore

/-!
  Small semantic projections of the native-checked global catalogue audit.
-/

namespace LRATCatcher.Tests.R35

/-- The generated catalogue sequence has exactly one more level than the
transition-witness sequence. -/
theorem catalogues_length_eq :
    catalogues.length = extensionWitnesses.length + 1 := by
  have hchecked := r35_catalogue_extensions_checked
  unfold checkCatalogues at hchecked
  rw [Bool.and_eq_true] at hchecked
  have hprefix := hchecked.1
  rw [Bool.and_eq_true] at hprefix
  exact beq_iff_eq.mp hprefix.1

/-- Every graph stored at a checked catalogue level passes both independent
Boolean audits used by the certificate. -/
theorem catalogue_entry_checked
    (order : Nat) (horder : order < catalogues.length)
    (graph : Graph) (hgraph : graph ∈ catalogues.getD order []) :
    wellFormedGraph order graph = true ∧ validGraph graph = true := by
  have hchecked := r35_catalogue_extensions_checked
  unfold checkCatalogues at hchecked
  rw [Bool.and_eq_true] at hchecked
  have hprefix := hchecked.1
  rw [Bool.and_eq_true] at hprefix
  have hdata := hprefix.2
  have hlevel := List.all_eq_true.mp hdata order (List.mem_range.mpr horder)
  have hentry := List.all_eq_true.mp hlevel graph hgraph
  rw [Bool.and_eq_true] at hentry
  exact hentry

/-- The generated base catalogue is the singleton empty graph. -/
theorem catalogue_zero_eq : catalogues.getD 0 [] = [[]] := by
  native_decide

end LRATCatcher.Tests.R35
