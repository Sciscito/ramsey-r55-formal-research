import LRATCatcher.Tests.R35CatalogGraphIsoBridge
import LRATCatcher.Tests.R35UpperBound
import LRATCatcher.Tests.R44RootedGen4416CoverData
import LRATCatcher.Tests.R44RootedMixedClauses

/-!
  # Certified isomorphism cover for the rooted `gen4416` classifier

  The LRAT classifier returns one of 64 labelled rooted rows.  The generated
  data supplies one explicit permutation from each row to one of the two
  complete order-sixteen graphs in `gen4416`, as well as an explicit
  self-complementing permutation for each target.  This module independently
  decodes the ternary graph identifiers and checks every permutation in Lean.
-/

namespace LRATCatcher.Tests.R44RootedGen4416Cover

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedGen4416Semantics
open LRATCatcher.Tests.R44RootedGen4416CoverData
open LRATCatcher.Tests.R44RootedMixedClauses

abbrev order : Nat := 16
abbrev edgeCount : Nat := order * (order - 1) / 2

/-- Decode a true/raw edge from a complete HOL-style base-three graph id.
The variable index is the row-major upper-triangle index used by `edgeVar`.
-/
def ternaryColoring (encoded index : Nat) : Bool :=
  (encoded / 3 ^ (edgeCount - 1 - index)) % 3 == 1

/-- One of the two materialized `gen4416` graphs. -/
def gen4416Graph (targetIndex : Nat) : Graph :=
  coloringGraph order
    (ternaryColoring (gen4416GraphIds.getD targetIndex 0))

/-- Canonical rooted graph represented by one classifier row. -/
def rootedModelGraph (model : AllowedModel) : Graph :=
  coloringGraph order
    (canonicalColoring model.leftSelector model.antiSelector model.mask)

def defaultAllowedModel : AllowedModel :=
  { leftSelector := 0, antiSelector := 0, mask := 0 }

/-- Independent Boolean check for one of the 64 generated cover witnesses. -/
def checkAllowedModelCover (rowIndex : Nat) : Bool :=
  let model := allowedModels.getD rowIndex defaultAllowedModel
  let targetIndex := gen4416TargetIndexForSelectors
    model.leftSelector model.antiSelector
  decide (targetIndex < gen4416GraphIds.length) &&
    isGraphIsomorphism
      (rootedModelGraph model)
      (gen4416Graph targetIndex)
      (gen4416CoverPermutations.getD rowIndex [])

def checkAllAllowedModelCovers : Bool :=
  allowedModels.length == gen4416CoverPermutations.length &&
    (List.range allowedModels.length).all checkAllowedModelCover

theorem gen4416_graph_count : gen4416GraphIds.length = 2 := by
  native_decide

theorem gen4416_cover_count : gen4416CoverPermutations.length = 64 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem allowed_model_covers_checked : checkAllAllowedModelCovers = true := by
  native_decide

/-- Every row returned by the LRAT classifier has a checked strong graph
isomorphism to one of the two materialized `gen4416` graphs. -/
theorem allowed_model_covered (model : AllowedModel)
    (hmodel : List.Mem model allowedModels) :
    Exists fun targetIndex =>
      targetIndex < gen4416GraphIds.length /\
        GraphIsomorphicFin (rootedModelGraph model)
          (gen4416Graph targetIndex) := by
  obtain ⟨rowIndex, hrowIndex, hrow⟩ := List.getElem_of_mem hmodel
  have hgetD : allowedModels.getD rowIndex defaultAllowedModel = model := by
    rw [← List.getElem_eq_getD (l := allowedModels) (i := rowIndex)
      (h := hrowIndex) defaultAllowedModel]
    exact hrow
  have hchecked := allowed_model_covers_checked
  unfold checkAllAllowedModelCovers at hchecked
  rw [Bool.and_eq_true] at hchecked
  have hrowChecked := List.all_eq_true.mp hchecked.2 rowIndex
    (List.mem_range.mpr hrowIndex)
  unfold checkAllowedModelCover at hrowChecked
  rw [hgetD, Bool.and_eq_true] at hrowChecked
  let targetIndex := gen4416TargetIndexForSelectors
    model.leftSelector model.antiSelector
  refine ⟨targetIndex, of_decide_eq_true hrowChecked.1, ?_⟩
  refine ⟨isGraphIsomorphism_toGraphIsoFin hrowChecked.2 ?_ ?_⟩
  · simpa [rootedModelGraph] using
      coloringGraph_wellFormed order
        (canonicalColoring model.leftSelector model.antiSelector model.mask)
  · simpa [rootedModelGraph, gen4416Graph] using
      coloringGraph_wellFormed order
        (ternaryColoring (gen4416GraphIds.getD targetIndex 0))

/-- Graph obtained by exchanging the two colors in a decoded target. -/
def complementGen4416Graph (targetIndex : Nat) : Graph :=
  coloringGraph order fun index =>
    !(ternaryColoring (gen4416GraphIds.getD targetIndex 0) index)

def checkGen4416SelfComplement (targetIndex : Nat) : Bool :=
  isGraphIsomorphism
    (complementGen4416Graph targetIndex)
    (gen4416Graph targetIndex)
    (gen4416SelfComplementPermutations.getD targetIndex [])

def checkAllGen4416SelfComplements : Bool :=
  gen4416GraphIds.length == gen4416SelfComplementPermutations.length &&
    (List.range gen4416GraphIds.length).all checkGen4416SelfComplement

theorem gen4416_self_complement_count :
    gen4416SelfComplementPermutations.length = 2 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gen4416_self_complements_checked :
    checkAllGen4416SelfComplements = true := by
  native_decide

/-- Both `gen4416` targets are self-complementary, with an explicit checked
strong isomorphism. -/
theorem gen4416_self_complementary (targetIndex : Nat)
    (htarget : targetIndex < gen4416GraphIds.length) :
    GraphIsomorphicFin (complementGen4416Graph targetIndex)
      (gen4416Graph targetIndex) := by
  have hchecked := gen4416_self_complements_checked
  unfold checkAllGen4416SelfComplements at hchecked
  rw [Bool.and_eq_true] at hchecked
  have htargetChecked := List.all_eq_true.mp hchecked.2 targetIndex
    (List.mem_range.mpr htarget)
  refine ⟨isGraphIsomorphism_toGraphIsoFin htargetChecked ?_ ?_⟩
  · simpa [complementGen4416Graph] using
      coloringGraph_wellFormed order (fun index =>
        !(ternaryColoring
          (gen4416GraphIds.getD targetIndex 0) index))
  · simpa [complementGen4416Graph, gen4416Graph] using
      coloringGraph_wellFormed order
        (ternaryColoring (gen4416GraphIds.getD targetIndex 0))

#print axioms allowed_model_covers_checked
#print axioms allowed_model_covered
#print axioms gen4416_self_complementary

end LRATCatcher.Tests.R44RootedGen4416Cover
