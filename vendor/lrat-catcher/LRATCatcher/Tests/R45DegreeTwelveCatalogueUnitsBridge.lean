import LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation
import LRATCatcher.Tests.R45DegreeTwelveSelectorBridge
import LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-!
  # The 66 catalogue units of the degree-twelve guarded master

  For each valid selector code, the Python generator emits one unit for every
  pair among local vertices `0, ..., 11`.  Positive DIMACS literals are red
  edges and negative literals are blue edges; all variables use the global
  `edgeVar 24` indexing of the fixed-root CNF.

  This module proves the exact semantic bridge.  A strong graph isomorphism
  from the actual red neighborhood to the selected catalogue representative
  is inverted into a representative-to-neighborhood permutation.  That local
  permutation is then lifted to a genuine permutation of `Fin 25`.  The
  resulting reduced assignment, extended by the selected four-bit code,
  satisfies all 66 direct units.
-/

namespace LRATCatcher.Tests.R45DegreeTwelveCatalogueUnitsBridge

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45RootDegreeCore
open LRATCatcher.Tests.R45DegreeTwelveBridge
open LRATCatcher.Tests.R45DegreeTwelveSelectorBridge
open LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation
open LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-! ## The reduced `K_24` assignment -/

theorem localEdgePair_edgeVar_twentyFour (left right : Fin 24)
    (hordered : left < right) :
    localEdgePair 24 (edgeVar 24 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Pull an ambient coloring back along labels `1, ..., 24` after a genuine
ambient permutation. -/
def reducedAssignment (permutation : FinPermutation 25)
    (coloring : Nat → Bool) : Nat → Bool :=
  inducedColoring 24 (permutedNonRootEmbedding permutation) coloring false

theorem reducedAssignment_edgeVar (permutation : FinPermutation 25)
    (coloring : Nat → Bool) (left right : Fin 24)
    (hordered : left < right) :
    reducedAssignment permutation coloring
        (edgeVar 24 left.val right.val) =
      LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
        (permutedNonRootEmbedding permutation left).val
        (permutedNonRootEmbedding permutation right).val := by
  simpa [reducedAssignment] using
    inducedColoring_edgeVar (permutedNonRootEmbedding permutation)
      coloring false localEdgePair_edgeVar_twentyFour left right hordered

/-- On the first twelve reduced vertices, the global permutation reads the
actual red-neighborhood graph through its chosen local permutation. -/
theorem reducedAssignment_global_red
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation bluePermutation : FinPermutation 12)
    (left right : Fin 12) (hordered : left < right) :
    reducedAssignment
        (degreeTwelveGlobalPermutation coloring root hroot hdegree
          redPermutation bluePermutation) coloring
        (edgeVar 24 left.val right.val) =
      edge (redDegreeTwelveGraph coloring root hdegree)
        (redPermutation left).val (redPermutation right).val := by
  let global := degreeTwelveGlobalPermutation coloring root hroot hdegree
    redPermutation bluePermutation
  let left24 : Fin 24 := ⟨left.val, by omega⟩
  let right24 : Fin 24 := ⟨right.val, by omega⟩
  have hordered24 : left24 < right24 := by
    simpa [left24, right24] using hordered
  have hne : redPermutation left ≠ redPermutation right := by
    intro hequal
    exact (by
      have := FinPermutation.injective redPermutation hequal
      omega)
  calc
    reducedAssignment global coloring
        (edgeVar 24 left.val right.val) =
        LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
          (permutedNonRootEmbedding global left24).val
          (permutedNonRootEmbedding global right24).val := by
      simpa [left24, right24] using
        reducedAssignment_edgeVar global coloring left24 right24 hordered24
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
        (redDegreeTwelveEmbedding coloring root hdegree
          (redPermutation left)).val
        (redDegreeTwelveEmbedding coloring root hdegree
          (redPermutation right)).val := by
      simp [global, permutedNonRootEmbedding, canonicalNonRootVertex,
        left24, right24]
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 12
        (redDegreeTwelveColoring coloring root hdegree)
          (redPermutation left).val (redPermutation right).val := by
      symm
      simpa [redDegreeTwelveColoring] using
        ramseyEdge_inducedColoring
          (redDegreeTwelveEmbedding coloring root hdegree)
          coloring false localEdgePair_edgeVar_twelve
          (redPermutation left) (redPermutation right) hne
    _ = coloringEdge 12
        (redDegreeTwelveColoring coloring root hdegree)
          (redPermutation left).val (redPermutation right).val := by rfl
    _ = edge (redDegreeTwelveGraph coloring root hdegree)
        (redPermutation left).val (redPermutation right).val := by
      symm
      simpa [redDegreeTwelveGraph] using
        edge_coloringGraph 12
          (redDegreeTwelveColoring coloring root hdegree)
          (redPermutation left) (redPermutation right)

/-! ## Exact direct-unit list -/

/-- The complete unit cube emitted for selector `code`.  This is exactly the
generator's `graph_units`: Python-combination order, `edgeVar 24`, and direct
red/blue polarity. -/
def catalogueDirectUnits (code : Nat) : List Int :=
  let graph := catalogueRepresentative code
  (upperPairs 12).map fun pair =>
    edgeUnit pair.1 pair.2 (edge graph pair.1 pair.2)

theorem upperPairs_twelve_ordered
    (pair : Nat × Nat) (hpair : pair ∈ upperPairs 12) :
    pair.1 < pair.2 ∧ pair.2 < 12 := by
  native_decide +revert

/-- There is one direct unit for every edge of `K_12`. -/
theorem catalogueDirectUnits_length (code : Nat) :
    (catalogueDirectUnits code).length = 66 := by
  simp [catalogueDirectUnits]
  native_decide

/-- All red-block variables lie below the four selector variables. -/
theorem redEdgeVar_below_selectorStart (left right : Fin 12) :
    edgeVar 24 left.val right.val < selectorStart := by
  native_decide +revert

/-! ## Inverting the catalogue isomorphism -/

def reindexPermutation {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder) :
    FinPermutation targetOrder := by
  subst targetOrder
  exact permutation

@[simp] theorem reindexPermutation_apply_val
    {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder)
    (vertex : Fin targetOrder) :
    (reindexPermutation horder permutation vertex).val =
      (permutation (Fin.cast horder.symm vertex)).val := by
  subst targetOrder
  rfl

/-- The unit-facing orientation of the catalogue isomorphism.  The
permutation sends each catalogue label to the corresponding source-graph
vertex. -/
structure CatalogueDirectUnitWitness (source : Graph) (code : Nat) where
  permutation : FinPermutation 12
  fixed_edge : ∀ left right : Fin 12,
    edge source (permutation left).val (permutation right).val =
      edge (catalogueRepresentative code) left.val right.val

/-- Invert a strong source-to-catalogue isomorphism into the orientation
needed by the direct unit cube. -/
theorem graphIsomorphic_catalogueDirectUnitWitness
    {source : Graph} {code : Nat}
    (hsourceLength : source.length = 12)
    (hisomorphic : GraphIsomorphicFin source
      (catalogueRepresentative code)) :
    Nonempty (CatalogueDirectUnitWitness source code) := by
  obtain ⟨isomorphism⟩ := hisomorphic
  have hisomorphismOrder : isomorphism.order = 12 := by
    exact isomorphism.sourceOrder.symm.trans hsourceLength
  let sourceToCatalogue : FinPermutation 12 :=
    reindexPermutation hisomorphismOrder isomorphism.permutation
  let catalogueToSource : FinPermutation 12 := sourceToCatalogue.symm
  have hmap (left right : Fin 12) :
      edge source left.val right.val =
        edge (catalogueRepresentative code)
          (sourceToCatalogue left).val
          (sourceToCatalogue right).val := by
    have hedge := isomorphism.map_edge
      (Fin.cast hisomorphismOrder.symm left)
      (Fin.cast hisomorphismOrder.symm right)
    simpa [sourceToCatalogue, hisomorphismOrder] using hedge
  refine ⟨{
    permutation := catalogueToSource
    fixed_edge := ?_
  }⟩
  intro left right
  have hedge := hmap (sourceToCatalogue.symm left)
    (sourceToCatalogue.symm right)
  simpa [catalogueToSource] using hedge

namespace CatalogueDirectUnitWitness

/-- Literal-level semantics of all 66 generated units. -/
theorem allUnitsSatisfied
    {source : Graph} {code : Nat}
    (witness : CatalogueDirectUnitWitness source code)
    (assignment : Nat → Bool)
    (hassignment : ∀ left right : Fin 12, left < right →
      assignment (edgeVar 24 left.val right.val) =
        edge source
          (witness.permutation left).val
          (witness.permutation right).val) :
    AllUnitsSatisfied assignment (catalogueDirectUnits code) := by
  intro literal hliteral
  simp only [catalogueDirectUnits, List.mem_map] at hliteral
  obtain ⟨pair, hpair, hequal⟩ := hliteral
  obtain ⟨horderedNat, hright⟩ := upperPairs_twelve_ordered pair hpair
  let left : Fin 12 := ⟨pair.1, by omega⟩
  let right : Fin 12 := ⟨pair.2, hright⟩
  have hordered : left < right := by
    simpa [left, right] using horderedNat
  rw [← hequal]
  apply (edgeUnit_satisfied_iff assignment pair.1 pair.2
    (edge (catalogueRepresentative code) pair.1 pair.2)).2
  calc
    assignment (edgeVar 24 pair.1 pair.2) =
        edge source
          (witness.permutation left).val
          (witness.permutation right).val := by
      simpa [left, right] using hassignment left right hordered
    _ = edge (catalogueRepresentative code) pair.1 pair.2 := by
      simpa [left, right] using witness.fixed_edge left right

end CatalogueDirectUnitWitness

/-! ## One encoded assignment carrying both selector and unit semantics -/

/-- The base edge assignment, globally relabeled by the catalogue witness
and extended with its four-bit selector code.  The blue block needs no local
catalogue yet, so its permutation is the identity. -/
noncomputable def encodedCatalogueAssignment
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation : FinPermutation 12) (code : Nat) : Nat → Bool :=
  extendWithDegreeTwelveCode
    (reducedAssignment
      (degreeTwelveGlobalPermutation coloring root hroot hdegree
        redPermutation (FinPermutation.refl 12)) coloring)
    code

theorem encodedCatalogueAssignment_redEdge
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation : FinPermutation 12) (code : Nat)
    (left right : Fin 12) (hordered : left < right) :
    encodedCatalogueAssignment coloring root hroot hdegree
        redPermutation code (edgeVar 24 left.val right.val) =
      edge (redDegreeTwelveGraph coloring root hdegree)
        (redPermutation left).val (redPermutation right).val := by
  rw [encodedCatalogueAssignment,
    extendWithDegreeTwelveCode_of_lt _ _ _
      (redEdgeVar_below_selectorStart left right)]
  exact reducedAssignment_global_red coloring root hroot hdegree
    redPermutation (FinPermutation.refl 12) left right hordered

/-- The packaged result consumed by guarded-master semantics: a valid code,
its representative-to-neighborhood permutation, and all 66 selected units. -/
structure EncodedCatalogueUnitCase
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) where
  code : Nat
  valid : code < catalogueCodeCount
  redPermutation : FinPermutation 12
  units : AllUnitsSatisfied
    (encodedCatalogueAssignment coloring root hroot hdegree
      redPermutation code)
    (catalogueDirectUnits code)

namespace EncodedCatalogueUnitCase

noncomputable def assignment
    {coloring : Nat → Bool} {root : Nat} {hroot : root < 25}
    {hdegree : (colorNeighbors coloring root false).length = 12}
    (unitCase : EncodedCatalogueUnitCase coloring root hroot hdegree) :
    Nat → Bool :=
  encodedCatalogueAssignment coloring root hroot hdegree
    unitCase.redPermutation unitCase.code

theorem selector_bits
    {coloring : Nat → Bool} {root : Nat} {hroot : root < 25}
    {hdegree : (colorNeighbors coloring root false).length = 12}
    (unitCase : EncodedCatalogueUnitCase coloring root hroot hdegree) :
    decodeSelectorBits unitCase.assignment =
      selectorCodeBits unitCase.code := by
  exact decodeSelectorBits_extendWithDegreeTwelveCode _ _

theorem selected_guard_false
    {coloring : Nat → Bool} {root : Nat} {hroot : root < 25}
    {hdegree : (colorNeighbors coloring root false).length = 12}
    (unitCase : EncodedCatalogueUnitCase coloring root hroot hdegree) :
    CNF.Clause.eval unitCase.assignment
      (selectorMismatchClause unitCase.code) = false := by
  exact selectorMismatchClause_selected_false _ _

theorem other_guard_true
    {coloring : Nat → Bool} {root : Nat} {hroot : root < 25}
    {hdegree : (colorNeighbors coloring root false).length = 12}
    (unitCase : EncodedCatalogueUnitCase coloring root hroot hdegree)
    {other : Nat} (hother : other < selectorCodeCount)
    (hne : unitCase.code ≠ other) :
    CNF.Clause.eval unitCase.assignment
      (selectorMismatchClause other) = true := by
  apply selectorMismatchClause_other_true _
  · change unitCase.code < 16
    have hvalid : unitCase.code < 12 := by
      simpa [catalogueCodeCount] using unitCase.valid
    omega
  · exact hother
  · exact hne

theorem invalid_blocker_true
    {coloring : Nat → Bool} {root : Nat} {hroot : root < 25}
    {hdegree : (colorNeighbors coloring root false).length = 12}
    (unitCase : EncodedCatalogueUnitCase coloring root hroot hdegree) :
    CNF.Clause.eval unitCase.assignment invalidSelectorCodeClause = true := by
  exact invalidSelectorCodeClause_valid_true _ unitCase.valid

end EncodedCatalogueUnitCase

/-- Upgrade an already selected semantic catalogue case to the exact encoded
assignment satisfying its 66 global-CNF units. -/
theorem guardedCatalogueCase_encodedUnitCase
    {coloring : Nat → Bool} (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (guardedCase : GuardedCatalogueCase
      (redDegreeTwelveGraph coloring root hdegree)) :
    Nonempty (EncodedCatalogueUnitCase coloring root hroot hdegree) := by
  have hsourceLength :
      (redDegreeTwelveGraph coloring root hdegree).length = 12 := by
    simp [redDegreeTwelveGraph, redNeighborGraph]
  obtain ⟨witness⟩ :=
    graphIsomorphic_catalogueDirectUnitWitness hsourceLength
      guardedCase.isomorphic
  refine ⟨{
    code := guardedCase.code
    valid := guardedCase.valid
    redPermutation := witness.permutation
    units := ?_
  }⟩
  apply witness.allUnitsSatisfied
  intro left right hordered
  exact encodedCatalogueAssignment_redEdge coloring root hroot hdegree
    witness.permutation guardedCase.code left right hordered

/-- End-to-end selector-to-unit bridge for every Ramsey-free exact
red-degree-twelve root. -/
theorem red_degree_twelve_enters_encoded_catalogue_unit_case
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Nonempty (EncodedCatalogueUnitCase coloring root hroot hdegree) := by
  obtain ⟨guardedCase⟩ :=
    red_degree_twelve_enters_guarded_catalogue_case
      hfree root hroot hdegree
  exact guardedCatalogueCase_encodedUnitCase root hroot hdegree guardedCase

#print axioms catalogueDirectUnits_length
#print axioms graphIsomorphic_catalogueDirectUnitWitness
#print axioms CatalogueDirectUnitWitness.allUnitsSatisfied
#print axioms guardedCatalogueCase_encodedUnitCase
#print axioms red_degree_twelve_enters_encoded_catalogue_unit_case
#print axioms EncodedCatalogueUnitCase.selector_bits
#print axioms EncodedCatalogueUnitCase.selected_guard_false
#print axioms EncodedCatalogueUnitCase.other_guard_true
#print axioms EncodedCatalogueUnitCase.invalid_blocker_true

end LRATCatcher.Tests.R45DegreeTwelveCatalogueUnitsBridge
