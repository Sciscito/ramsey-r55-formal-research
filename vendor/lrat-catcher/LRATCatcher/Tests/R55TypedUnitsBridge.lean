import LRATCatcher.Tests.R55CanonicalUnitsBridge
import LRATCatcher.Tests.R55W5Symmetry

/-!
  Semantic bridge for the 45 type-unit clauses emitted by
  `ramsey.py fixed_anchor_type_clauses(43, type_graph)` when the type has
  order ten.

  There are two distinct orders in the Python generator:

  * graph6 is decoded by upper-triangle columns and packed into symmetric
    little-endian adjacency rows;
  * DIMACS units are emitted by `itertools.combinations(range(10), 2)`, hence
    by upper-triangle rows.

  The definitions below model the second order exactly.  The contents of a
  unit are read through the already-verified packed-row `edge` predicate, so
  the theorem is independent of the graph6 textual representation.
-/

namespace LRATCatcher.Tests.R55

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open DegreeTwentyCodegreeTenNeighborhood.ExactLists

namespace TypedUnits

open CanonicalUnits

/-- Pairs visited by Python's `itertools.combinations(range(10), 2)`:
`left` increases first, then `right` increases subject to `left < right`. -/
def typePairs : List (Nat × Nat) :=
  (List.range 10).flatMap fun left =>
    ((List.range 10).filter fun right => left < right).map fun right =>
      (left, right)

theorem mem_typePairs_iff (pair : Nat × Nat) :
    pair ∈ typePairs ↔ pair.1 < 10 ∧ pair.2 < 10 ∧ pair.1 < pair.2 := by
  rcases pair with ⟨left, right⟩
  simp [typePairs]

/-- The literal emitted for one local edge.  Local vertices `0,...,9` are
embedded as global vertices `2,...,11`; DIMACS variables are one-based. -/
def typeUnit (typeGraph : Graph) (pair : Nat × Nat) : Int :=
  if edge typeGraph pair.1 pair.2 then
    positiveEdgeLiteral 43 (pair.1 + 2) (pair.2 + 2)
  else
    negativeEdgeLiteral 43 (pair.1 + 2) (pair.2 + 2)

/-- Exactly the 45 unit literals emitted by
`fixed_anchor_type_clauses(43, type_graph)`. -/
def fixedAnchorTypeUnits (typeGraph : Graph) : List Int :=
  typePairs.map (typeUnit typeGraph)

@[simp] theorem typePairs_length : typePairs.length = 45 := by
  decide

@[simp] theorem fixedAnchorTypeUnits_length (typeGraph : Graph) :
    (fixedAnchorTypeUnits typeGraph).length = 45 := by
  simp [fixedAnchorTypeUnits]

/-- Semantic satisfaction of every generated type unit. -/
def TypeUnitsSatisfied (coloring : Nat → Bool) (typeGraph : Graph) : Prop :=
  AllUnitsSatisfied coloring (fixedAnchorTypeUnits typeGraph)

/-- One type literal says exactly that the corresponding ambient edge has
the Boolean value stored in the packed type graph. -/
theorem typeUnit_satisfied_iff (coloring : Nat → Bool) (typeGraph : Graph)
    (pair : Nat × Nat) (hordered : pair.1 < pair.2) :
    dimacsUnitSatisfied coloring (typeUnit typeGraph pair) ↔
      ramseyEdge 43 coloring (pair.1 + 2) (pair.2 + 2) =
        edge typeGraph pair.1 pair.2 := by
  have hambientOrdered : pair.1 + 2 < pair.2 + 2 := by omega
  cases hedge : edge typeGraph pair.1 pair.2 <;>
    simp [typeUnit, hedge, ramseyEdge, hambientOrdered]

/-- Exact semantic characterization of all 45 Python type units. -/
theorem typeUnitsSatisfied_iff_upperEdges
    (coloring : Nat → Bool) (typeGraph : Graph) :
    TypeUnitsSatisfied coloring typeGraph ↔
      ∀ left right, left < 10 → right < 10 → left < right →
        ramseyEdge 43 coloring (left + 2) (right + 2) =
          edge typeGraph left right := by
  constructor
  · intro hunits left right hleft hright hordered
    have hpair : (left, right) ∈ typePairs :=
      (mem_typePairs_iff (left, right)).mpr ⟨hleft, hright, hordered⟩
    have hunit :
        dimacsUnitSatisfied coloring (typeUnit typeGraph (left, right)) := by
      apply hunits
      exact List.mem_map.mpr ⟨(left, right), hpair, rfl⟩
    exact (typeUnit_satisfied_iff coloring typeGraph (left, right) hordered).mp hunit
  · intro hedges literal hliteral
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hliteral
    have hpairs := (mem_typePairs_iff pair).mp hpair
    exact (typeUnit_satisfied_iff coloring typeGraph pair hpairs.2.2).mpr
      (hedges pair.1 pair.2 hpairs.1 hpairs.2.1 hpairs.2.2)

/-- The packed graph induced by the canonically labelled common neighbours
`2,...,11` forced by the root and anchor units. -/
def canonicalInducedGraph {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) : Graph :=
  inducedGraph canonical.toLocalWitness.toExactLists

/-- The `Fin 10` order used when packing the induced graph agrees with the
global labels `2,...,11` used by `fixed_anchor_type_clauses`. -/
theorem canonicalCommon_eq_add_two {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) (index : Fin 10) :
    common canonical.toLocalWitness.toExactLists index = index.val + 2 := by
  unfold common LocalD20C10Witness.toExactLists CanonicalD20C10Units.toLocalWitness
  simp only [LocalD20C10Witness.ofCanonicalBranch]
  simp [rootAnchorCommonNeighbors_eq_range canonical, Nat.add_comm]

/-- The 45 type units are satisfied iff every upper-triangle edge of the
canonical induced graph equals the corresponding packed edge of the chosen
catalogue representative. -/
theorem typeUnitsSatisfied_iff_canonicalInducedUpperEdges
    {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) (typeGraph : Graph) :
    TypeUnitsSatisfied coloring typeGraph ↔
      ∀ left right : Fin 10, left.val < right.val →
        edge (canonicalInducedGraph canonical) left.val right.val =
          edge typeGraph left.val right.val := by
  rw [typeUnitsSatisfied_iff_upperEdges]
  constructor
  · intro hedges left right hordered
    rw [canonicalInducedGraph, edge_inducedGraph,
      canonicalCommon_eq_add_two, canonicalCommon_eq_add_two]
    exact hedges left.val right.val left.isLt right.isLt hordered
  · intro hedges left right hleft hright hordered
    have hedge := hedges ⟨left, hleft⟩ ⟨right, hright⟩ hordered
    rw [canonicalInducedGraph, edge_inducedGraph,
      canonicalCommon_eq_add_two, canonicalCommon_eq_add_two] at hedge
    exact hedge

/-- For a well-formed order-ten representative, the upper-triangle result is
equivalent to equality of the complete (symmetric, loop-free) edge relations.
This is the representation-independent statement needed by a catalogue
branch. -/
theorem typeUnitsSatisfied_iff_canonicalInducedEdges
    {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) (typeGraph : Graph)
    (htypeWellFormed : wellFormedGraph 10 typeGraph = true) :
    TypeUnitsSatisfied coloring typeGraph ↔
      ∀ left right : Fin 10,
        edge (canonicalInducedGraph canonical) left.val right.val =
          edge typeGraph left.val right.val := by
  have hinducedWellFormed :
      wellFormedGraph 10 (canonicalInducedGraph canonical) = true := by
    exact inducedGraph_wellFormed canonical.toLocalWitness.toExactLists
  constructor
  · intro hunits
    have hupper :=
      (typeUnitsSatisfied_iff_canonicalInducedUpperEdges canonical typeGraph).mp
        hunits
    intro left right
    by_cases hleftRight : left.val < right.val
    · exact hupper left right hleftRight
    · by_cases hrightLeft : right.val < left.val
      · calc
          edge (canonicalInducedGraph canonical) left.val right.val =
              edge (canonicalInducedGraph canonical) right.val left.val :=
            wellFormedGraph_edge_symmetric
              (canonicalInducedGraph canonical) 10 left.val right.val
              hinducedWellFormed left.isLt right.isLt
          _ = edge typeGraph right.val left.val :=
            hupper right left hrightLeft
          _ = edge typeGraph left.val right.val :=
            wellFormedGraph_edge_symmetric
              typeGraph 10 right.val left.val htypeWellFormed
              right.isLt left.isLt
      · have hequal : left = right := Fin.ext (by omega)
        subst right
        rw [wellFormedGraph_noLoop
              (canonicalInducedGraph canonical) 10 left.val
              hinducedWellFormed left.isLt,
            wellFormedGraph_noLoop typeGraph 10 left.val
              htypeWellFormed left.isLt]
  · intro hedges
    apply (typeUnitsSatisfied_iff_canonicalInducedUpperEdges canonical typeGraph).mpr
    intro left right _
    exact hedges left right

/-- Two well-formed packed order-ten graphs are equal as lists of natural
adjacency rows as soon as all their in-range edge bits agree.  Row bounds
from well-formedness discharge every bit at position ten or above. -/
theorem orderTenGraph_eq_of_edges (source target : Graph)
    (hsource : wellFormedGraph 10 source = true)
    (htarget : wellFormedGraph 10 target = true)
    (hedges : ∀ left right : Fin 10,
      edge source left.val right.val = edge target left.val right.val) :
    source = target := by
  have hsourceLength : source.length = 10 :=
    wellFormedGraph_length source 10 hsource
  have htargetLength : target.length = 10 :=
    wellFormedGraph_length target 10 htarget
  apply List.ext_getElem
  · omega
  · intro vertex hsourceVertex htargetVertex
    have hvertex : vertex < 10 := by
      simpa [hsourceLength] using hsourceVertex
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0]
    apply Nat.eq_of_testBit_eq
    intro bit
    by_cases hbit : bit < 10
    · simpa [edge] using hedges ⟨vertex, hvertex⟩ ⟨bit, hbit⟩
    · have hsourceRow : source.getD vertex 0 < 2 ^ 10 :=
        wellFormedGraph_row_bound source 10 vertex hsource hvertex
      have htargetRow : target.getD vertex 0 < 2 ^ 10 :=
        wellFormedGraph_row_bound target 10 vertex htarget hvertex
      have hpower : 2 ^ 10 ≤ 2 ^ bit :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hsourceZero : (source.getD vertex 0).testBit bit = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hsourceRow hpower)
      have htargetZero : (target.getD vertex 0).testBit bit = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le htargetRow hpower)
      exact hsourceZero.trans htargetZero.symm

/-- Strongest form of the bridge: the generated DIMACS type units are
satisfied exactly when the canonically packed induced graph is literally the
chosen packed representative, not merely isomorphic to it. -/
theorem typeUnitsSatisfied_iff_canonicalInducedGraph_eq
    {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) (typeGraph : Graph)
    (htypeWellFormed : wellFormedGraph 10 typeGraph = true) :
    TypeUnitsSatisfied coloring typeGraph ↔
      canonicalInducedGraph canonical = typeGraph := by
  have hinducedWellFormed :
      wellFormedGraph 10 (canonicalInducedGraph canonical) = true :=
    inducedGraph_wellFormed canonical.toLocalWitness.toExactLists
  constructor
  · intro hunits
    apply orderTenGraph_eq_of_edges
      (canonicalInducedGraph canonical) typeGraph
      hinducedWellFormed htypeWellFormed
    exact (typeUnitsSatisfied_iff_canonicalInducedEdges
      canonical typeGraph htypeWellFormed).mp hunits
  · intro hequal
    apply (typeUnitsSatisfied_iff_canonicalInducedEdges
      canonical typeGraph htypeWellFormed).mpr
    intro left right
    rw [hequal]

/-- The packed representative selected by the zero-based order-ten catalogue
index used by the Python manifest. -/
def orderTenCatalogueType (typeIndex : Nat) : Graph :=
  (catalogues.getD 10 []).getD typeIndex []

theorem orderTenCatalogueType_wellFormed (typeIndex : Nat)
    (hindex : typeIndex < (catalogues.getD 10 []).length) :
    wellFormedGraph 10 (orderTenCatalogueType typeIndex) = true := by
  have horder : 10 < catalogues.length := by
    rw [catalogues_length_eq, extensionWitnesses_length_eq_fourteen]
    omega
  have hmember : orderTenCatalogueType typeIndex ∈ catalogues.getD 10 [] := by
    unfold orderTenCatalogueType
    rw [← List.getElem_eq_getD
      (l := catalogues.getD 10 []) (i := typeIndex) (h := hindex) []]
    exact List.getElem_mem hindex
  exact (catalogue_entry_checked 10 horder
    (orderTenCatalogueType typeIndex) hmember).1

/-- Fully typed catalogue-index interface.  Once a manifest index is known
to address the same ordered graph6 record as Lean's generated order-ten
catalogue, these are exactly the SAT units for that branch. -/
theorem catalogueTypeUnitsSatisfied_iff_canonicalInducedEdges
    {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) (typeIndex : Nat)
    (hindex : typeIndex < (catalogues.getD 10 []).length) :
    TypeUnitsSatisfied coloring (orderTenCatalogueType typeIndex) ↔
      ∀ left right : Fin 10,
        edge (canonicalInducedGraph canonical) left.val right.val =
          edge (orderTenCatalogueType typeIndex) left.val right.val := by
  exact typeUnitsSatisfied_iff_canonicalInducedEdges canonical
    (orderTenCatalogueType typeIndex)
    (orderTenCatalogueType_wellFormed typeIndex hindex)

/-- Literal packed-graph equality for a zero-based manifest/catalogue index. -/
theorem catalogueTypeUnitsSatisfied_iff_canonicalInducedGraph_eq
    {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) (typeIndex : Nat)
    (hindex : typeIndex < (catalogues.getD 10 []).length) :
    TypeUnitsSatisfied coloring (orderTenCatalogueType typeIndex) ↔
      canonicalInducedGraph canonical = orderTenCatalogueType typeIndex := by
  exact typeUnitsSatisfied_iff_canonicalInducedGraph_eq canonical
    (orderTenCatalogueType typeIndex)
    (orderTenCatalogueType_wellFormed typeIndex hindex)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The hard manifest branch `type_index = 312` is the same packed graph used
by the independently checked W5 symmetry module. -/
theorem orderTenCatalogueType_312_eq_w5 :
    orderTenCatalogueType 312 = LRATCatcher.Tests.R55W5.w5 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem typeIndex312_bound : 312 < (catalogues.getD 10 []).length := by
  decide

/-- Concrete endpoint for the current hard `d20_c10_t312` branch. -/
theorem type312UnitsSatisfied_iff_canonicalInducedGraph_eq_w5
    {coloring : Nat → Bool}
    (canonical : CanonicalD20C10Units coloring) :
    TypeUnitsSatisfied coloring LRATCatcher.Tests.R55W5.w5 ↔
      canonicalInducedGraph canonical = LRATCatcher.Tests.R55W5.w5 := by
  rw [← orderTenCatalogueType_312_eq_w5]
  exact catalogueTypeUnitsSatisfied_iff_canonicalInducedGraph_eq
    canonical 312 typeIndex312_bound

#print axioms type312UnitsSatisfied_iff_canonicalInducedGraph_eq_w5

end TypedUnits

end LRATCatcher.Tests.R55
