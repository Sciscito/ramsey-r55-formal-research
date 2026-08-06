import LRATCatcher.Tests.R35CatalogCompleteness

/-!
  Closed semantic upper bound R(3,5) ≤ 14 from the exhaustive catalogue.

  The catalogue uses packed adjacency matrices, while the public Ramsey
  statement uses upper-triangle edge variables.  This file supplies the
  missing total translation and proves that a Ramsey-free coloring would
  yield a valid order-14 catalogue graph.  Completeness and the empty final
  catalogue then give the contradiction.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-- Symmetric loop-free edge relation induced by a Ramsey coloring. -/
def coloringEdge (order : Nat) (coloring : Nat → Bool)
    (left right : Nat) : Bool :=
  if left < right then
    coloring (edgeVar order left right)
  else if right < left then
    coloring (edgeVar order right left)
  else
    false

@[simp] theorem coloringEdge_self (order : Nat) (coloring : Nat → Bool)
    (vertex : Nat) :
    coloringEdge order coloring vertex vertex = false := by
  simp [coloringEdge]

theorem coloringEdge_comm (order : Nat) (coloring : Nat → Bool)
    (left right : Nat) :
    coloringEdge order coloring left right =
      coloringEdge order coloring right left := by
  by_cases hleftRight : left < right
  · have hnotRightLeft : ¬ right < left := by omega
    simp [coloringEdge, hleftRight, hnotRightLeft]
  · by_cases hrightLeft : right < left
    · simp [coloringEdge, hleftRight, hrightLeft]
    · have hequal : left = right := by omega
      subst right
      simp

/-- Little-endian packed row of the graph induced by a coloring. -/
def coloringRowBits (order : Nat) (coloring : Nat → Bool)
    (left : Fin order) : List Bool :=
  List.ofFn fun right : Fin order =>
    coloringEdge order coloring left.val right.val

def coloringRow (order : Nat) (coloring : Nat → Bool)
    (left : Fin order) : Nat :=
  (BitVec.ofBoolListLE (coloringRowBits order coloring left)).toNat

/-- Packed adjacency matrix on all vertices below `order`. -/
def coloringGraph (order : Nat) (coloring : Nat → Bool) : Graph :=
  List.ofFn fun left : Fin order => coloringRow order coloring left

@[simp] theorem coloringRowBits_length (order : Nat)
    (coloring : Nat → Bool) (left : Fin order) :
    (coloringRowBits order coloring left).length = order := by
  simp [coloringRowBits]

@[simp] theorem coloringGraph_length (order : Nat)
    (coloring : Nat → Bool) :
    (coloringGraph order coloring).length = order := by
  simp [coloringGraph]

theorem coloringRow_lt (order : Nat) (coloring : Nat → Bool)
    (left : Fin order) :
    coloringRow order coloring left < 2 ^ order := by
  unfold coloringRow
  simpa using (BitVec.ofBoolListLE
    (coloringRowBits order coloring left)).isLt

theorem coloringGraph_getD (order : Nat) (coloring : Nat → Bool)
    (left : Nat) (hleft : left < order) :
    (coloringGraph order coloring).getD left 0 =
      coloringRow order coloring ⟨left, hleft⟩ := by
  have hindex : left < (coloringGraph order coloring).length := by
    rw [coloringGraph_length]
    exact hleft
  rw [← List.getElem_eq_getD
    (l := coloringGraph order coloring) (i := left)
    (h := hindex) 0]
  change
    (List.ofFn fun left : Fin order =>
      coloringRow order coloring left)[left] = _
  rw [List.getElem_ofFn]

/-- Reading a packed graph bit recovers the symmetric coloring edge. -/
theorem edge_coloringGraph (order : Nat) (coloring : Nat → Bool)
    (left right : Fin order) :
    edge (coloringGraph order coloring) left.val right.val =
      coloringEdge order coloring left.val right.val := by
  rw [edge, coloringGraph_getD order coloring left.val left.isLt]
  unfold coloringRow
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := coloringRowBits order coloring left) (i := right.val)
    (h := by simp) false]
  change
    (List.ofFn fun right : Fin order =>
      coloringEdge order coloring left.val right.val)[right.val] = _
  rw [List.getElem_ofFn]

/-- The packed graph induced by any coloring is a well-formed simple graph. -/
theorem coloringGraph_wellFormed (order : Nat) (coloring : Nat → Bool) :
    wellFormedGraph order (coloringGraph order coloring) = true := by
  simp only [wellFormedGraph, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨coloringGraph_length order coloring, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro left hleft
    have hleftBound : left < order := by simpa using hleft
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rw [coloringGraph_getD order coloring left hleftBound]
      exact coloringRow_lt order coloring ⟨left, hleftBound⟩
    · have hedge := edge_coloringGraph order coloring
          ⟨left, hleftBound⟩ ⟨left, hleftBound⟩
      rw [hedge, coloringEdge_self]
      decide
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hlength, hbound, _⟩ :=
      subsets_valid order 2 vertices hvertices
    match vertices with
    | [left, right] =>
      have hleft : left < order := hbound left (by simp)
      have hright : right < order := hbound right (by simp)
      simp only [beq_iff_eq]
      rw [edge_coloringGraph order coloring ⟨left, hleft⟩ ⟨right, hright⟩,
        edge_coloringGraph order coloring ⟨right, hright⟩ ⟨left, hleft⟩]
      exact coloringEdge_comm order coloring _ _
    | [] => simp at hlength
    | [_] => simp at hlength
    | _ :: _ :: _ :: _ => simp at hlength

/-- A Ramsey-free coloring induces a graph with no triangle and no independent
set of five, in the exact semantic vocabulary of the catalogue. -/
theorem coloringGraph_semanticallyValid (order : Nat)
    (coloring : Nat → Bool)
    (hfree : isRamseyFree order 3 5 coloring) :
    SemanticallyValidGraph order (coloringGraph order coloring) := by
  constructor
  · intro triangle hlength hbound hnodup htriangle
    apply hfree.1 triangle hlength hbound hnodup
    intro left right hleft hright hlt
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    have hred := htriangle left hleft right hright (Nat.ne_of_lt hlt)
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩] at hred
    simpa [coloringEdge, hlt] using hred
  · intro independent hlength hbound hnodup hindependent
    apply hfree.2 independent hlength hbound hnodup
    intro left right hleft hright hlt
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    have hblue := hindependent left hleft right hright (Nat.ne_of_lt hlt)
    change Bool.not (edge (coloringGraph order coloring) left right) = true at hblue
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩] at hblue
    simpa [coloringEdge, hlt] using hblue

theorem coloringGraph_validAt (order : Nat) (coloring : Nat → Bool)
    (hfree : isRamseyFree order 3 5 coloring) :
    GraphValidAt order (coloringGraph order coloring) := by
  have hwellFormed := coloringGraph_wellFormed order coloring
  exact ⟨hwellFormed,
    semantic_validGraph hwellFormed
      (coloringGraph_semanticallyValid order coloring hfree)⟩

/-- Closed, machine-checked upper bound `R(3,5) ≤ 14`. -/
theorem r35_upper_catalogue :
    ¬ hasRamseyFreeColoring 14 3 5 := by
  rintro ⟨coloring, hfree⟩
  apply no_graph_valid_at_fourteen
  exact ⟨coloringGraph 14 coloring,
    coloringGraph_validAt 14 coloring hfree⟩

#print axioms r35_upper_catalogue

end LRATCatcher.Tests.R35
