import LRATCatcher.Tests.R45DegreeReduction

/-!
  # Handshaking parity and the `8/10/12` degree reduction for `R(4,5,25)`

  This module proves the fixed-order handshaking lemma without importing a
  graph library.  It lists the 600 vertex-edge incidences of `K_25`, checks
  that this list is a permutation of the 300 edge variables repeated twice,
  and folds both lists with Boolean XOR.  Thus not all 25 red degrees can be
  odd.  Combined with the `7 ≤ d ≤ 13` window, some red degree is 8, 10, or 12.
-/

namespace LRATCatcher.Tests.R45DegreeParity

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R45DegreeReduction

def xorList (values : List Bool) : Bool :=
  values.foldr Bool.xor false

@[simp] theorem xorList_cons (head : Bool) (tail : List Bool) :
    xorList (head :: tail) = (head ^^ xorList tail) := by
  rfl

theorem xorList_append (left right : List Bool) :
    xorList (left ++ right) = (xorList left ^^ xorList right) := by
  induction left with
  | nil => simp [xorList]
  | cons head tail ih =>
      change (head ^^ xorList (tail ++ right)) =
        ((head ^^ xorList tail) ^^ xorList right)
      rw [ih, Bool.xor_assoc]

theorem xor_decide_odd_succ (number : Nat) :
    (true ^^ decide (number % 2 = 1)) =
      decide ((number + 1) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one number with hmod | hmod
  · simp [Nat.add_mod, hmod]
  · simp [Nat.add_mod, hmod]

/-- XOR of predicates records whether an odd number of list elements satisfy
the predicate. -/
theorem xorList_map_eq_odd_filter {α : Type}
    (vertices : List α) (predicate : α → Bool) :
    xorList (vertices.map predicate) =
      decide ((vertices.filter predicate).length % 2 = 1) := by
  induction vertices with
  | nil => simp [xorList]
  | cons head tail ih =>
      cases hp : predicate head
      all_goals simp only [List.map_cons, xorList_cons, List.filter_cons, hp]
      · change (false ^^ xorList (tail.map predicate)) =
          decide ((tail.filter predicate).length % 2 = 1)
        simpa using ih
      · change (true ^^ xorList (tail.map predicate)) =
          decide ((Nat.succ (tail.filter predicate).length) % 2 = 1)
        rw [ih]
        simpa [Nat.succ_eq_add_one] using
          xor_decide_odd_succ (tail.filter predicate).length

/-! ## A checked incidence permutation -/

/-- Canonical edge-variable index of every edge incident to `root`. -/
def incidentEdgeVars (root : Nat) : List Nat :=
  (otherVertices root).map fun vertex =>
    if root < vertex then edgeVar 25 root vertex
    else edgeVar 25 vertex root

/-- All 25 rows of incidence indices: 25 times 24 entries. -/
def allIncidentEdgeVars : List Nat :=
  (List.range 25).flatMap incidentEdgeVars

/-- The 300 upper-triangle variables, each repeated exactly twice. -/
def doubledEdgeVars : List Nat :=
  (List.range 300).flatMap fun edge => [edge, edge]

/-- Executable finite check of the exact handshaking reindexing. -/
theorem allIncidentEdgeVars_perm_doubled :
    allIncidentEdgeVars.Perm doubledEdgeVars := by
  native_decide

theorem incidentEdgeVars_map_coloring
    (coloring : Nat → Bool) (root : Nat) :
    (incidentEdgeVars root).map coloring =
      (otherVertices root).map
        (fun vertex => ramseyEdge 25 coloring root vertex) := by
  rw [incidentEdgeVars, List.map_map]
  apply List.map_congr_left
  intro vertex hvertex
  have hne := (mem_otherVertices root vertex).mp hvertex |>.2
  by_cases hordered : root < vertex
  · simp [Function.comp, ramseyEdge, hordered]
  · have hreverse : vertex < root := by omega
    simp [Function.comp, ramseyEdge, hordered, hreverse]

theorem incident_xor_eq_odd_red_degree
    (coloring : Nat → Bool) (root : Nat) :
    xorList ((incidentEdgeVars root).map coloring) =
      decide ((R45DegreeReduction.colorNeighbors
        coloring root false).length % 2 = 1) := by
  rw [incidentEdgeVars_map_coloring]
  simpa [R45DegreeReduction.colorNeighbors] using
    xorList_map_eq_odd_filter (otherVertices root)
      (fun vertex => ramseyEdge 25 coloring root vertex)

theorem xorList_perm {left right : List Nat}
    (hperm : left.Perm right) (coloring : Nat → Bool) :
    xorList (left.map coloring) = xorList (right.map coloring) := by
  unfold xorList
  apply (hperm.map coloring).foldr_eq'
  intro x _hx y _hy z
  simp [Bool.xor_left_comm]

theorem xorList_pairs_false (edges : List Nat)
    (coloring : Nat → Bool) :
    xorList (((edges.flatMap fun edge => [edge, edge]).map coloring)) =
      false := by
  induction edges with
  | nil => simp [xorList]
  | cons head tail ih =>
      change xorList
        (([head, head] ++ tail.flatMap fun edge => [edge, edge]).map
          coloring) = false
      rw [List.map_append, xorList_append, ih]
      simp [xorList]

theorem xorList_doubledEdgeVars_false (coloring : Nat → Bool) :
    xorList (doubledEdgeVars.map coloring) = false := by
  exact xorList_pairs_false (List.range 300) coloring

/-- Boolean handshaking identity: XOR of all 600 incidence colors is false,
because every one of the 300 edge colors occurs exactly twice. -/
theorem all_incidence_xor_false (coloring : Nat → Bool) :
    xorList (allIncidentEdgeVars.map coloring) = false := by
  rw [xorList_perm allIncidentEdgeVars_perm_doubled coloring]
  exact xorList_doubledEdgeVars_false coloring

theorem xorList_map_flatMap {α : Type} (roots : List α)
    (rows : α → List Nat) (coloring : Nat → Bool) :
    xorList ((roots.flatMap rows).map coloring) =
      xorList (roots.map fun root => xorList ((rows root).map coloring)) := by
  induction roots with
  | nil => simp [xorList]
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.map_append, xorList_append,
        List.map_cons, xorList_cons, ih]

/-! ## Consequences for degrees -/

/-- Handshaking parity for the red graph on the fixed 25 vertices: at least
one vertex has even red degree. -/
theorem exists_even_red_degree (coloring : Nat → Bool) :
    ∃ root, root < 25 ∧
      (R45DegreeReduction.colorNeighbors
        coloring root false).length % 2 = 0 := by
  apply Classical.byContradiction
  intro hnone
  have hodd : ∀ root, root < 25 →
      (R45DegreeReduction.colorNeighbors
        coloring root false).length % 2 = 1 := by
    intro root hroot
    have hnotEven :
        (R45DegreeReduction.colorNeighbors
          coloring root false).length % 2 ≠ 0 := by
      intro heven
      exact hnone ⟨root, hroot, heven⟩
    rcases Nat.mod_two_eq_zero_or_one
      (R45DegreeReduction.colorNeighbors
        coloring root false).length with hzero | hone
    · exact absurd hzero hnotEven
    · exact hone
  have hrows :
      (List.range 25).map
          (fun root => xorList ((incidentEdgeVars root).map coloring)) =
        (List.range 25).map (fun _root => true) := by
    apply List.map_congr_left
    intro root hrootMem
    rw [incident_xor_eq_odd_red_degree]
    simp [hodd root (List.mem_range.mp hrootMem)]
  have hglobalTrue :
      xorList (allIncidentEdgeVars.map coloring) = true := by
    rw [allIncidentEdgeVars,
      xorList_map_flatMap (List.range 25) incidentEdgeVars coloring,
      hrows]
    native_decide
  have hglobalFalse := all_incidence_xor_false coloring
  rw [hglobalFalse] at hglobalTrue
  contradiction

/-- Full degree reduction: parity selects a vertex whose red degree is
exactly 8, 10, or 12. -/
theorem exists_red_degree_eight_ten_or_twelve
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hR35 : ¬ hasRamseyFreeColoring 14 3 5)
    (hR44 : ¬ hasRamseyFreeColoring 18 4 4) :
    ∃ root, root < 25 ∧
      ((R45DegreeReduction.colorNeighbors
          coloring root false).length = 8 ∨
       (R45DegreeReduction.colorNeighbors
          coloring root false).length = 10 ∨
       (R45DegreeReduction.colorNeighbors
          coloring root false).length = 12) := by
  obtain ⟨root, hroot, heven⟩ := exists_even_red_degree coloring
  have hwindow :=
    allRedDegrees_between_seven_and_thirteen hfree hR35 hR44 root hroot
  refine ⟨root, hroot, ?_⟩
  omega

/-- Existential version starting from the semantic counterexample object. -/
theorem counterexample_has_reduced_degree
    (hcounterexample : hasRamseyFreeColoring 25 4 5)
    (hR35 : ¬ hasRamseyFreeColoring 14 3 5)
    (hR44 : ¬ hasRamseyFreeColoring 18 4 4) :
    ∃ coloring root,
      isRamseyFree 25 4 5 coloring ∧ root < 25 ∧
      ((R45DegreeReduction.colorNeighbors
          coloring root false).length = 8 ∨
       (R45DegreeReduction.colorNeighbors
          coloring root false).length = 10 ∨
       (R45DegreeReduction.colorNeighbors
          coloring root false).length = 12) := by
  obtain ⟨coloring, hfree⟩ := hcounterexample
  obtain ⟨root, hroot, hdegree⟩ :=
    exists_red_degree_eight_ten_or_twelve hfree hR35 hR44
  exact ⟨coloring, root, hfree, hroot, hdegree⟩

#print axioms counterexample_has_reduced_degree

end LRATCatcher.Tests.R45DegreeParity
