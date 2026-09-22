import LRATCatcher.Tests.R45DegreeEightPilot
import LRATCatcher.Tests.R45DegreeEightGen4416Bridge

/-!
  # Exact semantics of the first certified degree-eight leaf

  This module reconstructs the complete `d8_l22_r01` DIMACS formula in Lean:

  * the `R(4,5)` clauses on the 24 non-root vertices;
  * the no-red-triangle clauses on the first eight vertices;
  * the no-blue-`K4` clauses on the last sixteen vertices;
  * the direct-orientation units from `gen358` parent 22 and `gen4416`
    target 1.

  The computational equality below is the exact bridge from the replayed
  LRAT theorem to these reusable mathematical components.
-/

namespace LRATCatcher.Tests.R45DegreeEightPilotSemantics

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-! ## Python-compatible clause order -/

/-- Exact `itertools.combinations` order on an increasing ambient list. -/
def pythonCombinations : List Nat -> Nat -> List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | head :: tail, size + 1 =>
      (pythonCombinations tail size).map (head :: .) ++
        pythonCombinations tail (size + 1)

theorem mem_pythonCombinations_properties
    {ambient vertices : List Nat} {size : Nat}
    (hmem : vertices ∈ pythonCombinations ambient size) :
    vertices.length = size ∧ vertices.Sublist ambient := by
  induction ambient generalizing size vertices with
  | nil =>
      cases size with
      | zero =>
          simp only [pythonCombinations, List.mem_singleton] at hmem
          subst vertices
          exact ⟨rfl, .slnil⟩
      | succ size => simp [pythonCombinations] at hmem
  | cons head tail ih =>
      cases size with
      | zero =>
          simp only [pythonCombinations, List.mem_singleton] at hmem
          subst vertices
          exact ⟨rfl, List.nil_sublist _⟩
      | succ size =>
          simp only [pythonCombinations, List.mem_append, List.mem_map] at hmem
          rcases hmem with ⟨rest, hrest, rfl⟩ | hwithout
          · obtain ⟨hlength, hsublist⟩ := ih hrest
            exact ⟨by simp [hlength], hsublist.cons_cons head⟩
          · obtain ⟨hlength, hsublist⟩ := ih hwithout
            exact ⟨hlength, hsublist.cons head⟩

/-- Red clauses first, then blue clauses, as emitted by `run_direct_pilot.py`. -/
def pythonRamseyEncode (n redSize blueSize : Nat) : CNF Nat :=
  { clauses :=
      (((pythonCombinations (List.range n) redSize).map (redClause n)) ++
        ((pythonCombinations (List.range n) blueSize).map
          (blueClause n))).toArray }

theorem pythonRamseyEncode_sat (assignment : Nat → Bool)
    (hfree : isRamseyFree 24 4 5 assignment) :
    CNF.eval assignment (pythonRamseyEncode 24 4 5) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hmem :
      (pythonRamseyEncode 24 4 5).clauses[index] ∈
        (pythonRamseyEncode 24 4 5).clauses :=
    Array.getElem_mem hindex
  simp only [pythonRamseyEncode, List.mem_toArray, List.mem_append,
    List.mem_map] at hmem
  rcases hmem with ⟨vertices, hvertices, hequal⟩ |
      ⟨vertices, hvertices, hequal⟩
  · obtain ⟨hlength, hsublist⟩ :=
      mem_pythonCombinations_properties hvertices
    simp only [pythonRamseyEncode]
    rw [← hequal]
    have hbound : ∀ vertex ∈ vertices, vertex < 24 := by
      intro vertex hvertex
      exact List.mem_range.mp (hsublist.mem hvertex)
    have hnodup : vertices.Nodup :=
      hsublist.nodup List.nodup_range
    obtain ⟨edgeIndex, hedgeIndex, hfalse⟩ :=
      exists_false_edge 24 vertices assignment
        (hfree.1 vertices hlength hbound hnodup)
    simp only [redClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨edgeIndex, hedgeIndex, by simp [Function.comp, hfalse]⟩
  · obtain ⟨hlength, hsublist⟩ :=
      mem_pythonCombinations_properties hvertices
    simp only [pythonRamseyEncode]
    rw [← hequal]
    have hbound : ∀ vertex ∈ vertices, vertex < 24 := by
      intro vertex hvertex
      exact List.mem_range.mp (hsublist.mem hvertex)
    have hnodup : vertices.Nodup :=
      hsublist.nodup List.nodup_range
    obtain ⟨edgeIndex, hedgeIndex, htrue⟩ :=
      exists_true_edge 24 vertices assignment
        (hfree.2 vertices hlength hbound hnodup)
    simp only [blueClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨edgeIndex, hedgeIndex, by simp [Function.comp, htrue]⟩

/-- The root is red-adjacent to local vertices `0,...,7`, so this block may
not contain a red triangle. -/
def leftNoRedTriangleCNF : CNF Nat :=
  { clauses :=
      ((pythonCombinations (List.range 8) 3).map (redClause 24)).toArray }

/-- The root is blue-adjacent to local vertices `8,...,23`, so this block may
not contain a blue `K4`. -/
def rightNoBlueFourCNF : CNF Nat :=
  { clauses :=
      ((pythonCombinations (List.range' 8 16) 4).map
        (blueClause 24)).toArray }

/-- No three vertices among reduced labels `0,...,7` form a red triangle. -/
def NoRedTriangleLeft (assignment : Nat → Bool) : Prop :=
  ∀ vertices : List Nat,
    vertices.length = 3 →
    (∀ vertex ∈ vertices, vertex < 8) →
    vertices.Nodup →
    ¬(∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      assignment (edgeVar 24 left right) = true)

/-- No four vertices among reduced labels `8,...,23` form a blue `K4`. -/
def NoBlueFourRight (assignment : Nat → Bool) : Prop :=
  ∀ vertices : List Nat,
    vertices.length = 4 →
    (∀ vertex ∈ vertices, 8 ≤ vertex ∧ vertex < 24) →
    vertices.Nodup →
    ¬(∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      assignment (edgeVar 24 left right) = false)

theorem leftNoRedTriangleCNF_sat (assignment : Nat → Bool)
    (hleft : NoRedTriangleLeft assignment) :
    CNF.eval assignment leftNoRedTriangleCNF = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hmem :
      leftNoRedTriangleCNF.clauses[index] ∈
        leftNoRedTriangleCNF.clauses :=
    Array.getElem_mem hindex
  simp only [leftNoRedTriangleCNF, List.mem_toArray, List.mem_map] at hmem
  obtain ⟨vertices, hvertices, hequal⟩ := hmem
  simp only [leftNoRedTriangleCNF]
  rw [← hequal]
  obtain ⟨hlength, hsublist⟩ :=
    mem_pythonCombinations_properties hvertices
  have hbound : ∀ vertex ∈ vertices, vertex < 8 := by
    intro vertex hvertex
    exact List.mem_range.mp (hsublist.mem hvertex)
  have hnodup : vertices.Nodup :=
    hsublist.nodup List.nodup_range
  obtain ⟨edgeIndex, hedgeIndex, hfalse⟩ :=
    exists_false_edge 24 vertices assignment
      (hleft vertices hlength hbound hnodup)
  simp only [redClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨edgeIndex, hedgeIndex, by simp [Function.comp, hfalse]⟩

theorem rightNoBlueFourCNF_sat (assignment : Nat → Bool)
    (hright : NoBlueFourRight assignment) :
    CNF.eval assignment rightNoBlueFourCNF = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hmem :
      rightNoBlueFourCNF.clauses[index] ∈
        rightNoBlueFourCNF.clauses :=
    Array.getElem_mem hindex
  simp only [rightNoBlueFourCNF, List.mem_toArray, List.mem_map] at hmem
  obtain ⟨vertices, hvertices, hequal⟩ := hmem
  simp only [rightNoBlueFourCNF]
  rw [← hequal]
  obtain ⟨hlength, hsublist⟩ :=
    mem_pythonCombinations_properties hvertices
  have hbound :
      ∀ vertex ∈ vertices, 8 ≤ vertex ∧ vertex < 24 := by
    intro vertex hvertex
    obtain ⟨offset, hoffset, hequal⟩ :=
      List.mem_range'.mp (hsublist.mem hvertex)
    omega
  have hnodup : vertices.Nodup :=
    hsublist.nodup (List.nodup_range' (s := 8) (n := 16))
  obtain ⟨edgeIndex, hedgeIndex, htrue⟩ :=
    exists_true_edge 24 vertices assignment
      (hright vertices hlength hbound hnodup)
  simp only [blueClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨edgeIndex, hedgeIndex, by simp [Function.comp, htrue]⟩

/-! ## Direct-orientation parent units -/

/-- One-based DIMACS literal for an edge whose required Boolean value is
`value`. -/
def edgeUnit (left right : Nat) (value : Bool) : Int :=
  if value then
    Int.ofNat (edgeVar 24 left right + 1)
  else
    -Int.ofNat (edgeVar 24 left right + 1)
/-- Parsing a direct edge unit recovers its zero-based variable and polarity. -/
theorem dimacsLit_edgeUnit (left right : Nat) (value : Bool) :
    LRATCatcher.dimacsLit (edgeUnit left right value) =
      (edgeVar 24 left right, value) := by
  cases value with
  | false =>
      unfold edgeUnit LRATCatcher.dimacsLit
      change
        (edgeVar 24 left right + 1 - 1,
          decide (0 < -Int.ofNat (edgeVar 24 left right + 1))) =
          (edgeVar 24 left right, false)
      have hpositive :
          (0 : Int) < Int.ofNat (edgeVar 24 left right + 1) :=
        Int.natCast_pos.mpr (by omega)
      have hnotPositive :
          ¬(0 : Int) < -Int.ofNat (edgeVar 24 left right + 1) := by
        omega
      have hnonnegative :
          (0 : Int) ≤ Int.ofNat (edgeVar 24 left right) :=
        Int.natCast_nonneg _
      simp
      omega
  | true =>
      unfold edgeUnit LRATCatcher.dimacsLit
      change
        (edgeVar 24 left right + 1 - 1,
          decide (0 < Int.ofNat (edgeVar 24 left right + 1))) =
          (edgeVar 24 left right, true)
      simp

/-- A direct edge unit has exactly the Boolean semantics used by the reduced
`K_24` assignment.  This packages both the one-based DIMACS shift and literal
polarity for the catalogue-to-certificate bridges. -/
@[simp] theorem edgeUnit_satisfied_iff (assignment : Nat → Bool)
    (left right : Nat) (value : Bool) :
    CNF.Clause.eval assignment [LRATCatcher.dimacsLit
      (edgeUnit left right value)] = true ↔
      assignment (edgeVar 24 left right) = value := by
  rw [dimacsLit_edgeUnit]
  cases value <;> simp [CNF.Clause.eval]

/-- Row-major upper-triangle pairs, in Python combination order. -/
def upperPairs (order : Nat) : List (Nat × Nat) :=
  (pythonCombinations (List.range order) 2).filterMap fun vertices =>
    match vertices with
    | [left, right] => some (left, right)
    | _ => none

/-- Fixed units of one partially colored `gen358` parent. HOL color 1 is
direct Lean `true`; HOL color 2 is direct Lean `false`; holes emit no unit. -/
def gen358DirectUnits (parentIndex : Nat) : List Int :=
  let encoded := gen358ParentIds.getD parentIndex 0
  (upperPairs 8).filterMap fun pair =>
    match ternaryColourAt encoded pair.1 pair.2 with
    | 0 => none
    | 1 => some (edgeUnit pair.1 pair.2 true)
    | 2 => some (edgeUnit pair.1 pair.2 false)
    | _ => none

/-- All 120 units of one complete `gen4416` target, shifted to vertices
`8,...,23` of the reduced `K24`. -/
def gen4416DirectUnits (targetIndex : Nat) : List Int :=
  let encoded := gen4416GraphIds.getD targetIndex 0
  (upperPairs 16).map fun pair =>
    edgeUnit (pair.1 + 8) (pair.2 + 8)
      (ternaryColoring encoded (edgeVar 16 pair.1 pair.2))

/-- The exact parent cube used by the certified `d8_l22_r01` leaf. -/
def l22r01Units : List Int :=
  gen358DirectUnits 22 ++ gen4416DirectUnits 1

def unitsCNF (units : List Int) : CNF Nat :=
  { clauses :=
      (units.map fun literal => [LRATCatcher.dimacsLit literal]).toArray }

/-- Semantic satisfaction of every one-literal DIMACS clause in `units`. -/
def AllUnitsSatisfied (assignment : Nat → Bool) (units : List Int) : Prop :=
  ∀ literal, literal ∈ units →
    CNF.Clause.eval assignment [LRATCatcher.dimacsLit literal] = true

theorem unitsCNF_sat_iff (assignment : Nat → Bool) (units : List Int) :
    CNF.eval assignment (unitsCNF units) = true ↔
      AllUnitsSatisfied assignment units := by
  simp only [CNF.eval, unitsCNF, Array.all_eq_true, AllUnitsSatisfied]
  constructor
  · intro hall literal hliteral
    obtain ⟨index, hindex, hequal⟩ := List.getElem_of_mem hliteral
    have hsatisfied := hall index (by simpa using hindex)
    simp only [List.getElem_toArray, List.getElem_map] at hsatisfied
    rw [hequal] at hsatisfied
    exact hsatisfied
  · intro hall index hindex
    have hmem := Array.getElem_mem hindex
    simp only [List.mem_toArray, List.mem_map] at hmem
    obtain ⟨literal, hliteral, hequal⟩ := hmem
    rw [← hequal]
    exact hall literal hliteral

/-- Complete mathematical reconstruction of the certified leaf. -/
def l22r01Decomposition : CNF Nat :=
  pythonRamseyEncode 24 4 5 ++
    leftNoRedTriangleCNF ++
    rightNoBlueFourCNF ++
    unitsCNF l22r01Units

theorem l22r01Units_length : l22r01Units.length = 148 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Every clause and literal of the LRAT-certified file agrees with the Lean
reconstruction, including parent indices, block offsets, polarity, and order. -/
theorem r45D8L22R01Formula_eq_decomposition :
    LRATCatcher.Tests.r45D8L22R01Formula = l22r01Decomposition := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

/-- Semantic use of the certified leaf.  Any reduced assignment satisfying
`R(4,5)` freeness, the two root-induced local exclusions, and the exact
`l22/r01` parent units would satisfy the LRAT-refuted CNF. -/
theorem no_l22r01_reduced_assignment
    (assignment : Nat → Bool)
    (hfree : isRamseyFree 24 4 5 assignment)
    (hleft : NoRedTriangleLeft assignment)
    (hright : NoBlueFourRight assignment)
    (hunits : AllUnitsSatisfied assignment l22r01Units) : False := by
  have hsat :
      CNF.eval assignment LRATCatcher.Tests.r45D8L22R01Formula = true := by
    rw [r45D8L22R01Formula_eq_decomposition]
    have hramsey := pythonRamseyEncode_sat assignment hfree
    have hleftSat := leftNoRedTriangleCNF_sat assignment hleft
    have hrightSat := rightNoBlueFourCNF_sat assignment hright
    have hunitsSat :=
      (unitsCNF_sat_iff assignment l22r01Units).mpr hunits
    simp [l22r01Decomposition, hramsey, hleftSat, hrightSat, hunitsSat]
  have hfalse := LRATCatcher.Tests.r45D8L22R01Formula_unsat assignment
  rw [hsat] at hfalse
  contradiction

#print axioms r45D8L22R01Formula_eq_decomposition
#print axioms no_l22r01_reduced_assignment

end LRATCatcher.Tests.R45DegreeEightPilotSemantics
