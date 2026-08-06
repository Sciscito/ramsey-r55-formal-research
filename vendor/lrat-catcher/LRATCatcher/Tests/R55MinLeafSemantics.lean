import LRATCatcher.Tests.R55MinLeafBridge

/-!
  End-to-end semantic use of the certified type-0 minimum-anchor leaf.

  The exact external formula is decomposed into:

  * the interleaved Ramsey `R(5,5,43)` clauses;
  * the rooted degree-window sequential-counter clauses;
  * the anchored minimum-internal-degree sequential-counter clauses;
  * the canonical root, anchor, and type-0 unit clauses.

  The final theorem deliberately requires satisfaction of both counter CNFs.
  Proving that suitable auxiliary bits exist from the corresponding graph
  inequalities is a separate, still-open encoding-soundness obligation.
-/

namespace LRATCatcher.Tests.R55.MinLeaf

open Std.Sat
open LRATCatcher.Ramsey
open CanonicalUnits
open TypedUnits

def rootedDegreeCNF : CNF Nat :=
  { clauses := rootedDegreeClauses }

def minimumInternalDegreeCNF : CNF Nat :=
  { clauses := minimumInternalDegreeClauses }

def unitsCNF (units : List Int) : CNF Nat :=
  { clauses := unitClauses units }

/-- Python `itertools.combinations` order on an increasing ambient list. -/
def pythonCombinations : List Nat -> Nat -> List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | head :: tail, size + 1 =>
      (pythonCombinations tail size).map (head :: .) ++
        pythonCombinations tail (size + 1)

theorem mem_pythonCombinations_properties {ambient vertices : List Nat} {size : Nat}
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

/-- Exact clause and literal order used by `ramsey.py ramsey_clauses`. -/
def pythonInterleavedRamseyEncode (n k : Nat) : CNF Nat :=
  { clauses := ((pythonCombinations (List.range n) k).flatMap fun vertices =>
      [redClause n vertices, blueClause n vertices]).toArray }

def minD20C10T0Decomposition : CNF Nat :=
  pythonInterleavedRamseyEncode 43 5 ++
    rootedDegreeCNF ++
    minimumInternalDegreeCNF ++
    unitsCNF canonicalRootUnits ++
    unitsCNF canonicalAnchorUnits ++
    unitsCNF (fixedAnchorTypeUnits (orderTenCatalogueType 0))

/-- Every clause of the Python-ordered Ramsey prefix is satisfied by a
Ramsey-free coloring. -/
theorem pythonInterleavedRamseyEncode_sat (assignment : Nat -> Bool)
    (hfree : isRamseyFree 43 5 5 assignment) :
    CNF.eval assignment (pythonInterleavedRamseyEncode 43 5) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hmem :
      (pythonInterleavedRamseyEncode 43 5).clauses[index] ∈
        (pythonInterleavedRamseyEncode 43 5).clauses :=
    Array.getElem_mem hindex
  simp only [pythonInterleavedRamseyEncode, List.mem_toArray,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨vertices, hvertices, hcolor⟩ := hmem
  obtain ⟨hlength', hsublist⟩ := mem_pythonCombinations_properties hvertices
  have hbound' : ∀ vertex ∈ vertices, vertex < 43 := by
    intro vertex hvertex
    exact List.mem_range.mp (hsublist.mem hvertex)
  have hnodup' : vertices.Nodup := hsublist.nodup List.nodup_range
  rcases hcolor with hred | hblue
  · have hnotRed := hfree.1 vertices hlength' hbound' hnodup'
    obtain ⟨edgeIndex, hedgeIndex, hfalse⟩ :=
      exists_false_edge 43 vertices assignment hnotRed
    have hsatisfied : CNF.Clause.eval assignment (redClause 43 vertices) = true := by
      simp only [redClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
      exact ⟨edgeIndex, hedgeIndex, by simp [Function.comp, hfalse]⟩
    simpa [pythonInterleavedRamseyEncode, hred] using hsatisfied
  · have hnotBlue := hfree.2 vertices hlength' hbound' hnodup'
    obtain ⟨edgeIndex, hedgeIndex, htrue⟩ :=
      exists_true_edge 43 vertices assignment hnotBlue
    have hsatisfied : CNF.Clause.eval assignment (blueClause 43 vertices) = true := by
      simp only [blueClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
      exact ⟨edgeIndex, hedgeIndex, by simp [Function.comp, htrue]⟩
    simpa [pythonInterleavedRamseyEncode, hblue] using hsatisfied

theorem unitsCNF_sat_iff (assignment : Nat -> Bool) (units : List Int) :
    CNF.eval assignment (unitsCNF units) = true ↔
      AllUnitsSatisfied assignment units := by
  simp only [CNF.eval, unitsCNF, unitClauses, Array.all_eq_true,
    AllUnitsSatisfied, dimacsUnitSatisfied]
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

/-- The two exact residual counter blocks.  This is intentionally a semantic
hypothesis on a full assignment (edge variables plus auxiliary variables). -/
structure CounterBlocksSatisfied (assignment : Nat -> Bool) : Prop where
  rootedDegree : CNF.eval assignment rootedDegreeCNF = true
  minimumInternalDegree :
    CNF.eval assignment minimumInternalDegreeCNF = true

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A computational equality check in Lean pins down the complete clause
layout, including the exact type-0 catalogue representative and both
auxiliary-variable blocks. -/
theorem minD20C10T0Formula_eq_decomposition :
    minD20C10T0Formula = minD20C10T0Decomposition := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

/-- Sound use of the LRAT leaf: no assignment can simultaneously describe a
Ramsey-free coloring, satisfy the canonical `d=20,c=10,type=0` units, and
satisfy the exact two auxiliary counter blocks from the external CNF. -/
theorem no_t0_assignment
    (assignment : Nat -> Bool)
    (hfree : isRamseyFree 43 5 5 assignment)
    (canonical : CanonicalD20C10Units assignment)
    (type0 : TypeUnitsSatisfied assignment (orderTenCatalogueType 0))
    (counters : CounterBlocksSatisfied assignment) : False := by
  have hsat : CNF.eval assignment minD20C10T0Formula = true := by
    rw [minD20C10T0Formula_eq_decomposition]
    have hramsey := pythonInterleavedRamseyEncode_sat assignment hfree
    have hroot :=
      (unitsCNF_sat_iff assignment canonicalRootUnits).mpr canonical.root
    have hanchor :=
      (unitsCNF_sat_iff assignment canonicalAnchorUnits).mpr canonical.anchor
    have htype := (unitsCNF_sat_iff assignment
      (fixedAnchorTypeUnits (orderTenCatalogueType 0))).mpr type0
    simp [minD20C10T0Decomposition, hramsey, counters.rootedDegree,
      counters.minimumInternalDegree, hroot, hanchor, htype]
  have hfalse := minD20C10T0Formula_unsat assignment
  rw [hsat] at hfalse
  contradiction

#print axioms minD20C10T0Formula_eq_decomposition
#print axioms no_t0_assignment

end LRATCatcher.Tests.R55.MinLeaf
