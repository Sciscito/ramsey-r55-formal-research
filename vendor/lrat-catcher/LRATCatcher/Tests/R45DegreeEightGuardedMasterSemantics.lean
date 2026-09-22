import LRATCatcher.Tests.R45DegreeEightBranchComposition
import LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-!
  # Semantics of the guarded degree-eight master formula

  The master formula shares catalogue units instead of duplicating them over
  all 54 pairs:

  * the structural order-24 base has 55,006 clauses;
  * five little-endian selector bits at variables 276,...,280 choose one of
    the 27 `gen358` parents;
  * variable 281 chooses one of the two `gen4416` targets;
  * every left unit is guarded only by its five-bit parent code;
  * every right unit is guarded only by its one-bit target code;
  * five clauses forbid unused left codes 27,...,31.

  This file contains no external certificate and asserts no parsed-CNF
  equality.  It proves the semantic bridge needed later: an LRAT refutation
  of this Lean decomposition implies all 54 pair-contradiction interfaces.
-/

namespace LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R45DegreeEightPilotSemantics
open LRATCatcher.Tests.R45DegreeEightBranchComposition
open LRATCatcher.Tests.R45DegreeEightReducedAssignment
open LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge
open LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-! ## Exact clause decomposition -/

abbrev leftSelectorStart : Nat := 276
abbrev leftSelectorWidth : Nat := 5
abbrev rightSelectorVariable : Nat := 281

private theorem leftSelectorCodeCardinality :
    2 ^ leftSelectorWidth = 32 := by
  native_decide

/-- Structural clauses common to every degree-eight leaf. -/
def guardedMasterBaseCNF : CNF Nat :=
  pythonRamseyEncode 24 4 5 ++
    leftNoRedTriangleCNF ++
    rightNoBlueFourCNF

/-- A clause literal which is true precisely when selector `bit` differs
from the corresponding little-endian bit of `code`. -/
def leftSelectorMismatchLiteral (code bit : Nat) : Nat × Bool :=
  (leftSelectorStart + bit, !(code.testBit bit))

/-- Negation of the complete five-bit equality test for `code`. -/
def leftSelectorMismatchClause (code : Nat) : CNF.Clause Nat :=
  (List.range leftSelectorWidth).map
    (leftSelectorMismatchLiteral code)

/-- Negation of the one-bit equality test for the right target code. -/
def rightSelectorMismatchClause (code : Nat) : CNF.Clause Nat :=
  [(rightSelectorVariable, !(code.testBit 0))]

/-- Implication from a selector equality to one direct catalogue unit. -/
def guardedUnitClause (guard : CNF.Clause Nat)
    (literal : Int) : CNF.Clause Nat :=
  guard ++ [LRATCatcher.dimacsLit literal]

/-- The 27 shared left blocks, in parent-index then unit-list order. -/
def leftGuardedUnitClauses : List (CNF.Clause Nat) :=
  (List.range 27).flatMap fun parentIndex =>
    (gen358DirectUnits parentIndex).map fun literal =>
      guardedUnitClause
        (leftSelectorMismatchClause parentIndex) literal

/-- The two shared right blocks, in target-index then unit-list order. -/
def rightGuardedUnitClauses : List (CNF.Clause Nat) :=
  (List.range 2).flatMap fun targetIndex =>
    (gen4416DirectUnits targetIndex).map fun literal =>
      guardedUnitClause
        (rightSelectorMismatchClause targetIndex) literal

/-- Clauses forbidding unused five-bit parent codes 27,...,31. -/
def invalidParentCodeClauses : List (CNF.Clause Nat) :=
  (List.range' 27 5).map leftSelectorMismatchClause

def leftGuardedUnitsCNF : CNF Nat :=
  { clauses := leftGuardedUnitClauses.toArray }

def rightGuardedUnitsCNF : CNF Nat :=
  { clauses := rightGuardedUnitClauses.toArray }

def invalidParentCodesCNF : CNF Nat :=
  { clauses := invalidParentCodeClauses.toArray }

/-- Exact Lean-side decomposition to be matched by a later generated DIMACS
master formula. -/
def guardedMasterDecomposition : CNF Nat :=
  guardedMasterBaseCNF ++
    leftGuardedUnitsCNF ++
    rightGuardedUnitsCNF ++
    invalidParentCodesCNF

/-! ## Selector extension of a reduced assignment -/

/-- Preserve all ordinary variables while writing the two little-endian
catalogue codes into variables 276,...,281. -/
def extendWithDegreeEightCodes (assignment : Nat -> Bool)
    (parentIndex targetIndex varIndex : Nat) : Bool :=
  if varIndex < leftSelectorStart then
    assignment varIndex
  else if varIndex < leftSelectorStart + leftSelectorWidth then
    parentIndex.testBit (varIndex - leftSelectorStart)
  else if varIndex = rightSelectorVariable then
    targetIndex.testBit 0
  else
    assignment varIndex

@[simp] theorem extendWithDegreeEightCodes_of_lt
    (assignment : Nat -> Bool) (parentIndex targetIndex varIndex : Nat)
    (hvarIndex : varIndex < leftSelectorStart) :
    extendWithDegreeEightCodes assignment parentIndex targetIndex varIndex =
      assignment varIndex := by
  simp [extendWithDegreeEightCodes, hvarIndex]

@[simp] theorem extendWithDegreeEightCodes_leftBit
    (assignment : Nat → Bool) (parentIndex targetIndex bit : Nat)
    (hbit : bit < leftSelectorWidth) :
    extendWithDegreeEightCodes assignment parentIndex targetIndex
        (leftSelectorStart + bit) =
      parentIndex.testBit bit := by
  have hnotBefore :
      ¬ leftSelectorStart + bit < leftSelectorStart := by omega
  have hinSelector :
      leftSelectorStart + bit <
        leftSelectorStart + leftSelectorWidth := by omega
  unfold extendWithDegreeEightCodes
  rw [if_neg hnotBefore, if_pos hinSelector]
  simp

@[simp] theorem extendWithDegreeEightCodes_rightBit
    (assignment : Nat → Bool) (parentIndex targetIndex : Nat) :
    extendWithDegreeEightCodes assignment parentIndex targetIndex
        rightSelectorVariable =
      targetIndex.testBit 0 := by
  simp [extendWithDegreeEightCodes, leftSelectorStart,
    leftSelectorWidth, rightSelectorVariable]

/-- Every genuine order-24 edge variable lies below the selector block. -/
theorem edgeVar_twentyFour_lt_leftSelectorStart
    (left right : Fin 24) (hordered : left < right) :
    edgeVar 24 left.val right.val < leftSelectorStart := by
  native_decide +revert

@[simp] theorem extendWithDegreeEightCodes_edgeVar
    (assignment : Nat → Bool) (parentIndex targetIndex left right : Nat)
    (hleft : left < 24) (hright : right < 24)
    (hordered : left < right) :
    extendWithDegreeEightCodes assignment parentIndex targetIndex
        (edgeVar 24 left right) =
      assignment (edgeVar 24 left right) := by
  apply extendWithDegreeEightCodes_of_lt
  simpa using edgeVar_twentyFour_lt_leftSelectorStart
    ⟨left, hleft⟩ ⟨right, hright⟩ hordered

/-! ## Structural semantics survive the selector extension -/

theorem ReducedAssignmentSemantics_extendWithDegreeEightCodes
    {assignment : Nat → Bool}
    (semantics : ReducedAssignmentSemantics assignment)
    (parentIndex targetIndex : Nat) :
    ReducedAssignmentSemantics
      (extendWithDegreeEightCodes assignment parentIndex targetIndex) where
  ramseyFree := by
    constructor
    · intro vertices hlength hbound hnodup hall
      apply semantics.ramseyFree.1 vertices hlength hbound hnodup
      intro left right hleft hright hordered
      have hedge := hall left right hleft hright hordered
      rw [extendWithDegreeEightCodes_edgeVar assignment parentIndex
        targetIndex left right (hbound left hleft) (hbound right hright)
        hordered] at hedge
      exact hedge
    · intro vertices hlength hbound hnodup hall
      apply semantics.ramseyFree.2 vertices hlength hbound hnodup
      intro left right hleft hright hordered
      have hedge := hall left right hleft hright hordered
      rw [extendWithDegreeEightCodes_edgeVar assignment parentIndex
        targetIndex left right (hbound left hleft) (hbound right hright)
        hordered] at hedge
      exact hedge
  noRedTriangleLeft := by
    intro vertices hlength hbound hnodup hall
    apply semantics.noRedTriangleLeft vertices hlength hbound hnodup
    intro left right hleft hright hordered
    have hedge := hall left right hleft hright hordered
    have hleft24 : left < 24 := Nat.lt_trans (hbound left hleft) (by omega)
    have hright24 : right < 24 :=
      Nat.lt_trans (hbound right hright) (by omega)
    rw [extendWithDegreeEightCodes_edgeVar assignment parentIndex
      targetIndex left right hleft24 hright24 hordered] at hedge
    exact hedge
  noBlueFourRight := by
    intro vertices hlength hbound hnodup hall
    apply semantics.noBlueFourRight vertices hlength hbound hnodup
    intro left right hleft hright hordered
    have hedge := hall left right hleft hright hordered
    rw [extendWithDegreeEightCodes_edgeVar assignment parentIndex
      targetIndex left right (hbound left hleft).2
        (hbound right hright).2 hordered] at hedge
    exact hedge

/-! ## Direct units remain satisfied after adding selectors -/

private theorem gen358DirectUnit_variable_lt
    {parentIndex : Nat} {literal : Int}
    (hliteral : literal ∈ gen358DirectUnits parentIndex) :
    (LRATCatcher.dimacsLit literal).1 < leftSelectorStart := by
  simp only [gen358DirectUnits, List.mem_filterMap] at hliteral
  obtain ⟨pair, hpair, hunit⟩ := hliteral
  obtain ⟨horderedNat, hright⟩ := upperPairs_eight_ordered pair hpair
  let left : Fin 24 := ⟨pair.1, by omega⟩
  let right : Fin 24 := ⟨pair.2, by omega⟩
  have hordered : left < right := by
    simpa [left, right] using horderedNat
  let colour := ternaryColourAt
    (gen358ParentIds.getD parentIndex 0) pair.1 pair.2
  have hcolourLt : colour < 3 := by
    dsimp [colour]
    unfold ternaryColourAt
    exact Nat.mod_lt _ (by omega)
  have hcases : colour = 0 ∨ colour = 1 ∨ colour = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hzero' : ternaryColourAt
        (gen358ParentIds.getD parentIndex 0) pair.1 pair.2 = 0 := by
      simpa [colour] using hzero
    rw [hzero'] at hunit
    simp at hunit
  · have hequal : edgeUnit pair.1 pair.2 true = literal := by
      have hone' : ternaryColourAt
          (gen358ParentIds.getD parentIndex 0) pair.1 pair.2 = 1 := by
        simpa [colour] using hone
      rw [hone'] at hunit
      exact Option.some.inj hunit
    rw [← hequal, dimacsLit_edgeUnit]
    exact edgeVar_twentyFour_lt_leftSelectorStart left right hordered
  · have hequal : edgeUnit pair.1 pair.2 false = literal := by
      have htwo' : ternaryColourAt
          (gen358ParentIds.getD parentIndex 0) pair.1 pair.2 = 2 := by
        simpa [colour] using htwo
      rw [htwo'] at hunit
      exact Option.some.inj hunit
    rw [← hequal, dimacsLit_edgeUnit]
    exact edgeVar_twentyFour_lt_leftSelectorStart left right hordered

private theorem gen4416DirectUnit_variable_lt
    {targetIndex : Nat} {literal : Int}
    (hliteral : literal ∈ gen4416DirectUnits targetIndex) :
    (LRATCatcher.dimacsLit literal).1 < leftSelectorStart := by
  simp only [gen4416DirectUnits, List.mem_map] at hliteral
  obtain ⟨pair, hpair, rfl⟩ := hliteral
  obtain ⟨horderedNat, hright⟩ :=
    upperPairs_sixteen_ordered pair hpair
  let left : Fin 24 := ⟨pair.1 + 8, by omega⟩
  let right : Fin 24 := ⟨pair.2 + 8, by omega⟩
  have hordered : left < right := by
    simpa [left, right] using horderedNat
  rw [dimacsLit_edgeUnit]
  exact edgeVar_twentyFour_lt_leftSelectorStart left right hordered

private theorem degreeEightPairUnit_variable_lt
    {parentIndex targetIndex : Nat} {literal : Int}
    (hliteral : literal ∈ degreeEightPairUnits parentIndex targetIndex) :
    (LRATCatcher.dimacsLit literal).1 < leftSelectorStart := by
  rcases List.mem_append.mp hliteral with hleft | hright
  · exact gen358DirectUnit_variable_lt hleft
  · exact gen4416DirectUnit_variable_lt hright

private theorem dimacsUnit_eval_extendWithDegreeEightCodes
    (assignment : Nat → Bool) (parentIndex targetIndex : Nat)
    (literal : Int)
    (hvariable :
      (LRATCatcher.dimacsLit literal).1 < leftSelectorStart) :
    CNF.Clause.eval
        (extendWithDegreeEightCodes assignment parentIndex targetIndex)
        [LRATCatcher.dimacsLit literal] =
      CNF.Clause.eval assignment [LRATCatcher.dimacsLit literal] := by
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  rw [extendWithDegreeEightCodes_of_lt assignment parentIndex targetIndex
    (LRATCatcher.dimacsLit literal).1 hvariable]

private theorem pairUnits_extendWithDegreeEightCodes
    {assignment : Nat → Bool} {parentIndex targetIndex : Nat}
    (hunits : AllUnitsSatisfied assignment
      (degreeEightPairUnits parentIndex targetIndex)) :
    AllUnitsSatisfied
      (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      (degreeEightPairUnits parentIndex targetIndex) := by
  intro literal hliteral
  rw [dimacsUnit_eval_extendWithDegreeEightCodes assignment parentIndex
    targetIndex literal (degreeEightPairUnit_variable_lt hliteral)]
  exact hunits literal hliteral

/-! ## Selector guards -/

private theorem exists_testBit_ne
    {width left right : Nat}
    (hleft : left < 2 ^ width) (hright : right < 2 ^ width)
    (hne : Not (left = right)) :
    Exists fun bit : Fin width =>
      Not (left.testBit bit.val = right.testBit bit.val) := by
  by_cases hwitness :
      Exists fun bit : Fin width =>
        Not (left.testBit bit.val = right.testBit bit.val)
  case pos =>
    exact hwitness
  case neg =>
    exfalso
    apply hne
    apply Nat.eq_of_testBit_eq
    intro bit
    by_cases hbit : bit < width
    case pos =>
      by_cases hbits : left.testBit bit = right.testBit bit
      case pos => exact hbits
      case neg =>
        exact False.elim
          (hwitness (Exists.intro (Fin.mk bit hbit) hbits))
    case neg =>
      have hpow : 2 ^ width <= 2 ^ bit :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      have hleftPow : left < 2 ^ bit :=
        Nat.lt_of_lt_of_le hleft hpow
      have hrightPow : right < 2 ^ bit :=
        Nat.lt_of_lt_of_le hright hpow
      rw [Nat.testBit_lt_two_pow hleftPow,
        Nat.testBit_lt_two_pow hrightPow]

private theorem leftMismatchClause_eval_true_of_ne
    (assignment : Nat → Bool) (parentIndex targetIndex other : Nat)
    (hparent : parentIndex < 2 ^ leftSelectorWidth)
    (hother : other < 2 ^ leftSelectorWidth)
    (hne : parentIndex ≠ other) :
    CNF.Clause.eval
        (extendWithDegreeEightCodes assignment parentIndex targetIndex)
        (leftSelectorMismatchClause other) = true := by
  obtain ⟨bit, hbit⟩ :=
    exists_testBit_ne hparent hother hne
  rw [CNF.Clause.eval, List.any_eq_true]
  refine ⟨leftSelectorMismatchLiteral other bit.val, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨bit.val, List.mem_range.mpr bit.isLt, rfl⟩
  · unfold leftSelectorMismatchLiteral
    change
      (extendWithDegreeEightCodes assignment parentIndex targetIndex
        (leftSelectorStart + bit.val) ==
          !(other.testBit bit.val)) = true
    rw [extendWithDegreeEightCodes_leftBit assignment parentIndex
      targetIndex bit.val bit.isLt]
    cases hselected : parentIndex.testBit bit.val <;>
      cases hguarded : other.testBit bit.val <;>
      simp_all [leftSelectorMismatchLiteral]

private theorem rightMismatchClause_eval_true_of_ne
    (assignment : Nat → Bool) (parentIndex targetIndex other : Nat)
    (htarget : targetIndex < 2) (hother : other < 2)
    (hne : targetIndex ≠ other) :
    CNF.Clause.eval
        (extendWithDegreeEightCodes assignment parentIndex targetIndex)
        (rightSelectorMismatchClause other) = true := by
  have htargetPow : targetIndex < 2 ^ 1 := by simpa using htarget
  have hotherPow : other < 2 ^ 1 := by simpa using hother
  obtain ⟨bit, hbit⟩ :=
    exists_testBit_ne htargetPow hotherPow hne
  have hbitZero : bit.val = 0 := by omega
  have hbitEq : bit = (0 : Fin 1) := by
    apply Fin.ext
    exact hbitZero
  subst bit
  simp only [rightSelectorMismatchClause, CNF.Clause.eval,
    List.any_cons, List.any_nil, Bool.or_false]
  rw [extendWithDegreeEightCodes_rightBit]
  cases hselected : targetIndex.testBit 0 <;>
    cases hguarded : other.testBit 0 <;>
    simp_all

private theorem guardedUnitClause_eval_true
    (assignment : Nat -> Bool) (guard : CNF.Clause Nat) (literal : Int)
    (hsatisfied :
      Or (CNF.Clause.eval assignment guard = true)
        (CNF.Clause.eval assignment
          [LRATCatcher.dimacsLit literal] = true)) :
    CNF.Clause.eval assignment (guardedUnitClause guard literal) = true := by
  simpa only [guardedUnitClause, CNF.Clause.eval,
    List.any_append, Bool.or_eq_true_iff] using hsatisfied

private theorem cnfOfClauseList_eval_true
    (assignment : Nat → Bool) (clauses : List (CNF.Clause Nat))
    (hall : ∀ clause, clause ∈ clauses →
      CNF.Clause.eval assignment clause = true) :
    CNF.eval assignment { clauses := clauses.toArray } = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hindexList : index < clauses.length := by simpa using hindex
  simp only [List.getElem_toArray]
  exact hall clauses[index] (List.getElem_mem hindexList)

/-! ## Satisfaction of all four master components -/

private theorem guardedMasterBaseCNF_sat
    {assignment : Nat → Bool} (parentIndex targetIndex : Nat)
    (semantics : ReducedAssignmentSemantics assignment) :
    CNF.eval (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      guardedMasterBaseCNF = true := by
  have extended := ReducedAssignmentSemantics_extendWithDegreeEightCodes
    semantics parentIndex targetIndex
  have hramsey := pythonRamseyEncode_sat
    (extendWithDegreeEightCodes assignment parentIndex targetIndex)
    extended.ramseyFree
  have hleft := leftNoRedTriangleCNF_sat
    (extendWithDegreeEightCodes assignment parentIndex targetIndex)
    extended.noRedTriangleLeft
  have hright := rightNoBlueFourCNF_sat
    (extendWithDegreeEightCodes assignment parentIndex targetIndex)
    extended.noBlueFourRight
  simp [guardedMasterBaseCNF, hramsey, hleft, hright]

private theorem leftGuardedUnitsCNF_sat
    {assignment : Nat → Bool} (parentIndex targetIndex : Nat)
    (hparent : parentIndex < 27)
    (hunits : AllUnitsSatisfied
      (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      (degreeEightPairUnits parentIndex targetIndex)) :
    CNF.eval (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      leftGuardedUnitsCNF = true := by
  unfold leftGuardedUnitsCNF
  apply cnfOfClauseList_eval_true
  intro clause hclause
  simp only [leftGuardedUnitClauses, List.mem_flatMap,
    List.mem_range, List.mem_map] at hclause
  rcases hclause with ⟨other, hother, literal, hliteral, rfl⟩
  by_cases hequal : other = parentIndex
  · subst other
    apply guardedUnitClause_eval_true
    right
    exact hunits literal (List.mem_append.mpr (Or.inl hliteral))
  · apply guardedUnitClause_eval_true
    left
    apply leftMismatchClause_eval_true_of_ne
    · rw [leftSelectorCodeCardinality]
      omega
    · rw [leftSelectorCodeCardinality]
      omega
    · exact fun h => hequal h.symm

private theorem rightGuardedUnitsCNF_sat
    {assignment : Nat → Bool} (parentIndex targetIndex : Nat)
    (htarget : targetIndex < 2)
    (hunits : AllUnitsSatisfied
      (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      (degreeEightPairUnits parentIndex targetIndex)) :
    CNF.eval (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      rightGuardedUnitsCNF = true := by
  unfold rightGuardedUnitsCNF
  apply cnfOfClauseList_eval_true
  intro clause hclause
  simp only [rightGuardedUnitClauses, List.mem_flatMap,
    List.mem_range, List.mem_map] at hclause
  rcases hclause with ⟨other, hother, literal, hliteral, rfl⟩
  by_cases hequal : other = targetIndex
  · subst other
    apply guardedUnitClause_eval_true
    right
    exact hunits literal (List.mem_append.mpr (Or.inr hliteral))
  · apply guardedUnitClause_eval_true
    left
    apply rightMismatchClause_eval_true_of_ne
    · exact htarget
    · exact hother
    · exact fun h => hequal h.symm

private theorem invalidParentCodesCNF_sat
    (assignment : Nat → Bool) (parentIndex targetIndex : Nat)
    (hparent : parentIndex < 27) :
    CNF.eval (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      invalidParentCodesCNF = true := by
  unfold invalidParentCodesCNF
  apply cnfOfClauseList_eval_true
  intro clause hclause
  simp only [invalidParentCodeClauses, List.mem_map] at hclause
  rcases hclause with ⟨other, hother, rfl⟩
  obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hother
  apply leftMismatchClause_eval_true_of_ne
  · rw [leftSelectorCodeCardinality]
    omega
  · rw [leftSelectorCodeCardinality]
    omega
  · omega

/-- A reduced semantic witness for any admissible pair extends to a satisfying
assignment of the entire guarded master decomposition. -/
theorem guardedMasterDecomposition_sat
    {assignment : Nat → Bool} (parentIndex targetIndex : Nat)
    (hparent : parentIndex < 27) (htarget : targetIndex < 2)
    (semantics : ReducedAssignmentSemantics assignment)
    (hunits : AllUnitsSatisfied assignment
      (degreeEightPairUnits parentIndex targetIndex)) :
    CNF.eval (extendWithDegreeEightCodes assignment parentIndex targetIndex)
      guardedMasterDecomposition = true := by
  have hunitsExtended := pairUnits_extendWithDegreeEightCodes hunits
  have hbase := guardedMasterBaseCNF_sat
    parentIndex targetIndex semantics
  have hleft := leftGuardedUnitsCNF_sat
    parentIndex targetIndex hparent hunitsExtended
  have hright := rightGuardedUnitsCNF_sat
    parentIndex targetIndex htarget hunitsExtended
  have hinvalid := invalidParentCodesCNF_sat
    assignment parentIndex targetIndex hparent
  simp [guardedMasterDecomposition, hbase, hleft, hright, hinvalid]

/-! ## From one master refutation to all 54 pair interfaces -/

/-- One refutation of the guarded master formula supplies every pairwise
contradiction required by the global degree-eight branch composition. -/
theorem guardedMaster_unsat_implies_all_pair_contradictions
    (hunsat : guardedMasterDecomposition.Unsat) :
    AllAdmissibleDegreeEightPairsContradictory := by
  intro parentIndex hparent targetIndex htarget assignment semantics hunits
  have hparent27 : parentIndex < 27 := by
    rw [gen358_parent_count] at hparent
    exact hparent
  have htarget2 : targetIndex < 2 := by
    rw [LRATCatcher.Tests.R44RootedGen4416Cover.gen4416_graph_count]
      at htarget
    exact htarget
  have hsatisfied := guardedMasterDecomposition_sat
    parentIndex targetIndex hparent27 htarget2 semantics hunits
  have hfalse := hunsat
    (extendWithDegreeEightCodes assignment parentIndex targetIndex)
  exact Bool.noConfusion (hsatisfied.symm.trans hfalse)

/-! ## Auditable dimensions -/

set_option maxRecDepth 1000000 in
theorem guardedMasterBase_clause_count :
    guardedMasterBaseCNF.clauses.size = 55006 := by
  native_decide

set_option maxRecDepth 1000000 in
theorem leftGuardedUnit_clause_count :
    leftGuardedUnitsCNF.clauses.size = 675 := by
  native_decide

set_option maxRecDepth 1000000 in
theorem rightGuardedUnit_clause_count :
    rightGuardedUnitsCNF.clauses.size = 240 := by
  native_decide

set_option maxRecDepth 1000000 in
theorem invalidParentCode_clause_count :
    invalidParentCodesCNF.clauses.size = 5 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem guardedMaster_clause_count :
    guardedMasterDecomposition.clauses.size = 55926 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem guardedMaster_numLiterals :
    guardedMasterDecomposition.numLiterals = 282 := by
  native_decide

#print axioms guardedMaster_unsat_implies_all_pair_contradictions

end LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics
