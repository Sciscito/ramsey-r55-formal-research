import LRATCatcher.Tests.R55MinimumBlockBridge

/-!
  A single assignment extending the 903 edge colors with all 2,565 auxiliary
  values of the minimum-internal-degree block.
-/

namespace LRATCatcher.Tests.R55.MinLeaf.MinimumBlock

open Std.Sat
open MinimumCounter

def auxiliaryPairs : List (Nat × Nat) :=
  (List.range 19).flatMap fun index =>
    (List.range' 1 (Nat.min 9 (index + 1))).map fun threshold =>
      (index, threshold)

def counterValues (coloring : Nat -> Bool) (counter position : Nat) : Bool :=
  coloring (counterRelabel counter (.inl position))

/-- Decode a variable in the contiguous auxiliary block and assign the
prefix-count witness belonging to its counter. Edge and unrelated variables
retain their original value. -/
def minimumExtension (coloring : Nat -> Bool) (varIndex : Nat) : Bool :=
  if 59619 <= varIndex ∧ varIndex < 62184 then
    let relative := varIndex - 59619
    let counter := relative / 135
    let localOffset := relative % 135
    let pair := auxiliaryPairs.getD localOffset (0, 1)
    seqAssignment (counterValues coloring counter) (.inr pair)
  else
    coloring varIndex

set_option maxRecDepth 1000000 in
theorem auxiliaryPairs_length : auxiliaryPairs.length = 135 := by
  decide

set_option maxRecDepth 1000000 in
theorem primary_variables_below_auxiliary :
    ∀ counter : Fin 19, ∀ position : Fin 19,
      counterRelabel counter.val (.inl position.val) < 59619 := by
  native_decide

set_option maxRecDepth 1000000 in
/-- Finite arithmetic audit of the complete auxiliary decoder. -/
theorem auxiliary_decoder_checked :
    ∀ counter : Fin 19, ∀ index : Fin 19, ∀ threshold : Fin 10,
      1 <= threshold.val -> threshold.val <= Nat.min 9 (index.val + 1) ->
      let varIndex := counterAuxVariable counter.val index.val threshold.val
      59619 <= varIndex ∧ varIndex < 62184 ∧
      (varIndex - 59619) / 135 = counter.val ∧
      (varIndex - 59619) % 135 =
        auxiliaryRowOffset index.val + (threshold.val - 1) ∧
      auxiliaryPairs.getD
        (auxiliaryRowOffset index.val + (threshold.val - 1)) (0, 1) =
          (index.val, threshold.val) := by
  native_decide

theorem minimumExtension_primary (coloring : Nat -> Bool)
    (counter position : Nat) (hcounter : counter < 19) (hposition : position < 19) :
    minimumExtension coloring (counterRelabel counter (.inl position)) =
      seqAssignment (counterValues coloring counter) (.inl position) := by
  have hbelow : counterRelabel counter (.inl position) < 59619 := by
    simpa using primary_variables_below_auxiliary
      ⟨counter, hcounter⟩ ⟨position, hposition⟩
  have houtside : ¬ (59619 <= counterRelabel counter (.inl position) ∧
      counterRelabel counter (.inl position) < 62184) := by
    intro hrange
    omega
  change minimumExtension coloring (counterRelabel counter (.inl position)) =
    coloring (counterRelabel counter (.inl position))
  unfold minimumExtension
  rw [if_neg houtside]

theorem minimumExtension_auxiliary (coloring : Nat -> Bool)
    (counter index threshold : Nat)
    (hcounter : counter < 19) (hindex : index < 19)
    (hthresholdLower : 1 <= threshold)
    (hthresholdUpper : threshold <= Nat.min 9 (index + 1)) :
    minimumExtension coloring (counterRelabel counter (.inr (index, threshold))) =
      seqAssignment (counterValues coloring counter) (.inr (index, threshold)) := by
  have hminNine : Nat.min 9 (index + 1) <= 9 := Nat.min_le_left 9 (index + 1)
  have hthresholdTen : threshold < 10 := by omega
  have hdecode := auxiliary_decoder_checked
    ⟨counter, hcounter⟩ ⟨index, hindex⟩ ⟨threshold, hthresholdTen⟩
    hthresholdLower hthresholdUpper
  simp only [counterRelabel]
  dsimp only at hdecode
  rcases hdecode with ⟨hlower, hupper, hcounterDecode, hlocalDecode, hpairDecode⟩
  change minimumExtension coloring (counterAuxVariable counter index threshold) =
    seqAssignment (counterValues coloring counter) (.inr (index, threshold))
  unfold minimumExtension
  rw [if_pos ⟨hlower, hupper⟩]
  dsimp only
  rw [hcounterDecode, hlocalDecode, hpairDecode]

/-- The exact syntactic support of a nineteen-primary sequential counter. -/
def ValidSeqVariable : SeqVariable -> Prop
  | .inl position => position < 19
  | .inr (index, threshold) =>
      index < 19 ∧ 1 <= threshold ∧ threshold <= 9 ∧ threshold <= index + 1

theorem rowClauses_variables_valid (index : Nat) (hindex : index < 19)
    (clause : CNF.Clause SeqVariable) (hclause : clause ∈ rowClauses index)
    (seqVar : SeqVariable) (hvar : CNF.Clause.Mem seqVar clause) :
    ValidSeqVariable seqVar := by
  unfold rowClauses at hclause
  rcases List.mem_append.mp hclause with hfirst | hrest
  · simp only [List.mem_singleton] at hfirst
    subst clause
    simp [firstClause] at hvar
    rcases hvar with rfl | rfl
    · simp [ValidSeqVariable, hindex]
    · simp [ValidSeqVariable, hindex]
  · rcases List.mem_append.mp hrest with hpropagation | hrest
    · obtain ⟨threshold, hthreshold, rfl⟩ := List.mem_map.mp hpropagation
      obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hthreshold
      have hminLeNine : Nat.min 9 index <= 9 := Nat.min_le_left 9 index
      have hminLeIndex : Nat.min 9 index <= index := Nat.min_le_right 9 index
      simp at hvar
      rcases hvar with rfl | rfl
      · simp [ValidSeqVariable]
        omega
      · simp [ValidSeqVariable]
        omega
    · rcases List.mem_append.mp hrest with hincrement | hoverflow
      · obtain ⟨threshold, hthreshold, rfl⟩ := List.mem_map.mp hincrement
        obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hthreshold
        have hminLeNine : Nat.min 9 (index + 1) <= 9 :=
          Nat.min_le_left 9 (index + 1)
        have hminLeIndex : Nat.min 9 (index + 1) <= index + 1 :=
          Nat.min_le_right 9 (index + 1)
        simp at hvar
        rcases hvar with rfl | rfl | rfl
        · simp [ValidSeqVariable, hindex]
        · simp [ValidSeqVariable]
          omega
        · simp [ValidSeqVariable]
          omega
      · by_cases hlarge : 9 <= index
        · simp only [overflowClauses, if_pos hlarge, List.mem_singleton] at hoverflow
          subst clause
          simp at hvar
          rcases hvar with rfl | rfl
          · simp [ValidSeqVariable, hindex]
          · simp [ValidSeqVariable]
            omega
        · simp [overflowClauses, hlarge] at hoverflow

theorem sequentialAtMostNine_nineteen_variables_valid (seqVar : SeqVariable)
    (hvar : CNF.VarMem seqVar (sequentialAtMostNine 19)) :
    ValidSeqVariable seqVar := by
  rcases hvar with ⟨clause, hclause, hvar⟩
  simp only [sequentialAtMostNine, List.mem_toArray, List.mem_flatMap] at hclause
  obtain ⟨index, hindex, hclause⟩ := hclause
  exact rowClauses_variables_valid index (List.mem_range.mp hindex)
    clause hclause seqVar hvar

theorem minimumExtension_agrees_on_valid (coloring : Nat -> Bool)
    (counter : Nat) (hcounter : counter < 19) (seqVar : SeqVariable)
    (hvalid : ValidSeqVariable seqVar) :
    minimumExtension coloring (counterRelabel counter seqVar) =
      seqAssignment (counterValues coloring counter) seqVar := by
  cases seqVar with
  | inl position =>
      exact minimumExtension_primary coloring counter position hcounter hvalid
  | inr pair =>
      rcases pair with ⟨index, threshold⟩
      rcases hvalid with ⟨hindex, hlower, hleNine, hleIndex⟩
      apply minimumExtension_auxiliary coloring counter index threshold
        hcounter hindex hlower
      exact Nat.le_min.mpr ⟨hleNine, hleIndex⟩

/-- One exact relabelled counter is satisfied by the shared extension. -/
theorem relabelledCounter_satisfied (coloring : Nat -> Bool)
    (counter : Nat) (hcounter : counter < 19)
    (hbound : falseCount (counterValues coloring counter) 19 <= 9) :
    CNF.eval (minimumExtension coloring) (relabelledCounter counter) = true := by
  simp only [relabelledCounter, CNF.eval_relabel]
  calc
    CNF.eval (minimumExtension coloring ∘ counterRelabel counter)
        (sequentialAtMostNine 19) =
      CNF.eval (seqAssignment (counterValues coloring counter))
        (sequentialAtMostNine 19) := by
          apply CNF.eval_congr
          intro seqVar hvar
          exact minimumExtension_agrees_on_valid coloring counter hcounter seqVar
            (sequentialAtMostNine_nineteen_variables_valid seqVar hvar)
    _ = true := sequentialAtMostNine_sat
      (counterValues coloring counter) 19 hbound

/-- Semantic form of the nineteen minimum-internal-degree inequalities:
each rooted side vertex has at most nine blue edges inside the side. -/
def MinimumInternalDegreeBounds (coloring : Nat -> Bool) : Prop :=
  ∀ counter, counter < 19 ->
    falseCount (counterValues coloring counter) 19 <= 9

theorem foldl_relabelledCounters_satisfied (coloring : Nat -> Bool)
    (hbound : MinimumInternalDegreeBounds coloring)
    (counters : List Nat) (formula : CNF Nat)
    (hformula : CNF.eval (minimumExtension coloring) formula = true)
    (hvalid : ∀ counter ∈ counters, counter < 19) :
    CNF.eval (minimumExtension coloring)
      (counters.foldl (fun current counter =>
        current ++ relabelledCounter counter) formula) = true := by
  induction counters generalizing formula with
  | nil => simpa using hformula
  | cons head tail ih =>
      simp only [List.foldl_cons]
      apply ih (formula := formula ++ relabelledCounter head)
      · have hhead : head < 19 := hvalid head (by simp)
        simp [hformula,
          relabelledCounter_satisfied coloring head hhead (hbound head hhead)]
      · intro counter hcounter
        exact hvalid counter (List.mem_cons_of_mem head hcounter)

theorem generatedMinimumInternalDegreeCNF_satisfied_of_bounds
    (coloring : Nat -> Bool) (hbound : MinimumInternalDegreeBounds coloring) :
    CNF.eval (minimumExtension coloring) generatedMinimumInternalDegreeCNF = true := by
  unfold generatedMinimumInternalDegreeCNF
  apply foldl_relabelledCounters_satisfied coloring hbound
  · simp
  · intro counter hcounter
    exact List.mem_range.mp hcounter

/-- Constructive witness-extension theorem for the exact 5,149-clause block
extracted from the LRAT-certified leaf. -/
theorem minimumInternalDegreeCNF_satisfied_of_bounds
    (coloring : Nat -> Bool) (hbound : MinimumInternalDegreeBounds coloring) :
    CNF.eval (minimumExtension coloring) minimumInternalDegreeCNF = true := by
  rw [← generatedMinimumInternalDegreeCNF_eq_external]
  exact generatedMinimumInternalDegreeCNF_satisfied_of_bounds coloring hbound

theorem minimumExtension_below_auxiliary (coloring : Nat -> Bool)
    (varIndex : Nat) (hbelow : varIndex < 59619) :
    minimumExtension coloring varIndex = coloring varIndex := by
  unfold minimumExtension
  rw [if_neg]
  omega

#print axioms minimumInternalDegreeCNF_satisfied_of_bounds

end LRATCatcher.Tests.R55.MinLeaf.MinimumBlock
