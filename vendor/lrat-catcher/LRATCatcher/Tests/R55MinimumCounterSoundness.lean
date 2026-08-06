import LRATCatcher.Tests.R55MinLeafSemantics
import Std.Sat.CNF.Relabel

/-!
  Sound witness for the Sinz-style `<= 9` sequential counter used by the
  5,149-clause minimum-internal-degree block of the type-0 leaf.

  A primary variable is the red value of one internal edge.  Consequently a
  false primary is a blue edge, and the counter bounds the number of false
  primaries by nine.  Auxiliary `(i,j)` records that at least `j` of positions
  `0,...,i` are false.
-/

namespace LRATCatcher.Tests.R55.MinLeaf.MinimumCounter

open Std.Sat

abbrev SeqVariable := Sum Nat (Nat × Nat)

def falseCount (values : Nat -> Bool) (stop : Nat) : Nat :=
  (List.range stop).countP fun index => !values index

theorem falseCount_succ (values : Nat -> Bool) (stop : Nat) :
    falseCount values (stop + 1) =
      falseCount values stop + if values stop then 0 else 1 := by
  cases hvalue : values stop <;> simp [falseCount, List.range_succ, hvalue]

theorem falseCount_mono (values : Nat -> Bool) {left right : Nat}
    (hle : left <= right) :
    falseCount values left <= falseCount values right := by
  exact (List.range_sublist.mpr hle).countP_le

def seqAssignment (values : Nat -> Bool) : SeqVariable -> Bool
  | .inl index => values index
  | .inr (index, threshold) =>
      decide (threshold <= falseCount values (index + 1))

def firstClause (index : Nat) : CNF.Clause SeqVariable :=
  [(.inl index, true), (.inr (index, 1), true)]

def propagationClauses (index : Nat) : List (CNF.Clause SeqVariable) :=
  (List.range' 1 (Nat.min 9 index)).map fun threshold =>
    [(.inr (index - 1, threshold), false),
      (.inr (index, threshold), true)]

def incrementClauses (index : Nat) : List (CNF.Clause SeqVariable) :=
  (List.range' 2 (Nat.min 9 (index + 1) - 1)).map fun threshold =>
    [(.inl index, true),
      (.inr (index - 1, threshold - 1), false),
      (.inr (index, threshold), true)]

def overflowClauses (index : Nat) : List (CNF.Clause SeqVariable) :=
  if 9 <= index then
    [[(.inl index, true), (.inr (index - 1, 9), false)]]
  else
    []

def rowClauses (index : Nat) : List (CNF.Clause SeqVariable) :=
  [firstClause index] ++ (propagationClauses index ++
    (incrementClauses index ++ overflowClauses index))

def sequentialAtMostNine (length : Nat) : CNF SeqVariable :=
  { clauses := ((List.range length).flatMap rowClauses).toArray }

theorem firstClause_satisfied (values : Nat -> Bool) (index : Nat) :
    CNF.Clause.eval (seqAssignment values) (firstClause index) = true := by
  by_cases hvalue : values index
  · simp [firstClause, seqAssignment, hvalue]
  · have hcount : 1 <= falseCount values (index + 1) := by
      rw [falseCount_succ]
      simp [hvalue]
    simp [firstClause, seqAssignment, hvalue, hcount]

theorem propagationClause_satisfied (values : Nat -> Bool)
    (index threshold : Nat) (hindex : 1 <= index) :
    CNF.Clause.eval (seqAssignment values)
      [(.inr (index - 1, threshold), false),
        (.inr (index, threshold), true)] = true := by
  have hmono :
      falseCount values ((index - 1) + 1) <=
        falseCount values (index + 1) := by
    apply falseCount_mono
    omega
  by_cases hprevious : threshold <= falseCount values ((index - 1) + 1)
  · have hcurrent : threshold <= falseCount values (index + 1) :=
      Nat.le_trans hprevious hmono
    simp [seqAssignment, hprevious, hcurrent]
  · simp [seqAssignment, hprevious]

theorem incrementClause_satisfied (values : Nat -> Bool)
    (index threshold : Nat) (hindex : 1 <= index) (hthreshold : 2 <= threshold) :
    CNF.Clause.eval (seqAssignment values)
      [(.inl index, true),
        (.inr (index - 1, threshold - 1), false),
        (.inr (index, threshold), true)] = true := by
  cases hvalue : values index with
  | true => simp [seqAssignment, hvalue]
  | false =>
    have hcount : falseCount values (index + 1) =
        falseCount values ((index - 1) + 1) + 1 := by
      rw [falseCount_succ]
      simp [hvalue, show (index - 1) + 1 = index by omega]
    by_cases hprevious :
        threshold - 1 <= falseCount values ((index - 1) + 1)
    · have hcurrent :
          threshold <= falseCount values (index + 1) := by
        rw [hcount]
        omega
      simp [seqAssignment, hvalue, hprevious, hcurrent]
    · simp [seqAssignment, hvalue, hprevious]

theorem overflowClause_satisfied (values : Nat -> Bool)
    (length index : Nat) (hindex : index < length) (hbound : falseCount values length <= 9)
    (hlarge : 9 <= index) :
    CNF.Clause.eval (seqAssignment values)
      [(.inl index, true), (.inr (index - 1, 9), false)] = true := by
  cases hvalue : values index with
  | true => simp [seqAssignment, hvalue]
  | false =>
    have hprefixLe : falseCount values (index + 1) <= falseCount values length := by
      apply falseCount_mono
      omega
    have hcount : falseCount values (index + 1) =
        falseCount values ((index - 1) + 1) + 1 := by
      rw [falseCount_succ]
      simp [hvalue, show (index - 1) + 1 = index by omega]
    have hprefixBound : falseCount values ((index - 1) + 1) + 1 <= 9 := by
      calc
        falseCount values ((index - 1) + 1) + 1 =
            falseCount values (index + 1) := hcount.symm
        _ <= falseCount values length := hprefixLe
        _ <= 9 := hbound
    have hnotPrevious : ¬ (9 <= falseCount values ((index - 1) + 1)) := by
      intro hge
      omega
    simp [seqAssignment, hvalue, hnotPrevious]

theorem rowClause_satisfied (values : Nat -> Bool)
    (length index : Nat) (hindex : index < length)
    (hbound : falseCount values length <= 9)
    (clause : CNF.Clause SeqVariable) (hclause : clause ∈ rowClauses index) :
    CNF.Clause.eval (seqAssignment values) clause = true := by
  unfold rowClauses at hclause
  rcases List.mem_append.mp hclause with hfirst | hrest
  · simp only [List.mem_singleton] at hfirst
    subst clause
    exact firstClause_satisfied values index
  · rcases List.mem_append.mp hrest with hpropagation | hrest
    · obtain ⟨threshold, hthreshold, rfl⟩ := List.mem_map.mp hpropagation
      obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hthreshold
      have hminLe : Nat.min 9 index <= index := Nat.min_le_right 9 index
      have hpositive : 1 <= index := by omega
      exact propagationClause_satisfied values index threshold hpositive
    · rcases List.mem_append.mp hrest with hincrement | hoverflow
      · obtain ⟨threshold, hthreshold, rfl⟩ := List.mem_map.mp hincrement
        obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hthreshold
        have hminLe : Nat.min 9 (index + 1) <= index + 1 :=
          Nat.min_le_right 9 (index + 1)
        have hpositive : 1 <= index := by omega
        have hthresholdTwo : 2 <= threshold := by omega
        exact incrementClause_satisfied values index threshold hpositive hthresholdTwo
      · by_cases hlarge : 9 <= index
        · simp only [overflowClauses, if_pos hlarge, List.mem_singleton] at hoverflow
          subst clause
          exact overflowClause_satisfied values length index hindex hbound hlarge
        · simp [overflowClauses, hlarge] at hoverflow

/-- Canonical witness-extension theorem for a complete `<= 9` sequential
counter: a vector with at most nine false primaries satisfies every generated
clause after assigning each auxiliary to its prefix-count meaning. -/
theorem sequentialAtMostNine_sat (values : Nat -> Bool) (length : Nat)
    (hbound : falseCount values length <= 9) :
    CNF.eval (seqAssignment values) (sequentialAtMostNine length) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro clauseIndex hclauseIndex
  have hmember :
      (sequentialAtMostNine length).clauses[clauseIndex] ∈
        (sequentialAtMostNine length).clauses :=
    Array.getElem_mem hclauseIndex
  simp only [sequentialAtMostNine, List.mem_toArray, List.mem_flatMap] at hmember
  obtain ⟨index, hindex, hclause⟩ := hmember
  exact rowClause_satisfied values length index (List.mem_range.mp hindex)
    hbound _ hclause

#print axioms sequentialAtMostNine_sat

end LRATCatcher.Tests.R55.MinLeaf.MinimumCounter
