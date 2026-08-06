import LRATCatcher.Tests.R55MinLeafSemantics

/-!
  A polarity- and bound-generic soundness theorem for the Sinz sequential
  counters emitted by `r55/ramsey.py`.

  The literal `(primary, guardPolarity)` is the negation of the constrained
  input literal.  Thus an input is active exactly when the primary value is
  different from `guardPolarity`.  This single formulation covers both red
  counters (`guardPolarity = false`) and blue counters
  (`guardPolarity = true`).
-/

namespace LRATCatcher.Tests.R55.SequentialCounter

open Std.Sat

abbrev SeqVariable := Sum Nat (Nat × Nat)

def activeCount (values : Nat → Bool) (guardPolarity : Bool)
    (stop : Nat) : Nat :=
  (List.range stop).countP fun index => values index != guardPolarity

theorem activeCount_succ (values : Nat → Bool) (guardPolarity : Bool)
    (stop : Nat) :
    activeCount values guardPolarity (stop + 1) =
      activeCount values guardPolarity stop +
        if values stop = guardPolarity then 0 else 1 := by
  cases hp : guardPolarity <;> cases hv : values stop <;>
    simp [activeCount, List.range_succ, hv]

theorem activeCount_mono (values : Nat → Bool) (guardPolarity : Bool)
    {left right : Nat} (hle : left ≤ right) :
    activeCount values guardPolarity left ≤
      activeCount values guardPolarity right := by
  exact (List.range_sublist.mpr hle).countP_le

def seqAssignment (values : Nat → Bool) (guardPolarity : Bool) :
    SeqVariable → Bool
  | .inl index => values index
  | .inr (index, threshold) =>
      decide (threshold ≤ activeCount values guardPolarity (index + 1))

def firstClause (guardPolarity : Bool) (index : Nat) :
    CNF.Clause SeqVariable :=
  [(.inl index, guardPolarity), (.inr (index, 1), true)]

def propagationClauses (bound index : Nat) : List (CNF.Clause SeqVariable) :=
  (List.range' 1 (Nat.min bound index)).map fun threshold =>
    [(.inr (index - 1, threshold), false),
      (.inr (index, threshold), true)]

def incrementClauses (guardPolarity : Bool) (bound index : Nat) :
    List (CNF.Clause SeqVariable) :=
  (List.range' 2 (Nat.min bound (index + 1) - 1)).map fun threshold =>
    [(.inl index, guardPolarity),
      (.inr (index - 1, threshold - 1), false),
      (.inr (index, threshold), true)]

def overflowClauses (guardPolarity : Bool) (bound index : Nat) :
    List (CNF.Clause SeqVariable) :=
  if bound ≤ index then
    [[(.inl index, guardPolarity), (.inr (index - 1, bound), false)]]
  else
    []

def rowClauses (guardPolarity : Bool) (bound index : Nat) :
    List (CNF.Clause SeqVariable) :=
  [firstClause guardPolarity index] ++
    (propagationClauses bound index ++
      (incrementClauses guardPolarity bound index ++
        overflowClauses guardPolarity bound index))

def sequentialAtMost (length bound : Nat) (guardPolarity : Bool) :
    CNF SeqVariable :=
  { clauses := ((List.range length).flatMap
      (rowClauses guardPolarity bound)).toArray }

theorem firstClause_satisfied (values : Nat → Bool)
    (guardPolarity : Bool) (index : Nat) :
    CNF.Clause.eval (seqAssignment values guardPolarity)
      (firstClause guardPolarity index) = true := by
  by_cases hguard : values index = guardPolarity
  · simp [firstClause, seqAssignment, hguard]
  · have hcount : 1 ≤ activeCount values guardPolarity (index + 1) := by
      rw [activeCount_succ]
      simp [hguard]
    simp [firstClause, seqAssignment, hcount]

theorem propagationClause_satisfied (values : Nat → Bool)
    (guardPolarity : Bool) (index threshold : Nat) (hindex : 1 ≤ index) :
    CNF.Clause.eval (seqAssignment values guardPolarity)
      [(.inr (index - 1, threshold), false),
        (.inr (index, threshold), true)] = true := by
  have hmono :
      activeCount values guardPolarity ((index - 1) + 1) ≤
        activeCount values guardPolarity (index + 1) := by
    apply activeCount_mono
    omega
  by_cases hprevious :
      threshold ≤ activeCount values guardPolarity ((index - 1) + 1)
  · have hcurrent :
        threshold ≤ activeCount values guardPolarity (index + 1) :=
      Nat.le_trans hprevious hmono
    simp [seqAssignment, hprevious, hcurrent]
  · simp [seqAssignment, hprevious]

theorem incrementClause_satisfied (values : Nat → Bool)
    (guardPolarity : Bool) (index threshold : Nat) (hindex : 1 ≤ index)
    (hthreshold : 2 ≤ threshold) :
    CNF.Clause.eval (seqAssignment values guardPolarity)
      [(.inl index, guardPolarity),
        (.inr (index - 1, threshold - 1), false),
        (.inr (index, threshold), true)] = true := by
  by_cases hguard : values index = guardPolarity
  · simp [seqAssignment, hguard]
  · have hcount : activeCount values guardPolarity (index + 1) =
        activeCount values guardPolarity ((index - 1) + 1) + 1 := by
      rw [activeCount_succ]
      simp [hguard, show (index - 1) + 1 = index by omega]
    by_cases hprevious :
        threshold - 1 ≤
          activeCount values guardPolarity ((index - 1) + 1)
    · have hcurrent :
          threshold ≤ activeCount values guardPolarity (index + 1) := by
        rw [hcount]
        omega
      simp [seqAssignment, hprevious, hcurrent]
    · simp [seqAssignment, hprevious]

theorem overflowClause_satisfied (values : Nat → Bool)
    (guardPolarity : Bool) (length bound index : Nat)
    (hindex : index < length)
    (hbound : activeCount values guardPolarity length ≤ bound)
    (hboundPositive : 1 ≤ bound) (hlarge : bound ≤ index) :
    CNF.Clause.eval (seqAssignment values guardPolarity)
      [(.inl index, guardPolarity),
        (.inr (index - 1, bound), false)] = true := by
  by_cases hguard : values index = guardPolarity
  · simp [seqAssignment, hguard]
  · have hprefixLe : activeCount values guardPolarity (index + 1) ≤
        activeCount values guardPolarity length := by
      apply activeCount_mono
      omega
    have hcount : activeCount values guardPolarity (index + 1) =
        activeCount values guardPolarity ((index - 1) + 1) + 1 := by
      rw [activeCount_succ]
      simp [hguard, show (index - 1) + 1 = index by omega]
    have hprefixBound :
        activeCount values guardPolarity ((index - 1) + 1) + 1 ≤ bound := by
      calc
        activeCount values guardPolarity ((index - 1) + 1) + 1 =
            activeCount values guardPolarity (index + 1) := hcount.symm
        _ ≤ activeCount values guardPolarity length := hprefixLe
        _ ≤ bound := hbound
    have hnotPrevious :
        ¬ (bound ≤
          activeCount values guardPolarity ((index - 1) + 1)) := by
      intro hge
      omega
    simp [seqAssignment, hnotPrevious]

theorem rowClause_satisfied (values : Nat → Bool)
    (guardPolarity : Bool) (length bound index : Nat)
    (hindex : index < length)
    (hbound : activeCount values guardPolarity length ≤ bound)
    (hboundPositive : 1 ≤ bound)
    (clause : CNF.Clause SeqVariable)
    (hclause : clause ∈ rowClauses guardPolarity bound index) :
    CNF.Clause.eval (seqAssignment values guardPolarity) clause = true := by
  unfold rowClauses at hclause
  rcases List.mem_append.mp hclause with hfirst | hrest
  · simp only [List.mem_singleton] at hfirst
    subst clause
    exact firstClause_satisfied values guardPolarity index
  · rcases List.mem_append.mp hrest with hpropagation | hrest
    · obtain ⟨threshold, hthreshold, rfl⟩ := List.mem_map.mp hpropagation
      obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hthreshold
      have hminLe : Nat.min bound index ≤ index := Nat.min_le_right bound index
      have hpositive : 1 ≤ index := by omega
      exact propagationClause_satisfied values guardPolarity index threshold hpositive
    · rcases List.mem_append.mp hrest with hincrement | hoverflow
      · obtain ⟨threshold, hthreshold, rfl⟩ := List.mem_map.mp hincrement
        obtain ⟨offset, hoffset, hequal⟩ := List.mem_range'.mp hthreshold
        have hminLe : Nat.min bound (index + 1) ≤ index + 1 :=
          Nat.min_le_right bound (index + 1)
        have hpositive : 1 ≤ index := by omega
        have hthresholdTwo : 2 ≤ threshold := by omega
        exact incrementClause_satisfied values guardPolarity index threshold
          hpositive hthresholdTwo
      · by_cases hlarge : bound ≤ index
        · simp only [overflowClauses, if_pos hlarge,
            List.mem_singleton] at hoverflow
          subst clause
          exact overflowClause_satisfied values guardPolarity length bound index
            hindex hbound hboundPositive hlarge
        · simp [overflowClauses, hlarge] at hoverflow

/- Prefix-count witnesses satisfy every clause of any positive-bound Sinz
counter in the exact clause order used by the Python generator. -/
theorem sequentialAtMost_sat (values : Nat → Bool)
    (guardPolarity : Bool) (length bound : Nat)
    (hboundPositive : 1 ≤ bound)
    (hbound : activeCount values guardPolarity length ≤ bound) :
    CNF.eval (seqAssignment values guardPolarity)
      (sequentialAtMost length bound guardPolarity) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro clauseIndex hclauseIndex
  have hmember :
      (sequentialAtMost length bound guardPolarity).clauses[clauseIndex] ∈
        (sequentialAtMost length bound guardPolarity).clauses :=
    Array.getElem_mem hclauseIndex
  simp only [sequentialAtMost, List.mem_toArray, List.mem_flatMap] at hmember
  obtain ⟨index, hindex, hclause⟩ := hmember
  exact rowClause_satisfied values guardPolarity length bound index
    (List.mem_range.mp hindex) hbound hboundPositive _ hclause

#print axioms sequentialAtMost_sat

end LRATCatcher.Tests.R55.SequentialCounter
