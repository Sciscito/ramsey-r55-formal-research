import LRATCatcher.Tests.R45DegreeEightGuardedMaster
import LRATCatcher.Tests.R45DegreeReductionCertified

/-!
  # Remaining root degrees after the certified degree-eight branch

  The classical handshaking reduction already forces a red degree in
  `{8, 10, 12}` in every hypothetical `(4,5)`-free coloring of `K_25`.
  The guarded 59-leaf LRAT certificate excludes degree eight, leaving the
  two exact global branches `10` and `12`.
-/

namespace LRATCatcher.Tests.R45RemainingDegrees

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeReductionCertified
open LRATCatcher.Tests.R45DegreeEightGuardedMaster

/-- Every hypothetical `(4,5)`-free coloring of `K_25` has a vertex whose red
degree is exactly ten or twelve. -/
theorem certified_exists_red_degree_ten_or_twelve
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∃ root, root < 25 ∧
      ((colorNeighbors coloring root false).length = 10 ∨
       (colorNeighbors coloring root false).length = 12) := by
  obtain ⟨root, hroot, hdegree⟩ :=
    certified_exists_red_degree_eight_ten_or_twelve hfree
  refine ⟨root, hroot, ?_⟩
  rcases hdegree with hdegree | hdegree | hdegree
  · exact False.elim
      ((no_root_has_redDegree_eight_certified hfree root hroot) hdegree)
  · exact Or.inl hdegree
  · exact Or.inr hdegree

/-- Counterexample-object form of the two-branch global reduction. -/
theorem certified_counterexample_has_degree_ten_or_twelve
    (hcounterexample : hasRamseyFreeColoring 25 4 5) :
    ∃ coloring root,
      isRamseyFree 25 4 5 coloring ∧ root < 25 ∧
      ((colorNeighbors coloring root false).length = 10 ∨
       (colorNeighbors coloring root false).length = 12) := by
  obtain ⟨coloring, hfree⟩ := hcounterexample
  obtain ⟨root, hroot, hdegree⟩ :=
    certified_exists_red_degree_ten_or_twelve hfree
  exact ⟨coloring, root, hfree, hroot, hdegree⟩

#print axioms certified_exists_red_degree_ten_or_twelve
#print axioms certified_counterexample_has_degree_ten_or_twelve

end LRATCatcher.Tests.R45RemainingDegrees
