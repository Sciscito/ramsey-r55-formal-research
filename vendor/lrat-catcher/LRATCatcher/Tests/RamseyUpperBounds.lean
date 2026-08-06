import LRATCatcher.Tests.RamseyRecurrence

/-!
  # Small Ramsey upper bounds used by the R(5,5) project

  Certificates in this module are generated from the exact Lean encoder with
  `lratcatch-gen` and replayed by the verified LRAT checker.
-/

namespace LRATCatcher.Tests.RamseyUpperBounds

open LRATCatcher.Ramsey

-- The classical upper bound `R(3,4) <= 9`, certified by LRAT.
ramsey_lrat r34_upper 9 3 4 "examples/ramsey/r34/r34_9.lrat"

#print axioms r34_upper

/-- The classical recurrence `R(4,4) ≤ R(3,4) + R(4,3)` turns the certified
`R(3,4) ≤ 9` bound into `R(4,4) ≤ 18`. -/
theorem r44_upper : ¬ hasRamseyFreeColoring 18 4 4 :=
  LRATCatcher.Tests.RamseyRecurrence.r44_upper_of_r34_upper r34_upper

#print axioms r44_upper

end LRATCatcher.Tests.RamseyUpperBounds
