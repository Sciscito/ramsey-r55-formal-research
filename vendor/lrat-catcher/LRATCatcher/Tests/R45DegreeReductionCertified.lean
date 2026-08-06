import LRATCatcher.Tests.R45DegreeParity
import LRATCatcher.Tests.R35UpperBound
import LRATCatcher.Tests.RamseyUpperBounds

/-!
  Closed endpoint for the classical degree reduction in a hypothetical
  `(4,5)`-free coloring of `K_25`.

  The two small Ramsey hypotheses used by the semantic reduction are supplied
  here by this repository's checked catalogue proof of `R(3,5) <= 14` and its
  checked LRAT-plus-recurrence proof of `R(4,4) <= 18`.
-/

namespace LRATCatcher.Tests.R45DegreeReductionCertified

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeParity

/-- Every hypothetical `(4,5)`-free coloring of `K_25` has a vertex whose red
degree is exactly 8, 10, or 12, with no external Ramsey-bound hypothesis. -/
theorem certified_exists_red_degree_eight_ten_or_twelve
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∃ root, root < 25 ∧
      ((colorNeighbors coloring root false).length = 8 ∨
       (colorNeighbors coloring root false).length = 10 ∨
       (colorNeighbors coloring root false).length = 12) :=
  exists_red_degree_eight_ten_or_twelve hfree
    LRATCatcher.Tests.R35.r35_upper_catalogue
    LRATCatcher.Tests.RamseyUpperBounds.r44_upper

/-- Existential version starting from a semantic counterexample object. -/
theorem certified_counterexample_has_reduced_degree
    (hcounterexample : hasRamseyFreeColoring 25 4 5) :
    ∃ coloring root,
      isRamseyFree 25 4 5 coloring ∧ root < 25 ∧
      ((colorNeighbors coloring root false).length = 8 ∨
       (colorNeighbors coloring root false).length = 10 ∨
       (colorNeighbors coloring root false).length = 12) :=
  counterexample_has_reduced_degree hcounterexample
    LRATCatcher.Tests.R35.r35_upper_catalogue
    LRATCatcher.Tests.RamseyUpperBounds.r44_upper

#print axioms certified_counterexample_has_reduced_degree

end LRATCatcher.Tests.R45DegreeReductionCertified
