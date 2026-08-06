import LRATCatcher.Tests.R45DegreeEightBridge
import LRATCatcher.Tests.R44Gen4416Classification

/-!
  # Certified `gen358`/`gen4416` bridge for the degree-eight branch

  In a hypothetical `(4,5)`-free coloring of `K_25`, a root with eight red
  neighbours determines both a certified `gen358` parent for its red block
  and one of the two classified `gen4416` graphs for its sixteen-vertex blue
  block after the standard color complementation.
-/

namespace LRATCatcher.Tests.R45DegreeEightGen4416Bridge

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R45DegreeEightBridge
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData
open LRATCatcher.Tests.R44Gen4416Classification

/-- Every degree-eight branch simultaneously enters a certified `gen358`
parent on the red side and one of the two classified `gen4416` graphs on
the complemented blue side. -/
theorem degree_eight_enters_gen358_and_gen4416
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    (∃ parentIndex, parentIndex < gen358ParentIds.length ∧
      CoveredByGen358Parent
        (redDegreeEightGraph coloring root hdegree)
        (gen358ParentIds.getD parentIndex 0)) ∧
      ∃ targetIndex, targetIndex < gen4416GraphIds.length ∧
        GraphIsomorphicFin
          (coloringGraph 16
            (blueDegreeSixteenColoring coloring root hroot hdegree))
          (gen4416Graph targetIndex) := by
  obtain ⟨hparent, hblueFree⟩ :=
    degree_eight_local_split hfree root hroot hdegree
  exact ⟨hparent,
    ramseyFree_isomorphic_to_gen4416
      (blueDegreeSixteenColoring coloring root hroot hdegree) hblueFree⟩

#print axioms degree_eight_enters_gen358_and_gen4416

end LRATCatcher.Tests.R45DegreeEightGen4416Bridge
