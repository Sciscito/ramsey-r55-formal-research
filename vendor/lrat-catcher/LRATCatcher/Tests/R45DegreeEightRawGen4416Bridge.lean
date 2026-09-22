import LRATCatcher.Tests.R45DegreeEightGen4416Bridge

/-!
  # Raw blue-block bridge for the degree-eight branch

  The `R(4,4,16)` classifier is applied to the complemented coloring of the
  sixteen blue neighbours.  The direct degree-eight DIMACS leaves instead
  constrain their raw ambient colors.  Since each checked `gen4416` target is
  self-complementary, the raw block is strongly isomorphic to the same target.
-/

namespace LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightBridge
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData
open LRATCatcher.Tests.R44Gen4416Classification

/-- An isomorphism from the complemented blue block to a checked `gen4416`
target induces an isomorphism from the raw ambient blue block to the same
target.  The intermediate graph is the complemented target; its checked
self-complementing permutation closes the color-orientation gap. -/
theorem blueDegreeSixteenRaw_isomorphic_to_gen4416
    {coloring : Nat → Bool}
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (targetIndex : Nat) (htarget : targetIndex < gen4416GraphIds.length)
    (hisomorphic : GraphIsomorphicFin
      (coloringGraph 16
        (blueDegreeSixteenColoring coloring root hroot hdegree))
      (gen4416Graph targetIndex)) :
    GraphIsomorphicFin
      (coloringGraph 16
        (blueDegreeSixteenRawColoring coloring root hroot hdegree))
      (gen4416Graph targetIndex) := by
  let raw := blueDegreeSixteenRawColoring coloring root hroot hdegree
  have hcomplemented : GraphIsomorphicFin
      (coloringGraph 16 (complementColoring raw))
      (gen4416Graph targetIndex) := by
    simpa [raw, blueDegreeSixteenRawColoring,
      blueDegreeSixteenColoring, inducedColoring,
      complementColoring] using hisomorphic
  exact GraphIsomorphicFin.trans
    (originalGraph_to_complementGen4416 raw targetIndex hcomplemented)
    (gen4416_self_complementary targetIndex htarget)

#print axioms blueDegreeSixteenRaw_isomorphic_to_gen4416

end LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge
