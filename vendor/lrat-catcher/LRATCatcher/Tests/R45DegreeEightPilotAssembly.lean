import LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore

/-!
  # End-to-end closure of the certified `d8_l22_r01` leaf

  The generic degree-eight assembly core transports arbitrary catalogue
  witnesses to their exact direct-unit cube.  This module only instantiates
  that result at `gen358` parent 22 and `gen4416` target 1, then applies the
  corresponding replayed LRAT contradiction.
-/

namespace LRATCatcher.Tests.R45DegreeEightPilotAssembly

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightBridge
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R45DegreeEightPilotSemantics
open LRATCatcher.Tests.R45DegreeEightReducedAssignment
open LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-- The exact catalogue witnesses for parent 22 and target 1 force all 148
unit clauses of the LRAT-certified leaf, hence contradict `(4,5)`-freeness. -/
theorem no_degreeEight_l22r01_of_catalogue_witnesses
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (hred : CoveredByGen358Parent
      (redDegreeEightGraph coloring root hdegree)
      (gen358ParentIds.getD 22 0))
    (hblue : GraphIsomorphicFin
      (coloringGraph 16
        (blueDegreeSixteenColoring coloring root hroot hdegree))
      (gen4416Graph 1)) : False := by
  have htarget : 1 < gen4416GraphIds.length := by
    have hcount := gen4416_graph_count
    omega
  obtain ⟨assembly⟩ := catalogueWitnesses_leafAssembly
    root hroot hdegree 22 1 htarget hred hblue
  apply no_l22r01_of_canonical_reducedAssignment
    hfree assembly.canonical
  simpa [l22r01Units] using assembly.units

#print axioms no_degreeEight_l22r01_of_catalogue_witnesses

end LRATCatcher.Tests.R45DegreeEightPilotAssembly