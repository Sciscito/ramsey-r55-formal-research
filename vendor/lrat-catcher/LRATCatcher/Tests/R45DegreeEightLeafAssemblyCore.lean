import LRATCatcher.Tests.R45DegreeEightGlobalPermutation
import LRATCatcher.Tests.R45DegreeEightReducedAssignment
import LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge
import LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge

/-!
  # Generic assembly core for degree-eight SAT leaves

  For arbitrary `gen358` and `gen4416` indices, catalogue witnesses determine
  two local permutations.  This module assembles them into the ambient
  block permutation of `Fin 25` and proves that the resulting reduced
  assignment satisfies the concatenation of the two generated unit lists.

  No particular LRAT certificate or leaf index is used here.
-/

namespace LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightBridge
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R45DegreeEightGlobalPermutation
open LRATCatcher.Tests.R45DegreeEightPilotSemantics
open LRATCatcher.Tests.R45DegreeEightReducedAssignment
open LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge
open LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-! ## Private transport facts -/

private theorem globalPermutation_canonicalRoot
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    CanonicalDegreeEightRoot coloring ⟨root, hroot⟩
      (degreeEightGlobalPermutation coloring root hroot hdegree
        redPermutation bluePermutation) := by
  constructor
  · exact degreeEightGlobalPermutation_root coloring root hroot hdegree
      redPermutation bluePermutation
  · intro index
    simpa using redDegreeEightEmbedding_color coloring root hdegree
      (redPermutation index)
  · intro index
    simpa using blueDegreeSixteenEmbedding_color coloring root hroot hdegree
      (bluePermutation index)

private theorem reducedAssignment_global_red
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16)
    (left right : Fin 8) (hordered : left < right) :
    reducedAssignment
        (degreeEightGlobalPermutation coloring root hroot hdegree
          redPermutation bluePermutation) coloring
        (edgeVar 24 left.val right.val) =
      edge (redDegreeEightGraph coloring root hdegree)
        (redPermutation left).val (redPermutation right).val := by
  let global := degreeEightGlobalPermutation coloring root hroot hdegree
    redPermutation bluePermutation
  let left24 : Fin 24 := ⟨left.val, by omega⟩
  let right24 : Fin 24 := ⟨right.val, by omega⟩
  have hordered24 : left24 < right24 := by
    simpa [left24, right24] using hordered
  have hne : redPermutation left ≠ redPermutation right := by
    intro hequal
    have hinput : left = right :=
      FinPermutation.injective redPermutation hequal
    omega
  calc
    reducedAssignment global coloring
        (edgeVar 24 left.val right.val) =
        LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
          (nonRootEmbedding global left24).val
          (nonRootEmbedding global right24).val := by
      simpa [left24, right24] using
        reducedAssignment_edgeVar global coloring left24 right24 hordered24
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
        (redDegreeEightEmbedding coloring root hdegree
          (redPermutation left)).val
        (redDegreeEightEmbedding coloring root hdegree
          (redPermutation right)).val := by
      simp [global, nonRootEmbedding, left24, right24]
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 8
        (redDegreeEightColoring coloring root hdegree)
          (redPermutation left).val (redPermutation right).val := by
      symm
      simpa [redDegreeEightColoring] using
        ramseyEdge_inducedColoring
          (redDegreeEightEmbedding coloring root hdegree)
          coloring false localEdgePair_edgeVar_eight
          (redPermutation left) (redPermutation right) hne
    _ = coloringEdge 8 (redDegreeEightColoring coloring root hdegree)
        (redPermutation left).val (redPermutation right).val := by rfl
    _ = edge (redDegreeEightGraph coloring root hdegree)
        (redPermutation left).val (redPermutation right).val := by
      symm
      simpa [redDegreeEightGraph] using
        edge_coloringGraph 8
          (redDegreeEightColoring coloring root hdegree)
          (redPermutation left) (redPermutation right)

private theorem reducedAssignment_global_blue
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16)
    (left right : Fin 16) (hordered : left < right) :
    reducedAssignment
        (degreeEightGlobalPermutation coloring root hroot hdegree
          redPermutation bluePermutation) coloring
        (edgeVar 24 (left.val + 8) (right.val + 8)) =
      coloringEdge 16
        (blueDegreeSixteenRawColoring coloring root hroot hdegree)
        (bluePermutation left).val (bluePermutation right).val := by
  let global := degreeEightGlobalPermutation coloring root hroot hdegree
    redPermutation bluePermutation
  let left24 : Fin 24 := ⟨left.val + 8, by omega⟩
  let right24 : Fin 24 := ⟨right.val + 8, by omega⟩
  have hordered24 : left24 < right24 := by
    simpa [left24, right24] using hordered
  have hne : bluePermutation left ≠ bluePermutation right := by
    intro hequal
    have hinput : left = right :=
      FinPermutation.injective bluePermutation hequal
    omega
  calc
    reducedAssignment global coloring
        (edgeVar 24 (left.val + 8) (right.val + 8)) =
        LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
          (nonRootEmbedding global left24).val
          (nonRootEmbedding global right24).val := by
      simpa [left24, right24] using
        reducedAssignment_edgeVar global coloring left24 right24 hordered24
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
        (blueDegreeSixteenEmbedding coloring root hroot hdegree
          (bluePermutation left)).val
        (blueDegreeSixteenEmbedding coloring root hroot hdegree
          (bluePermutation right)).val := by
      simp [global, nonRootEmbedding, left24, right24]
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 16
        (blueDegreeSixteenRawColoring coloring root hroot hdegree)
          (bluePermutation left).val (bluePermutation right).val := by
      symm
      simpa [blueDegreeSixteenRawColoring] using
        ramseyEdge_inducedColoring
          (blueDegreeSixteenEmbedding coloring root hroot hdegree)
          coloring false localEdgePair_edgeVar_sixteen
          (bluePermutation left) (bluePermutation right) hne
    _ = coloringEdge 16
        (blueDegreeSixteenRawColoring coloring root hroot hdegree)
        (bluePermutation left).val (bluePermutation right).val := by rfl

/-! ## Generic assembled witness -/

/-- Structural output shared by every degree-eight SAT leaf.  Its two local
permutations determine the ambient permutation, the canonical root split,
and all direct catalogue units. -/
structure DegreeEightLeafAssembly
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (parentIndex targetIndex : Nat) where
  redPermutation : FinPermutation 8
  bluePermutation : FinPermutation 16
  canonical : CanonicalDegreeEightRoot coloring ⟨root, hroot⟩
    (degreeEightGlobalPermutation coloring root hroot hdegree
      redPermutation bluePermutation)
  units : AllUnitsSatisfied
    (reducedAssignment
      (degreeEightGlobalPermutation coloring root hroot hdegree
        redPermutation bluePermutation) coloring)
    (gen358DirectUnits parentIndex ++ gen4416DirectUnits targetIndex)

namespace DegreeEightLeafAssembly

/-- The ambient permutation explicitly assembled from the two local
catalogue relabelings. -/
noncomputable def globalPermutation
    {coloring : Nat → Bool} {root : Nat} {hroot : root < 25}
    {hdegree : (colorNeighbors coloring root false).length = 8}
    {parentIndex targetIndex : Nat}
    (assembly : DegreeEightLeafAssembly coloring root hroot hdegree
      parentIndex targetIndex) : FinPermutation 25 :=
  degreeEightGlobalPermutation coloring root hroot hdegree
    assembly.redPermutation assembly.bluePermutation

end DegreeEightLeafAssembly

/-- Arbitrary valid catalogue indices assemble into one canonical ambient
permutation satisfying exactly the concatenated direct-unit cube.  Ramsey
freeness and a leaf contradiction are intentionally absent from this core. -/
theorem catalogueWitnesses_leafAssembly
    {coloring : Nat → Bool}
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (parentIndex targetIndex : Nat)
    (htarget : targetIndex < gen4416GraphIds.length)
    (hred : CoveredByGen358Parent
      (redDegreeEightGraph coloring root hdegree)
      (gen358ParentIds.getD parentIndex 0))
    (hblue : GraphIsomorphicFin
      (coloringGraph 16
        (blueDegreeSixteenColoring coloring root hroot hdegree))
      (gen4416Graph targetIndex)) :
    Nonempty (DegreeEightLeafAssembly coloring root hroot hdegree
      parentIndex targetIndex) := by
  have hwellFormed : wellFormedGraph 8
      (redDegreeEightGraph coloring root hdegree) = true := by
    simpa [redDegreeEightGraph] using
      coloringGraph_wellFormed 8
        (redDegreeEightColoring coloring root hdegree)
  obtain ⟨redWitness⟩ :=
    coveredByGen358Parent_directUnitWitness hwellFormed hred
  obtain ⟨blueWitness⟩ :=
    blueDegreeSixteen_gen4416DirectUnitWitness
      root hroot hdegree targetIndex htarget hblue
  refine ⟨{
    redPermutation := redWitness.permutation
    bluePermutation := blueWitness.permutation
    canonical := globalPermutation_canonicalRoot coloring root hroot hdegree
      redWitness.permutation blueWitness.permutation
    units := ?_
  }⟩
  let global := degreeEightGlobalPermutation coloring root hroot hdegree
    redWitness.permutation blueWitness.permutation
  have hredUnits : AllUnitsSatisfied
      (reducedAssignment global coloring)
      (gen358DirectUnits parentIndex) := by
    apply redWitness.allUnitsSatisfied
    intro left right hordered
    simpa [global] using reducedAssignment_global_red
      coloring root hroot hdegree redWitness.permutation
        blueWitness.permutation left right hordered
  have hblueUnits : AllUnitsSatisfied
      (reducedAssignment global coloring)
      (gen4416DirectUnits targetIndex) := by
    apply blueWitness.allUnitsSatisfied
    intro left right hordered
    simpa [global] using reducedAssignment_global_blue
      coloring root hroot hdegree redWitness.permutation
        blueWitness.permutation left right hordered
  intro literal hliteral
  rcases List.mem_append.mp hliteral with hleft | hright
  · exact hredUnits literal hleft
  · exact hblueUnits literal hright

#print axioms catalogueWitnesses_leafAssembly

end LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore
