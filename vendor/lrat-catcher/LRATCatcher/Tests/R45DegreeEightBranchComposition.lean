import LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore
import LRATCatcher.Tests.R45DegreeEightGen4416Bridge

/-!
  # Global composition of the red-degree-eight branch

  A future guarded master certificate only needs to establish one semantic
  interface: for every admissible pair of catalogue indices, no reduced
  assignment can satisfy both the structural degree-eight constraints and
  that pair's direct-unit cube.

  The theorem below composes such pairwise contradictions with the certified
  `gen358`/`gen4416` classification and the generic leaf assembly.  It thereby
  excludes every red-degree-eight root in a hypothetical `(4,5)`-free
  coloring of `K_25`, without mentioning a particular LRAT certificate.
-/

namespace LRATCatcher.Tests.R45DegreeEightBranchComposition

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightCover
open LRATCatcher.Tests.R45DegreeEightBridge
open LRATCatcher.Tests.R45DegreeEightGen4416Bridge
open LRATCatcher.Tests.R45DegreeEightPilotSemantics
open LRATCatcher.Tests.R45DegreeEightReducedAssignment
open LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore
open LRATCatcher.Tests.R45DegreeEightGlobalPermutation
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-- The exact direct-unit cube selected by one left/right catalogue pair. -/
def degreeEightPairUnits (parentIndex targetIndex : Nat) : List Int :=
  gen358DirectUnits parentIndex ++ gen4416DirectUnits targetIndex

/-- Certificate-facing interface for one catalogue pair.

It deliberately quantifies only over the reduced order-24 assignment.  A
guarded master formula can therefore prove this predicate without knowing
anything about the original root, embeddings, or catalogue isomorphisms. -/
def DegreeEightPairContradiction
    (parentIndex targetIndex : Nat) : Prop :=
  ∀ assignment : Nat → Bool,
    ReducedAssignmentSemantics assignment →
    AllUnitsSatisfied assignment
      (degreeEightPairUnits parentIndex targetIndex) →
    False

/-- All semantically possible catalogue pairs have been refuted.  Bounds are
kept explicit so a future guarded certificate may use any convenient finite
selector encoding and prove only the decoded valid cases. -/
def AllAdmissibleDegreeEightPairsContradictory : Prop :=
  ∀ parentIndex, parentIndex < gen358ParentIds.length →
    ∀ targetIndex, targetIndex < gen4416GraphIds.length →
      DegreeEightPairContradiction parentIndex targetIndex

/-- Pairwise reduced-assignment contradictions compose with the two catalogue
classifications to exclude an arbitrary root of red degree eight. -/
theorem no_degreeEight_root_of_all_pair_contradictions
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hall : AllAdmissibleDegreeEightPairsContradictory)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) : False := by
  obtain ⟨⟨parentIndex, hparentBound, hred⟩,
      targetIndex, htargetBound, hblue⟩ :=
    degree_eight_enters_gen358_and_gen4416
      hfree root hroot hdegree
  obtain ⟨assembly⟩ := catalogueWitnesses_leafAssembly
    root hroot hdegree parentIndex targetIndex htargetBound hred hblue
  let assignment := reducedAssignment
    (degreeEightGlobalPermutation coloring root hroot hdegree
      assembly.redPermutation assembly.bluePermutation) coloring
  have hsemantics : ReducedAssignmentSemantics assignment := by
    exact canonical_reducedAssignment_semantics hfree assembly.canonical
  have hunits : AllUnitsSatisfied assignment
      (degreeEightPairUnits parentIndex targetIndex) := by
    simpa [assignment, degreeEightPairUnits] using assembly.units
  exact hall parentIndex hparentBound targetIndex htargetBound
    assignment hsemantics hunits

/-- Equivalent rootwise formulation: in a `(4,5)`-free coloring, no ambient
vertex has exactly eight red neighbours once all admissible pair interfaces
have been certified. -/
theorem no_root_has_redDegree_eight
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hall : AllAdmissibleDegreeEightPairsContradictory) :
    ∀ root, root < 25 →
      (colorNeighbors coloring root false).length ≠ 8 := by
  intro root hroot hdegree
  exact no_degreeEight_root_of_all_pair_contradictions
    hfree hall root hroot hdegree

#print axioms no_degreeEight_root_of_all_pair_contradictions
#print axioms no_root_has_redDegree_eight

end LRATCatcher.Tests.R45DegreeEightBranchComposition
