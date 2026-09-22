import LRATCatcher.Tests.R45DegreeTwelveBridge
import LRATCatcher.Tests.R44RootedGraphReduction

/-!
  # Raw blue-block semantics for the degree-twelve branch

  The main degree-twelve bridge normalizes the blue-neighbour block by
  complementing its colors.  SAT certificates may instead use the ambient
  (raw) colors directly.  At `R(4,4)` the two presentations are equivalent:
  the raw coloring is pointwise the complement of the normalized coloring,
  and exchanging the two colors preserves Ramsey freeness.
-/

namespace LRATCatcher.Tests.R45DegreeTwelveRawBlueBridge

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45RootDegreeCore
open LRATCatcher.Tests.R45DegreeTwelveBridge
open LRATCatcher.Tests.R44RootedGraphReduction

/-- The uncomplemented blue-neighbour coloring is exactly the pointwise
complement of the normalized blue-neighbour coloring.  This is stated on all
natural-number indices, not merely on genuine `edgeVar 12` indices. -/
theorem blueDegreeTwelveRawColoring_eq_complement
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    blueDegreeTwelveRawColoring coloring root hroot hdegree =
      complementColoring
        (blueDegreeTwelveColoring coloring root hroot hdegree) := by
  funext index
  simp [blueDegreeTwelveRawColoring, blueDegreeTwelveColoring,
    blueNeighborRawColoring, blueNeighborColoring, inducedColoring,
    complementColoring]

/-- Edge-variable form of `blueDegreeTwelveRawColoring_eq_complement`. -/
theorem blueDegreeTwelveRawColoring_edgeVar_eq_not_complemented
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (left right : Fin 12) :
    blueDegreeTwelveRawColoring coloring root hroot hdegree
        (edgeVar 12 left.val right.val) =
      !(blueDegreeTwelveColoring coloring root hroot hdegree
        (edgeVar 12 left.val right.val)) := by
  rw [blueDegreeTwelveRawColoring_eq_complement]
  rfl

/-- Direct `R(4,4,12)` fact for the ambient (uncomplemented) blue block.

The existing degree-twelve theorem supplies freeness of the normalized
coloring.  Color symmetry at `(4,4)` then transfers it to the raw coloring.
-/
theorem blueDegreeTwelveRawColoring_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    isRamseyFree 12 4 4
      (blueDegreeTwelveRawColoring coloring root hroot hdegree) := by
  have hnormalized : isRamseyFree 12 4 4
      (blueDegreeTwelveColoring coloring root hroot hdegree) :=
    blueDegreeTwelveColoring_isRamseyFree hfree root hroot hdegree
  have hcomplement := complementColoring_isRamseyFree hnormalized
  rwa [← blueDegreeTwelveRawColoring_eq_complement
    coloring root hroot hdegree] at hcomplement

#print axioms blueDegreeTwelveRawColoring_eq_complement
#print axioms blueDegreeTwelveRawColoring_edgeVar_eq_not_complemented
#print axioms blueDegreeTwelveRawColoring_isRamseyFree

end LRATCatcher.Tests.R45DegreeTwelveRawBlueBridge
