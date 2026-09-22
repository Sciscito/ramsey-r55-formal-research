import LRATCatcher.Tests.R45DegreeReduction
import LRATCatcher.Tests.R35UpperBound
import LRATCatcher.Tests.R45DegreeEightCover

/-!
  # Semantic bridge for the local degree-eight split

  A red neighbourhood of size eight in a hypothetical `(4,5)`-free coloring
  of `K_25` inherits a `(3,5)`-free coloring.  Packing that restriction into
  the certified catalogue graph representation lets the exhaustive `gen358`
  theorem select a concrete left parent.  The complementary sixteen blue
  neighbours simultaneously inherit a complemented `(4,4)`-free coloring.
-/

namespace LRATCatcher.Tests.R45DegreeEightBridge

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightCover

/-- The generic local decoder has the expected row-major round trip at
order eight. -/
theorem localEdgePair_edgeVar_eight (left right : Fin 8)
    (hordered : left < right) :
    localEdgePair 8 (edgeVar 8 left.val right.val) = (left, right) := by
  native_decide +revert

/-- The same finite decoder round trip at order sixteen. -/
theorem localEdgePair_edgeVar_sixteen (left right : Fin 16)
    (hordered : left < right) :
    localEdgePair 16 (edgeVar 16 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Canonical enumeration of all eight red neighbours of `root`. -/
def redDegreeEightEmbedding (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Fin 8 → AmbientVertex :=
  neighborEmbedding coloring root false (by omega)

/-- The exact local Ramsey coloring induced on the eight red neighbours. -/
def redDegreeEightColoring (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Nat → Bool :=
  inducedColoring 8 (redDegreeEightEmbedding coloring root hdegree)
    coloring false

/-- Packed catalogue graph of the induced red neighbourhood. -/
def redDegreeEightGraph (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 8) : Graph :=
  coloringGraph 8 (redDegreeEightColoring coloring root hdegree)

theorem redDegreeEightEmbedding_injective (coloring : Nat → Bool)
    (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Function.Injective (redDegreeEightEmbedding coloring root hdegree) := by
  simpa [redDegreeEightEmbedding] using
    neighborEmbedding_injective coloring root false (by omega)

theorem redDegreeEightEmbedding_ne_root (coloring : Nat → Bool)
    (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (index : Fin 8) :
    root ≠ (redDegreeEightEmbedding coloring root hdegree index).val := by
  simpa [redDegreeEightEmbedding] using
    neighborEmbedding_ne_root coloring root false (by omega) index

theorem redDegreeEightEmbedding_color (coloring : Nat → Bool)
    (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (index : Fin 8) :
    LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring root
      (redDegreeEightEmbedding coloring root hdegree index).val = true := by
  simpa [redDegreeEightEmbedding] using
    neighborEmbedding_color coloring root false (by omega) index

/-- The degree-eight red neighbourhood has exactly the `(3,5)` validity used
by the exhaustive order-eight catalogue. -/
theorem redDegreeEightColoring_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    isRamseyFree 8 3 5
      (redDegreeEightColoring coloring root hdegree) := by
  exact red_induced_isRamseyFree_of_decoder hfree
    (redDegreeEightEmbedding coloring root hdegree)
    (redDegreeEightEmbedding_injective coloring root hdegree)
    localEdgePair_edgeVar_eight ⟨root, hroot⟩
    (redDegreeEightEmbedding_ne_root coloring root hdegree)
    (redDegreeEightEmbedding_color coloring root hdegree)

theorem redDegreeEightGraph_validAt
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    GraphValidAt 8 (redDegreeEightGraph coloring root hdegree) := by
  exact coloringGraph_validAt 8
    (redDegreeEightColoring coloring root hdegree)
    (redDegreeEightColoring_isRamseyFree hfree root hroot hdegree)

/-! ## The complementary blue block -/

theorem blueDegreeSixteen_length (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    (colorNeighbors coloring root true).length = 16 := by
  have hsum := colorNeighbors_length_sum_twentyFour coloring root hroot
  omega

/-- Canonical enumeration of all sixteen blue neighbours of `root`. -/
def blueDegreeSixteenEmbedding (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Fin 16 → AmbientVertex :=
  neighborEmbedding coloring root true (by
    rw [blueDegreeSixteen_length coloring root hroot hdegree]
    omega)

/-- Raw ambient colors on the blue block.  This is the convention required
later by the DIMACS units. -/
def blueDegreeSixteenRawColoring (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Nat → Bool :=
  inducedColoring 16
    (blueDegreeSixteenEmbedding coloring root hroot hdegree) coloring false

/-- Complemented colors on the blue block.  Complementation turns the
inherited local condition into the symmetric `(4,4)` convention. -/
def blueDegreeSixteenColoring (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Nat → Bool :=
  inducedColoring 16
    (blueDegreeSixteenEmbedding coloring root hroot hdegree) coloring true

theorem blueDegreeSixteenEmbedding_injective (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    Function.Injective
      (blueDegreeSixteenEmbedding coloring root hroot hdegree) := by
  simpa [blueDegreeSixteenEmbedding] using
    neighborEmbedding_injective coloring root true (by
      rw [blueDegreeSixteen_length coloring root hroot hdegree]
      omega)

theorem blueDegreeSixteenEmbedding_ne_root (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (index : Fin 16) :
    root ≠
      (blueDegreeSixteenEmbedding coloring root hroot hdegree index).val := by
  simpa [blueDegreeSixteenEmbedding] using
    neighborEmbedding_ne_root coloring root true (by
      rw [blueDegreeSixteen_length coloring root hroot hdegree]
      omega) index

theorem blueDegreeSixteenEmbedding_color (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (index : Fin 16) :
    LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring root
      (blueDegreeSixteenEmbedding coloring root hroot hdegree index).val =
        false := by
  simpa [blueDegreeSixteenEmbedding] using
    neighborEmbedding_color coloring root true (by
      rw [blueDegreeSixteen_length coloring root hroot hdegree]
      omega) index

/-- The exact sixteen-vertex blue block forced by a red degree of eight is
`(4,4)`-free after complementation. -/
theorem blueDegreeSixteenColoring_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    isRamseyFree 16 4 4
      (blueDegreeSixteenColoring coloring root hroot hdegree) := by
  exact blue_induced_isRamseyFree_of_decoder hfree
    (blueDegreeSixteenEmbedding coloring root hroot hdegree)
    (blueDegreeSixteenEmbedding_injective coloring root hroot hdegree)
    localEdgePair_edgeVar_sixteen ⟨root, hroot⟩
    (blueDegreeSixteenEmbedding_ne_root coloring root hroot hdegree)
    (blueDegreeSixteenEmbedding_color coloring root hroot hdegree)

/-- On actual local edge variables, the raw DIMACS convention is exactly
the Boolean complement of the `(4,4)` coloring above. -/
theorem blueDegreeSixteenRaw_eq_not_complemented
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (left right : Fin 16) (hordered : left < right) :
    blueDegreeSixteenRawColoring coloring root hroot hdegree
        (edgeVar 16 left.val right.val) =
      !(blueDegreeSixteenColoring coloring root hroot hdegree
        (edgeVar 16 left.val right.val)) := by
  simp [blueDegreeSixteenRawColoring, blueDegreeSixteenColoring,
    inducedColoring, localEdgePair_edgeVar_sixteen left right hordered]

/-- Every actual degree-eight branch of a hypothetical `(4,5)`-free
`K_25` coloring enters one of the 27 certified `gen358` parents. -/
theorem red_degree_eight_enters_gen358
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    ∃ parentIndex, parentIndex < gen358ParentIds.length ∧
      CoveredByGen358Parent
        (redDegreeEightGraph coloring root hdegree)
        (gen358ParentIds.getD parentIndex 0) := by
  exact every_r35_order_eight_graph_enters_gen358
    (redDegreeEightGraph coloring root hdegree)
    (redDegreeEightGraph_validAt hfree root hroot hdegree)

/-- Certified local decomposition of every degree-eight branch: the left
block enters `gen358`, while the right block is a concrete `(4,4,16)`-free
coloring. -/
theorem degree_eight_local_split
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    (∃ parentIndex, parentIndex < gen358ParentIds.length ∧
      CoveredByGen358Parent
        (redDegreeEightGraph coloring root hdegree)
        (gen358ParentIds.getD parentIndex 0)) ∧
      isRamseyFree 16 4 4
        (blueDegreeSixteenColoring coloring root hroot hdegree) := by
  exact ⟨red_degree_eight_enters_gen358 hfree root hroot hdegree,
    blueDegreeSixteenColoring_isRamseyFree hfree root hroot hdegree⟩

#print axioms red_degree_eight_enters_gen358
#print axioms degree_eight_local_split

end LRATCatcher.Tests.R45DegreeEightBridge
