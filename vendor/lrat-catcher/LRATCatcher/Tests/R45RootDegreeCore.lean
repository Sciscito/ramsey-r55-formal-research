import LRATCatcher.Tests.R45DegreeReduction
import LRATCatcher.Tests.R35UpperBound

/-!
  # Degree-parametric rooted neighbourhoods in `K_25`

  This module isolates the semantic part common to every exact root-degree
  branch of the `R(4,5,25)` search.  If a root has exactly `redOrder` red
  neighbours and `redOrder + blueOrder = 24`, the two canonical filtered
  lists give injective embeddings of `Fin redOrder` and `Fin blueOrder`.

  The red block inherits an `(3,5)`-free coloring.  After complementation,
  the blue block inherits an `(4,4)`-free coloring.  Concrete branches only
  have to supply the finite decoder round trips for their two orders.
-/

namespace LRATCatcher.Tests.R45RootDegreeCore

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction

/-! ## The exact red block -/

/-- Canonical enumeration of all red neighbours of an exact-degree root. -/
def redNeighborEmbedding (redOrder : Nat) (coloring : Nat → Bool)
    (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Fin redOrder → AmbientVertex :=
  neighborEmbedding coloring root false (by omega)

theorem redNeighborEmbedding_injective (redOrder : Nat)
    (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Function.Injective
      (redNeighborEmbedding redOrder coloring root hdegree) := by
  simpa [redNeighborEmbedding] using
    neighborEmbedding_injective coloring root false (by omega)

theorem redNeighborEmbedding_ne_root (redOrder : Nat)
    (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = redOrder)
    (index : Fin redOrder) :
    root ≠ (redNeighborEmbedding redOrder coloring root hdegree index).val := by
  simpa [redNeighborEmbedding] using
    neighborEmbedding_ne_root coloring root false (by omega) index

theorem redNeighborEmbedding_color (redOrder : Nat)
    (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = redOrder)
    (index : Fin redOrder) :
    LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring root
      (redNeighborEmbedding redOrder coloring root hdegree index).val = true := by
  simpa [redNeighborEmbedding] using
    neighborEmbedding_color coloring root false (by omega) index

/-- The coloring induced on the exact red neighbourhood. -/
def redNeighborColoring (redOrder : Nat) [NeZero redOrder]
    (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Nat → Bool :=
  inducedColoring redOrder
    (redNeighborEmbedding redOrder coloring root hdegree) coloring false

/-- Packed graph used by the exhaustive `R(3,5)` catalogues. -/
def redNeighborGraph (redOrder : Nat) [NeZero redOrder]
    (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) : Graph :=
  coloringGraph redOrder
    (redNeighborColoring redOrder coloring root hdegree)

theorem redNeighborColoring_isRamseyFree
    {redOrder : Nat} [NeZero redOrder]
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hdecoder : ∀ left right : Fin redOrder, left < right →
      localEdgePair redOrder (edgeVar redOrder left.val right.val) =
        (left, right))
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    isRamseyFree redOrder 3 5
      (redNeighborColoring redOrder coloring root hdegree) := by
  exact red_induced_isRamseyFree_of_decoder hfree
    (redNeighborEmbedding redOrder coloring root hdegree)
    (redNeighborEmbedding_injective redOrder coloring root hdegree)
    hdecoder ⟨root, hroot⟩
    (redNeighborEmbedding_ne_root redOrder coloring root hdegree)
    (redNeighborEmbedding_color redOrder coloring root hdegree)

theorem redNeighborGraph_validAt
    {redOrder : Nat} [NeZero redOrder]
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hdecoder : ∀ left right : Fin redOrder, left < right →
      localEdgePair redOrder (edgeVar redOrder left.val right.val) =
        (left, right))
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    GraphValidAt redOrder
      (redNeighborGraph redOrder coloring root hdegree) := by
  exact coloringGraph_validAt redOrder
    (redNeighborColoring redOrder coloring root hdegree)
    (redNeighborColoring_isRamseyFree hfree hdecoder root hroot hdegree)

/-! ## The complementary blue block -/

theorem blueNeighbors_length
    {redOrder blueOrder : Nat}
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    (colorNeighbors coloring root true).length = blueOrder := by
  have hsum := colorNeighbors_length_sum_twentyFour coloring root hroot
  omega

/-- Canonical enumeration of the complementary blue neighbourhood. -/
def blueNeighborEmbedding (redOrder blueOrder : Nat)
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Fin blueOrder → AmbientVertex :=
  neighborEmbedding coloring root true (by
    have hlength := blueNeighbors_length coloring root hroot hsizes hdegree
    omega)

theorem blueNeighborEmbedding_injective (redOrder blueOrder : Nat)
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Function.Injective
      (blueNeighborEmbedding redOrder blueOrder coloring root hroot
        hsizes hdegree) := by
  simpa [blueNeighborEmbedding] using
    neighborEmbedding_injective coloring root true (by
      have hlength := blueNeighbors_length coloring root hroot hsizes hdegree
      omega)

theorem blueNeighborEmbedding_ne_root (redOrder blueOrder : Nat)
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder)
    (index : Fin blueOrder) :
    root ≠
      (blueNeighborEmbedding redOrder blueOrder coloring root hroot
        hsizes hdegree index).val := by
  simpa [blueNeighborEmbedding] using
    neighborEmbedding_ne_root coloring root true (by
      have hlength := blueNeighbors_length coloring root hroot hsizes hdegree
      omega) index

theorem blueNeighborEmbedding_color (redOrder blueOrder : Nat)
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder)
    (index : Fin blueOrder) :
    LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring root
      (blueNeighborEmbedding redOrder blueOrder coloring root hroot
        hsizes hdegree index).val = false := by
  simpa [blueNeighborEmbedding] using
    neighborEmbedding_color coloring root true (by
      have hlength := blueNeighbors_length coloring root hroot hsizes hdegree
      omega) index

/-- Ambient (uncomplemented) edge colors on the blue block. -/
def blueNeighborRawColoring (redOrder blueOrder : Nat) [NeZero blueOrder]
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Nat → Bool :=
  inducedColoring blueOrder
    (blueNeighborEmbedding redOrder blueOrder coloring root hroot
      hsizes hdegree) coloring false

/-- Complemented colors on the blue block, in `(4,4)` convention. -/
def blueNeighborColoring (redOrder blueOrder : Nat) [NeZero blueOrder]
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    Nat → Bool :=
  inducedColoring blueOrder
    (blueNeighborEmbedding redOrder blueOrder coloring root hroot
      hsizes hdegree) coloring true

theorem blueNeighborColoring_isRamseyFree
    {redOrder blueOrder : Nat} [NeZero blueOrder]
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hdecoder : ∀ left right : Fin blueOrder, left < right →
      localEdgePair blueOrder (edgeVar blueOrder left.val right.val) =
        (left, right))
    (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder) :
    isRamseyFree blueOrder 4 4
      (blueNeighborColoring redOrder blueOrder coloring root hroot
        hsizes hdegree) := by
  exact blue_induced_isRamseyFree_of_decoder hfree
    (blueNeighborEmbedding redOrder blueOrder coloring root hroot
      hsizes hdegree)
    (blueNeighborEmbedding_injective redOrder blueOrder coloring root hroot
      hsizes hdegree)
    hdecoder ⟨root, hroot⟩
    (blueNeighborEmbedding_ne_root redOrder blueOrder coloring root hroot
      hsizes hdegree)
    (blueNeighborEmbedding_color redOrder blueOrder coloring root hroot
      hsizes hdegree)

theorem blueNeighborRaw_eq_not_complemented
    {redOrder blueOrder : Nat} [NeZero blueOrder]
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hsizes : redOrder + blueOrder = 24)
    (hdegree : (colorNeighbors coloring root false).length = redOrder)
    (hdecoder : ∀ left right : Fin blueOrder, left < right →
      localEdgePair blueOrder (edgeVar blueOrder left.val right.val) =
        (left, right))
    (left right : Fin blueOrder) (hordered : left < right) :
    blueNeighborRawColoring redOrder blueOrder coloring root hroot
        hsizes hdegree (edgeVar blueOrder left.val right.val) =
      !(blueNeighborColoring redOrder blueOrder coloring root hroot
        hsizes hdegree (edgeVar blueOrder left.val right.val)) := by
  simp [blueNeighborRawColoring, blueNeighborColoring, inducedColoring,
    hdecoder left right hordered]

/-! ## Canonical non-root labels -/

/-- SAT labels `1, ..., 24`, embedded canonically into ambient `Fin 25`. -/
def canonicalNonRootVertex (index : Fin 24) : AmbientVertex :=
  ⟨index.val + 1, by omega⟩

theorem canonicalNonRootVertex_injective :
    Function.Injective canonicalNonRootVertex := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  simpa [canonicalNonRootVertex] using Nat.add_right_cancel hvalues

/-- Canonical non-root labels followed by an arbitrary ambient relabeling. -/
def permutedNonRootEmbedding (permutation : FinPermutation 25) :
    Fin 24 → AmbientVertex :=
  fun index => permutation (canonicalNonRootVertex index)

theorem permutedNonRootEmbedding_injective (permutation : FinPermutation 25) :
    Function.Injective (permutedNonRootEmbedding permutation) := by
  intro left right hequal
  apply canonicalNonRootVertex_injective
  apply FinPermutation.injective permutation
  simpa [permutedNonRootEmbedding] using hequal

#print axioms redNeighborColoring_isRamseyFree
#print axioms blueNeighborColoring_isRamseyFree
#print axioms redNeighborGraph_validAt
#print axioms permutedNonRootEmbedding_injective

end LRATCatcher.Tests.R45RootDegreeCore
