import LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation
import LRATCatcher.Tests.R44Gen4416Classification

/-!
  # Root-neighborhood symmetry breaking at order twelve

  A coloring of `K_12` can be pulled back along a genuine permutation that
  fixes vertex zero and places all true edges from zero before all false
  edges.  The construction is finite and executable: it filters the eleven
  non-root labels by their root-edge color and turns the resulting list into
  a `FinPermutation 12`.

  Besides the prefix clauses, this module records transport of semantic
  `R(4,4)` freeness and of induced motif occurrences.  These are the two
  invariants needed to use the prefix clauses in a universal cover CNF.
-/

namespace LRATCatcher.Tests.R44OrderTwelveRootSymmetry

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44Gen4416Classification

abbrev Vertex := Fin 12
abbrev RootPattern := BitVec 11

def patternColor (pattern : RootPattern) (vertex : Fin 11) : Bool :=
  pattern.getLsbD vertex.val

/-! ## A fixed-order coloring pullback -/

theorem localEdgePair_edgeVar_twelve (left right : Vertex)
    (hordered : left < right) :
    localEdgePair 12 (edgeVar 12 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Pull a twelve-vertex coloring back along a genuine vertex permutation. -/
def permuteColoring (permutation : FinPermutation 12)
    (coloring : Nat -> Bool) (index : Nat) : Bool :=
  let endpoints := localEdgePair 12 index
  coloringEdge 12 coloring
    (permutation endpoints.1).val (permutation endpoints.2).val

theorem permuteColoring_edgeVar (permutation : FinPermutation 12)
    (coloring : Nat -> Bool) (left right : Vertex)
    (hordered : left < right) :
    permuteColoring permutation coloring (edgeVar 12 left.val right.val) =
      coloringEdge 12 coloring
        (permutation left).val (permutation right).val := by
  simp [permuteColoring, localEdgePair_edgeVar_twelve left right hordered]

theorem coloringEdge_permuteColoring (permutation : FinPermutation 12)
    (coloring : Nat -> Bool) (left right : Vertex) :
    coloringEdge 12 (permuteColoring permutation coloring)
        left.val right.val =
      coloringEdge 12 coloring
        (permutation left).val (permutation right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [coloringEdge, hordered] using
      permuteColoring_edgeVar permutation coloring left right hordered
  · have : left = right := Fin.ext hequal
    subst right
    simp
  · have hreverseFin : right < left := hreverse
    rw [coloringEdge_comm 12
      (permuteColoring permutation coloring) left.val right.val]
    rw [show coloringEdge 12 (permuteColoring permutation coloring)
        right.val left.val =
          permuteColoring permutation coloring
            (edgeVar 12 right.val left.val) by
      simp [coloringEdge, hreverse]]
    rw [permuteColoring_edgeVar permutation coloring right left hreverseFin]
    exact coloringEdge_comm 12 coloring _ _

/-! ## Executable root sorting -/

/-- The eleven non-root indices, true root edges first and false edges last. -/
def sortedNonRoot (pattern : RootPattern) : List (Fin 11) :=
  (List.finRange 11).filter (patternColor pattern) ++
    (List.finRange 11).filter (fun vertex => !(patternColor pattern vertex))

/-- Full old-vertex list indexed by the new labels `0, ..., 11`. -/
def sortedLabels (pattern : RootPattern) : List Nat :=
  0 :: (sortedNonRoot pattern).map (fun vertex => vertex.val + 1)

theorem sortedLabels_isPermutation (pattern : RootPattern) :
    isPermutation (sortedLabels pattern) 12 = true := by
  native_decide +revert

end LRATCatcher.Tests.R44OrderTwelveRootSymmetry
