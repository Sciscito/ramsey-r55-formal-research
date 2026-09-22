import LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge
import LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-!
  # Semantic `gen4416` unit bridge for the degree-eight branch

  The strong graph isomorphism produced by the sixteen-vertex classifier
  sends raw blue-block labels to a `gen4416` target.  The global degree-eight
  relabeling needs the inverse direction: a canonical target label must be
  sent to the corresponding raw blue-block label.

  This module extracts exactly that `FinPermutation 16`, proves the raw
  true/false colour of every canonical target edge, and finally discharges
  the literal-level `gen4416DirectUnits` predicate used by the LRAT leaf.
-/

namespace LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightBridge
open LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData
open LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-- The precise semantic payload of the direct `gen4416` unit cube.

The permutation sends a canonical target label to the corresponding label in
the raw blue block.  Thus `fixed_edge` has the same orientation and Boolean
polarity as `gen4416DirectUnits`: target `true` is raw `true`, and target
`false` is raw `false`. -/
structure Gen4416DirectUnitWitness
    (rawColoring : Nat -> Bool) (targetIndex : Nat) where
  permutation : FinPermutation 16
  fixed_edge : forall left right : Fin 16, left < right ->
    coloringEdge 16 rawColoring
        (permutation left).val (permutation right).val =
      ternaryColoring (gen4416GraphIds.getD targetIndex 0)
        (edgeVar 16 left.val right.val)

/-- A strong isomorphism from a raw coloring graph to a `gen4416` target
yields the inverse, target-to-raw permutation required by the direct unit
cube. -/
theorem graphIsomorphicFin_to_gen4416DirectUnitWitness
    {rawColoring : Nat -> Bool} {targetIndex : Nat}
    (hisomorphic : GraphIsomorphicFin
      (coloringGraph 16 rawColoring)
      (gen4416Graph targetIndex)) :
    Nonempty (Gen4416DirectUnitWitness rawColoring targetIndex) := by
  obtain ⟨isomorphism⟩ := hisomorphic
  rcases isomorphism with
    ⟨isoOrder, sourceOrder, targetOrder, sourceToTarget, mapEdge⟩
  have horder : isoOrder = 16 := by
    calc
      isoOrder = (coloringGraph 16 rawColoring).length := sourceOrder.symm
      _ = 16 := coloringGraph_length 16 rawColoring
  subst isoOrder
  let targetToSource : FinPermutation 16 := sourceToTarget.symm
  refine ⟨{
    permutation := targetToSource
    fixed_edge := ?_
  }⟩
  intro left right hordered
  have hmap := mapEdge (targetToSource left) (targetToSource right)
  change
    edge (coloringGraph 16 rawColoring)
        (targetToSource left).val (targetToSource right).val =
      edge (coloringGraph 16
        (ternaryColoring (gen4416GraphIds.getD targetIndex 0)))
        (sourceToTarget (targetToSource left)).val
        (sourceToTarget (targetToSource right)).val at hmap
  simp only [targetToSource, FinPermutation.apply_symm_apply] at hmap
  rw [edge_coloringGraph, edge_coloringGraph] at hmap
  have horderedNat : left.val < right.val := hordered
  simpa [targetToSource, coloringEdge, horderedNat] using hmap

/-- The raw-blue bridge closes the complement-orientation gap and then
extracts the exact target-to-raw permutation.  The input is the classifier's
isomorphism for the complemented blue coloring. -/
theorem blueDegreeSixteen_gen4416DirectUnitWitness
    {coloring : Nat -> Bool}
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (targetIndex : Nat) (htarget : targetIndex < gen4416GraphIds.length)
    (hisomorphic : GraphIsomorphicFin
      (coloringGraph 16
        (blueDegreeSixteenColoring coloring root hroot hdegree))
      (gen4416Graph targetIndex)) :
    Nonempty (Gen4416DirectUnitWitness
      (blueDegreeSixteenRawColoring coloring root hroot hdegree)
      targetIndex) :=
  graphIsomorphicFin_to_gen4416DirectUnitWitness
    (blueDegreeSixteenRaw_isomorphic_to_gen4416
      root hroot hdegree targetIndex htarget hisomorphic)

/-! ## Exact literal-level unit semantics -/

/-- The concrete list `upperPairs 16` contains precisely ordered in-range
pairs.  This finite fact connects its Python-compatible enumeration to typed
`Fin 16` endpoints. -/
theorem upperPairs_sixteen_ordered
    (pair : Nat × Nat) (hpair : pair ∈ upperPairs 16) :
    pair.1 < pair.2 ∧ pair.2 < 16 := by
  native_decide +revert

namespace Gen4416DirectUnitWitness

/-- If an order-24 assignment reads its shifted right block through the
witness permutation, then it satisfies every literal emitted by
`gen4416DirectUnits targetIndex`--including the exact `+8` shift and DIMACS
polarity. -/
theorem allUnitsSatisfied
    {rawColoring : Nat -> Bool} {targetIndex : Nat}
    (witness : Gen4416DirectUnitWitness rawColoring targetIndex)
    (assignment : Nat -> Bool)
    (hassignment : forall left right : Fin 16, left < right ->
      assignment
          (edgeVar 24 (left.val + 8) (right.val + 8)) =
        coloringEdge 16 rawColoring
          (witness.permutation left).val
          (witness.permutation right).val) :
    AllUnitsSatisfied assignment (gen4416DirectUnits targetIndex) := by
  intro literal hliteral
  simp only [gen4416DirectUnits, List.mem_map] at hliteral
  obtain ⟨pair, hpair, rfl⟩ := hliteral
  obtain ⟨hordered, hright⟩ := upperPairs_sixteen_ordered pair hpair
  let left : Fin 16 := ⟨pair.1, by omega⟩
  let right : Fin 16 := ⟨pair.2, hright⟩
  apply (edgeUnit_satisfied_iff assignment
    (pair.1 + 8) (pair.2 + 8)
    (ternaryColoring (gen4416GraphIds.getD targetIndex 0)
      (edgeVar 16 pair.1 pair.2))).2
  calc
    assignment (edgeVar 24 (pair.1 + 8) (pair.2 + 8)) =
        coloringEdge 16 rawColoring
          (witness.permutation left).val
          (witness.permutation right).val := by
      simpa [left, right] using hassignment left right hordered
    _ = ternaryColoring (gen4416GraphIds.getD targetIndex 0)
          (edgeVar 16 pair.1 pair.2) := by
      simpa [left, right] using witness.fixed_edge left right hordered

end Gen4416DirectUnitWitness

#print axioms graphIsomorphicFin_to_gen4416DirectUnitWitness
#print axioms blueDegreeSixteen_gen4416DirectUnitWitness
#print axioms Gen4416DirectUnitWitness.allUnitsSatisfied

end LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge
