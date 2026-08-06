import LRATCatcher.Tests.R55CanonicalUnitsBridge

/-!
  Identification of the local order-ten common-neighbour indices with the
  ambient vertices fixed by the canonical `d = 20, c = 10` unit clauses.
-/

namespace LRATCatcher.Tests.R55

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open DegreeTwentyCodegreeTenNeighborhood.ExactLists

namespace CanonicalUnits

/-- In the canonical unit branch, local common-neighbour index `i` is exactly
ambient vertex `i + 2`. -/
@[simp] theorem CanonicalD20C10Units.common_eq_add_two
    {coloring : Nat → Bool}
    (units : CanonicalD20C10Units coloring) (index : Fin 10) :
    common units.toLocalWitness.toExactLists index = index.val + 2 := by
  unfold common LocalD20C10Witness.toExactLists
    CanonicalD20C10Units.toLocalWitness LocalD20C10Witness.ofCanonicalBranch
  change
    (rootAnchorCommonNeighbors coloring 0 1)[index.val]'(by
      rw [rootAnchorCommonNeighbors_eq_range units]
      simp) = index.val + 2
  simp only [rootAnchorCommonNeighbors_eq_range units]
  simp
  omega

/-- Consequently, every local bit of the packed order-ten graph is the
corresponding ambient Ramsey edge on vertices `2, ..., 11`. -/
@[simp] theorem CanonicalD20C10Units.edge_inducedGraph_eq_global
    {coloring : Nat → Bool}
    (units : CanonicalD20C10Units coloring) (left right : Fin 10) :
    edge (inducedGraph units.toLocalWitness.toExactLists) left.val right.val =
      ramseyEdge 43 coloring (left.val + 2) (right.val + 2) := by
  rw [edge_inducedGraph,
    units.common_eq_add_two left, units.common_eq_add_two right]

end CanonicalUnits

end LRATCatcher.Tests.R55
