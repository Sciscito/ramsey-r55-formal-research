import LRATCatcher.Showcases.Ramsey
import LRATCatcher.Tests.R35CatalogCompleteness

/-!
  Semantic bridge from the d=20,c=10 Ramsey branch to the exhaustive
  R(3,5,10) catalogue.

  The SAT branch fixes a red root neighbourhood of size 20, chooses a red
  anchor in it, and labels the ten common red neighbours of the root and the
  anchor.  This file packages exactly that mathematical data.  In any
  K5/K5-free colouring, the induced graph on the ten common neighbours has
  no red triangle (otherwise root and anchor complete a red K5) and no blue
  K5.  Consequently it is covered by the certified order-ten catalogue.
-/

namespace LRATCatcher.Tests.R55

open LRATCatcher.Ramsey

open LRATCatcher.Tests.R35

/-- Symmetric, loop-free edge relation associated with the upper-triangle
Ramsey colouring. -/
def ramseyEdge (order : Nat) (coloring : Nat → Bool)
    (left right : Nat) : Bool :=
  if left < right then
    coloring (edgeVar order left right)
  else if right < left then
    coloring (edgeVar order right left)
  else
    false

@[simp] theorem ramseyEdge_self (order : Nat) (coloring : Nat → Bool)
    (vertex : Nat) :
    ramseyEdge order coloring vertex vertex = false := by
  simp [ramseyEdge]

theorem ramseyEdge_comm (order : Nat) (coloring : Nat → Bool)
    (left right : Nat) :
    ramseyEdge order coloring left right =
      ramseyEdge order coloring right left := by
  by_cases hleftRight : left < right
  · have hnotRightLeft : ¬ right < left := by omega
    simp [ramseyEdge, hleftRight, hnotRightLeft]
  · by_cases hrightLeft : right < left
    · simp [ramseyEdge, hleftRight, hrightLeft]
    · have hequal : left = right := by omega
      subst right
      simp

/-- The labelled mathematical data of a d=20,c=10 branch.

`typeGraph` is the packed adjacency matrix used by the R(3,5) catalogue;
`common` identifies its ten index vertices with the common red neighbours in
the ambient K43 colouring.  `common_complete` records that the codegree is
exactly ten, not merely at least ten. -/
structure DegreeTwentyCodegreeTenNeighborhood (coloring : Nat → Bool) where
  root : Nat
  anchor : Nat
  rootNeighbors : List Nat
  root_bound : root < 43
  anchor_bound : anchor < 43
  rootNeighbors_length : rootNeighbors.length = 20
  rootNeighbors_nodup : rootNeighbors.Nodup
  root_not_mem : root ∉ rootNeighbors
  anchor_mem : anchor ∈ rootNeighbors
  rootNeighbors_bound : ∀ vertex, vertex ∈ rootNeighbors → vertex < 43
  rootNeighbors_red : ∀ vertex, vertex ∈ rootNeighbors →
    ramseyEdge 43 coloring root vertex = true
  rootNeighbors_complete : ∀ vertex, vertex < 43 →
    ramseyEdge 43 coloring root vertex = true → vertex ∈ rootNeighbors
  common : Fin 10 → Nat
  common_injective : Function.Injective common
  common_bound : ∀ index, common index < 43
  common_mem : ∀ index, common index ∈ rootNeighbors
  anchor_common_red : ∀ index,
    ramseyEdge 43 coloring anchor (common index) = true
  common_complete : ∀ vertex, vertex ∈ rootNeighbors →
    ramseyEdge 43 coloring anchor vertex = true →
    ∃ index, common index = vertex
  root_ne_anchor : root ≠ anchor
  root_ne_common : ∀ index, root ≠ common index
  anchor_ne_common : ∀ index, anchor ≠ common index
  typeGraph : Graph
  type_wellFormed : wellFormedGraph 10 typeGraph = true
  type_edge : ∀ left right : Fin 10,
    edge typeGraph left.val right.val =
      ramseyEdge 43 coloring (common left) (common right)

namespace DegreeTwentyCodegreeTenNeighborhood

/-- Total version of the common-neighbour labelling.  Out-of-range index
indices are sent above the ambient K43 range, which makes this extension
globally injective. -/
def commonVertex {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    (index : Nat) : Nat :=
  if hindex : index < 10 then branch.common ⟨index, hindex⟩ else 43 + index

@[simp] theorem commonVertex_of_lt {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    {index : Nat} (hindex : index < 10) :
    branch.commonVertex index = branch.common ⟨index, hindex⟩ := by
  simp [commonVertex, hindex]

theorem commonVertex_bound {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    {index : Nat} (hindex : index < 10) :
    branch.commonVertex index < 43 := by
  rw [commonVertex_of_lt branch hindex]
  exact branch.common_bound _

theorem commonVertex_injective {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring) :
    Function.Injective branch.commonVertex := by
  intro left right hequal
  by_cases hleft : left < 10
  · by_cases hright : right < 10
    · simp only [commonVertex, dif_pos hleft, dif_pos hright] at hequal
      have hfin : branch.common ⟨left, hleft⟩ =
          branch.common ⟨right, hright⟩ := hequal
      exact congrArg Fin.val (branch.common_injective hfin)
    · simp only [commonVertex, dif_pos hleft, dif_neg hright] at hequal
      have hbound := branch.common_bound ⟨left, hleft⟩
      omega
  · by_cases hright : right < 10
    · simp only [commonVertex, dif_neg hleft, dif_pos hright] at hequal
      have hbound := branch.common_bound ⟨right, hright⟩
      omega
    · simp only [commonVertex, dif_neg hleft, dif_neg hright] at hequal
      omega

theorem allDistinctRelated_cons
    {relation : Nat → Nat → Bool} {head : Nat} {tail : List Nat}
    (hsymmetric : ∀ left right, relation left right = relation right left)
    (htail : AllDistinctRelated relation tail)
    (hhead : ∀ vertex, vertex ∈ tail → relation head vertex = true) :
    AllDistinctRelated relation (head :: tail) := by
  intro left hleft right hright hne
  simp only [List.mem_cons] at hleft hright
  rcases hleft with rfl | hleft
  · rcases hright with rfl | hright
    · exact absurd rfl hne
    · exact hhead right hright
  · rcases hright with rfl | hright
    · rw [hsymmetric left right]
      exact hhead left hleft
    · exact htail left hleft right hright hne

theorem mapped_nodup {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map branch.commonVertex).Nodup := by
  exact hnodup.map branch.commonVertex
    (fun left right hne hequal =>
      hne (branch.commonVertex_injective hequal))

theorem mapped_bound {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    {vertices : List Nat}
    (hbound : ∀ index, index ∈ vertices → index < 10) :
    ∀ vertex, vertex ∈ vertices.map branch.commonVertex → vertex < 43 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact branch.commonVertex_bound (hbound index hindex)

theorem mapped_red {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    {vertices : List Nat}
    (hbound : ∀ index, index ∈ vertices → index < 10)
    (hrelated : AllDistinctRelated (edge branch.typeGraph) vertices) :
    AllDistinctRelated (ramseyEdge 43 coloring)
      (vertices.map branch.commonVertex) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg branch.commonVertex hequal)
  calc
    ramseyEdge 43 coloring
        (branch.commonVertex indexLeft) (branch.commonVertex indexRight) =
        edge branch.typeGraph indexLeft indexRight := by
          rw [branch.commonVertex_of_lt hleftBound,
            branch.commonVertex_of_lt hrightBound]
          exact (branch.type_edge ⟨indexLeft, hleftBound⟩
            ⟨indexRight, hrightBound⟩).symm
    _ = true := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe

theorem mapped_blue {coloring : Nat → Bool}
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring)
    {vertices : List Nat}
    (hbound : ∀ index, index ∈ vertices → index < 10)
    (hrelated : AllDistinctRelated
      (fun left right => !(edge branch.typeGraph left right)) vertices) :
    AllDistinctRelated (fun left right => !(ramseyEdge 43 coloring left right))
      (vertices.map branch.commonVertex) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg branch.commonVertex hequal)
  have hedge := branch.type_edge ⟨indexLeft, hleftBound⟩
    ⟨indexRight, hrightBound⟩
  have hnotEdge := congrArg Bool.not hedge
  calc
    Bool.not (ramseyEdge 43 coloring
        (branch.commonVertex indexLeft) (branch.commonVertex indexRight)) =
        Bool.not (edge branch.typeGraph indexLeft indexRight) := by
          rw [branch.commonVertex_of_lt hleftBound,
            branch.commonVertex_of_lt hrightBound]
          exact hnotEdge.symm
    _ = true := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe

/-- The ten labelled common neighbours form an R(3,5,10) graph. -/
theorem typeGraph_semanticallyValid {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring) :
    SemanticallyValidGraph 10 branch.typeGraph := by
  constructor
  · intro triangle hlength hbound hnodup htriangle
    let mapped := triangle.map branch.commonVertex
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup branch hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 43 := by
      exact mapped_bound branch hbound
    have hmappedRed :
        AllDistinctRelated (ramseyEdge 43 coloring) mapped := by
      exact mapped_red branch hbound htriangle
    have hanchorNotMapped : branch.anchor ∉ mapped := by
      intro hmem
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
      have hindexBound := hbound index hindex
      have hembed : branch.common ⟨index, hindexBound⟩ = branch.anchor := by
        simpa [commonVertex, hindexBound] using hequal
      exact branch.anchor_ne_common ⟨index, hindexBound⟩ hembed.symm
    have hrootNotMapped : branch.root ∉ mapped := by
      intro hmem
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
      have hindexBound := hbound index hindex
      have hembed : branch.common ⟨index, hindexBound⟩ = branch.root := by
        simpa [commonVertex, hindexBound] using hequal
      exact branch.root_ne_common ⟨index, hindexBound⟩ hembed.symm
    let withAnchor := branch.anchor :: mapped
    let forbidden := branch.root :: withAnchor
    have hforbiddenLength : forbidden.length = 5 := by
      simp [forbidden, withAnchor, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < 43 := by
      intro vertex hvertex
      simp only [forbidden, withAnchor, List.mem_cons] at hvertex
      rcases hvertex with rfl | rfl | hvertex
      · exact branch.root_bound
      · exact branch.anchor_bound
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, withAnchor, List.nodup_cons]
      exact ⟨by simp [branch.root_ne_anchor, hrootNotMapped],
        ⟨hanchorNotMapped, hmappedNodup⟩⟩
    have hanchorRed :
        AllDistinctRelated (ramseyEdge 43 coloring) withAnchor := by
      apply allDistinctRelated_cons
      · exact ramseyEdge_comm 43 coloring
      · exact hmappedRed
      · intro vertex hvertex
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
        have hindexBound := hbound index hindex
        simpa [commonVertex, hindexBound] using
          branch.anchor_common_red ⟨index, hindexBound⟩
    have hforbiddenRed :
        AllDistinctRelated (ramseyEdge 43 coloring) forbidden := by
      apply allDistinctRelated_cons
      · exact ramseyEdge_comm 43 coloring
      · exact hanchorRed
      · intro vertex hvertex
        simp only [withAnchor, List.mem_cons] at hvertex
        rcases hvertex with rfl | hvertex
        · exact branch.rootNeighbors_red branch.anchor branch.anchor_mem
        · obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
          have hindexBound := hbound index hindex
          apply branch.rootNeighbors_red
          simpa [commonVertex, hindexBound] using
            branch.common_mem ⟨index, hindexBound⟩
    apply hfree.1 forbidden hforbiddenLength hforbiddenBound
      hforbiddenNodup
    intro left right hleft hright hlt
    have hred := hforbiddenRed left hleft right hright (Nat.ne_of_lt hlt)
    simpa [ramseyEdge, hlt] using hred
  · intro independent hlength hbound hnodup hindependent
    let mapped := independent.map branch.commonVertex
    have hmappedNodup : mapped.Nodup := mapped_nodup branch hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 43 :=
      mapped_bound branch hbound
    have hmappedBlue :
        AllDistinctRelated
          (fun left right => !(ramseyEdge 43 coloring left right)) mapped :=
      mapped_blue branch hbound hindependent
    apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound hmappedNodup
    intro left right hleft hright hlt
    have hblue := hmappedBlue left hleft right hright (Nat.ne_of_lt hlt)
    simpa [ramseyEdge, hlt] using hblue

theorem typeGraph_valid {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring) :
    validGraph branch.typeGraph = true :=
  semantic_validGraph branch.type_wellFormed
    (typeGraph_semanticallyValid hfree branch)

/-- Exact `GraphValidAt` premise consumed by catalogue completeness. -/
theorem typeGraph_validAt {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring) :
    GraphValidAt 10 branch.typeGraph :=
  ⟨branch.type_wellFormed, typeGraph_valid hfree branch⟩

/-- Catalogue coverage of every semantic d=20,c=10 branch. -/
theorem d20c10_type_covered_by_orderTenCatalogue
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (branch : DegreeTwentyCodegreeTenNeighborhood coloring) :
    ∃ representative,
      representative ∈ catalogues.getD 10 [] ∧
      GraphIsomorphicFin branch.typeGraph representative := by
  exact r35_catalogue_order_ten_complete branch.typeGraph
    (typeGraph_validAt hfree branch)

end DegreeTwentyCodegreeTenNeighborhood

end LRATCatcher.Tests.R55
