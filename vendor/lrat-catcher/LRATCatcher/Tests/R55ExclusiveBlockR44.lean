import LRATCatcher.Tests.R55DegreeBounds

/-!
  # The exclusive block between two centres is `R(4,4)`-free

  In an `R(5,5)`-free ambient colouring, take four distinct vertices which
  are all red-adjacent to a root and blue-adjacent to an anchor.  A red `K4`
  in the block would extend with the root to a red `K5`; a blue `K4` would
  extend with the anchor to a blue `K5`.

  The terminal theorem states the conclusion using the repository's standard
  `isRamseyFree 4 4 4` predicate, after pulling the ambient colouring back to
  the four labelled block vertices.  The red root--anchor edge belongs to the
  intended branch interface, although the exclusion argument is stronger and
  does not need that edge.
-/

namespace LRATCatcher.Tests.R55ExclusiveBlockR44

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55DegreeBounds

abbrev BlockVertex := Fin 4

/-! ## Pulling an ambient colouring back to four vertices -/

/-- The six upper-triangle pairs in the row-major order of `edgeVar 4`. -/
def blockEdgePairs : List (BlockVertex × BlockVertex) :=
  (List.finRange 4).flatMap fun left =>
    (List.finRange 4).filterMap fun right =>
      if left < right then some (left, right) else none

/-- Total decoder for local edge-variable indices. -/
def blockEdgePair (index : Nat) : BlockVertex × BlockVertex :=
  blockEdgePairs.getD index (0, 0)

/-- Round trip on the six genuine edge variables of `K4`. -/
theorem blockEdgePair_edgeVar (left right : BlockVertex)
    (hordered : left < right) :
    blockEdgePair (edgeVar 4 left.val right.val) = (left, right) := by
  native_decide +revert

/-- The colouring induced on four labelled ambient vertices. -/
def inducedBlockColoring {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool) (index : Nat) : Bool :=
  let endpoints := blockEdgePair index
  ramseyEdge order coloring
    (embedding endpoints.1).val (embedding endpoints.2).val

theorem inducedBlockColoring_edgeVar {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool)
    (left right : BlockVertex) (hordered : left < right) :
    inducedBlockColoring embedding coloring
        (edgeVar 4 left.val right.val) =
      ramseyEdge order coloring
        (embedding left).val (embedding right).val := by
  simp [inducedBlockColoring,
    blockEdgePair_edgeVar left right hordered]

/-- Extend the finite embedding to an injective map on naturals. -/
def embedNat {order : Nat} (embedding : BlockVertex → Fin order)
    (vertex : Nat) : Nat :=
  if hvertex : vertex < 4 then
    (embedding ⟨vertex, hvertex⟩).val
  else
    order + vertex

@[simp] theorem embedNat_of_lt {order : Nat}
    (embedding : BlockVertex → Fin order)
    {vertex : Nat} (hvertex : vertex < 4) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound {order : Nat}
    (embedding : BlockVertex → Fin order)
    {vertex : Nat} (hvertex : vertex < 4) :
    embedNat embedding vertex < order := by
  rw [embedNat_of_lt embedding hvertex]
  exact (embedding ⟨vertex, hvertex⟩).isLt

theorem embedNat_injective {order : Nat}
    (embedding : BlockVertex → Fin order)
    (hinjective : Function.Injective embedding) :
    Function.Injective (embedNat embedding) := by
  intro left right hequal
  by_cases hleft : left < 4
  · by_cases hright : right < 4
    · have hfin : embedding ⟨left, hleft⟩ = embedding ⟨right, hright⟩ := by
        apply Fin.ext
        simpa [embedNat, hleft, hright] using hequal
      exact congrArg Fin.val (hinjective hfin)
    · have hleftBound := embedNat_bound embedding hleft
      have hrightValue : embedNat embedding right = order + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < 4
    · have hleftValue : embedNat embedding left = order + left := by
        simp [embedNat, hleft]
      have hrightBound := embedNat_bound embedding hright
      omega
    · simpa [embedNat, hleft, hright] using hequal

theorem mapped_nodup {order : Nat}
    (embedding : BlockVertex → Fin order)
    (hinjective : Function.Injective embedding)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map (embedNat embedding)).Nodup := by
  exact hnodup.map (embedNat embedding)
    (fun left right hne hequal =>
      hne (embedNat_injective embedding hinjective hequal))

theorem mapped_bound {order : Nat}
    (embedding : BlockVertex → Fin order)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 4) :
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < order := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem ramseyEdge_inducedBlockColoring {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool)
    (left right : BlockVertex) (hne : left ≠ right) :
    ramseyEdge 4 (inducedBlockColoring embedding coloring)
        left.val right.val =
      ramseyEdge order coloring
        (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      inducedBlockColoring_edgeVar embedding coloring left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm 4 (inducedBlockColoring embedding coloring)]
    rw [ramseyEdge_comm order coloring]
    simpa [ramseyEdge, hreverse] using
      inducedBlockColoring_edgeVar embedding coloring right left hreverseFin

theorem local_red_related {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hall : ∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      inducedBlockColoring embedding coloring (edgeVar 4 left right) = true) :
    AllDistinctRelated
      (ramseyEdge 4 (inducedBlockColoring embedding coloring)) vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem local_blue_related {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hall : ∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      inducedBlockColoring embedding coloring (edgeVar 4 left right) = false) :
    AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 4 (inducedBlockColoring embedding coloring) left right))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge 4 (inducedBlockColoring embedding coloring)
        left right) = true
    rw [ramseyEdge_comm 4 (inducedBlockColoring embedding coloring)]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem mapped_red_related {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 4)
    (hrelated : AllDistinctRelated
      (ramseyEdge 4 (inducedBlockColoring embedding coloring)) vertices) :
    AllDistinctRelated (ramseyEdge order coloring)
      (vertices.map (embedNat embedding)) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg (embedNat embedding) hequal)
  have hlocal := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe
  have hedge := ramseyEdge_inducedBlockColoring embedding coloring
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  rw [hedge] at hlocal
  exact hlocal

theorem mapped_blue_related {order : Nat}
    (embedding : BlockVertex → Fin order)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 4)
    (hrelated : AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 4 (inducedBlockColoring embedding coloring) left right))
      vertices) :
    AllDistinctRelated (fun left right => !(ramseyEdge order coloring left right))
      (vertices.map (embedNat embedding)) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg (embedNat embedding) hequal)
  have hlocal := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe
  have hedge := ramseyEdge_inducedBlockColoring embedding coloring
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  change Bool.not
    (ramseyEdge 4 (inducedBlockColoring embedding coloring)
      indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  exact hlocal

/-! ## The exclusive-block lemma -/

/-- Strong form: the colours from the two centres to the block already force
the induced block to be `R(4,4)`-free. -/
theorem exclusiveBlock_isRamseyFree {order : Nat}
    {coloring : Nat → Bool}
    (hfree : isRamseyFree order 5 5 coloring)
    (root anchor : Fin order)
    (embedding : BlockVertex → Fin order)
    (hinjective : Function.Injective embedding)
    (hrootNe : ∀ index, root ≠ embedding index)
    (hanchorNe : ∀ index, anchor ≠ embedding index)
    (hrootRed : ∀ index,
      ramseyEdge order coloring root.val (embedding index).val = true)
    (hanchorBlue : ∀ index,
      ramseyEdge order coloring anchor.val (embedding index).val = false) :
    isRamseyFree 4 4 4 (inducedBlockColoring embedding coloring) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := root.val :: mapped
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < order :=
      mapped_bound embedding hbound
    have hrootNotMapped : root.val ∉ mapped := by
      intro hmember
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmember
      have hindexBound := hbound index hindex
      have hequal' : root = embedding ⟨index, hindexBound⟩ := by
        apply Fin.ext
        simpa [embedNat, hindexBound] using hequal.symm
      exact hrootNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 5 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < order := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact root.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp [forbidden, hrootNotMapped, hmappedNodup]
    have hmappedRed :
        AllDistinctRelated (ramseyEdge order coloring) mapped := by
      exact mapped_red_related embedding coloring hbound
        (local_red_related embedding coloring hall)
    have hforbiddenRed :
        AllDistinctRelated (ramseyEdge order coloring) forbidden := by
      apply allDistinctRelated_cons
      · exact ramseyEdge_comm order coloring
      · exact hmappedRed
      · intro vertex hvertex
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
        have hindexBound := hbound index hindex
        simpa [embedNat, hindexBound] using
          hrootRed ⟨index, hindexBound⟩
    apply hfree.1 forbidden hforbiddenLength hforbiddenBound
      hforbiddenNodup
    intro left right hleft hright hlt
    have hred := hforbiddenRed left hleft right hright (Nat.ne_of_lt hlt)
    simpa [ramseyEdge, hlt] using hred
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := anchor.val :: mapped
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < order :=
      mapped_bound embedding hbound
    have hanchorNotMapped : anchor.val ∉ mapped := by
      intro hmember
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmember
      have hindexBound := hbound index hindex
      have hequal' : anchor = embedding ⟨index, hindexBound⟩ := by
        apply Fin.ext
        simpa [embedNat, hindexBound] using hequal.symm
      exact hanchorNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 5 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < order := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact anchor.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp [forbidden, hanchorNotMapped, hmappedNodup]
    have hmappedBlue :
        AllDistinctRelated
          (fun left right => !(ramseyEdge order coloring left right)) mapped := by
      exact mapped_blue_related embedding coloring hbound
        (local_blue_related embedding coloring hall)
    have hforbiddenBlue :
        AllDistinctRelated
          (fun left right => !(ramseyEdge order coloring left right))
          forbidden := by
      apply allDistinctRelated_cons
      · intro left right
        rw [ramseyEdge_comm order coloring]
      · exact hmappedBlue
      · intro vertex hvertex
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
        have hindexBound := hbound index hindex
        have hedge := hanchorBlue ⟨index, hindexBound⟩
        simp [embedNat, hindexBound, hedge]
    apply hfree.2 forbidden hforbiddenLength hforbiddenBound
      hforbiddenNodup
    intro left right hleft hright hlt
    have hblue := hforbiddenBlue left hleft right hright (Nat.ne_of_lt hlt)
    simpa [ramseyEdge, hlt] using hblue

/-- Requested branch-facing form.  The red edge between the root and anchor
is recorded explicitly; the stronger theorem above shows it is not needed
for the `R(4,4)` conclusion. -/
theorem redEdge_exclusiveBlock_isRamseyFree {order : Nat}
    {coloring : Nat → Bool}
    (hfree : isRamseyFree order 5 5 coloring)
    (root anchor : Fin order)
    (embedding : BlockVertex → Fin order)
    (hinjective : Function.Injective embedding)
    (_hrootAnchorRed :
      ramseyEdge order coloring root.val anchor.val = true)
    (hrootNe : ∀ index, root ≠ embedding index)
    (hanchorNe : ∀ index, anchor ≠ embedding index)
    (hrootRed : ∀ index,
      ramseyEdge order coloring root.val (embedding index).val = true)
    (hanchorBlue : ∀ index,
      ramseyEdge order coloring anchor.val (embedding index).val = false) :
    isRamseyFree 4 4 4 (inducedBlockColoring embedding coloring) :=
  exclusiveBlock_isRamseyFree hfree root anchor embedding hinjective
    hrootNe hanchorNe hrootRed hanchorBlue

#print axioms exclusiveBlock_isRamseyFree
#print axioms redEdge_exclusiveBlock_isRamseyFree

end LRATCatcher.Tests.R55ExclusiveBlockR44
