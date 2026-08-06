import LRATCatcher.Tests.R55DegreeBounds

/-!
  # The Ramsey recurrence at `R(4,4)`

  This module formalizes the classical step

      `R(4,4) ≤ R(3,4) + R(4,3) ≤ 9 + 9 = 18`.

  Complementation identifies the two small bounds, so the only hypothesis is
  `¬ hasRamseyFreeColoring 9 3 4`.
-/

namespace LRATCatcher.Tests.RamseyRecurrence

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55DegreeBounds

abbrev LocalVertex := Fin 9
abbrev AmbientVertex := Fin 18

/-- Upper-triangle pairs in the row-major order used by `edgeVar 9`. -/
def localEdgePairs : List (LocalVertex × LocalVertex) :=
  (List.finRange 9).flatMap fun left =>
    (List.finRange 9).filterMap fun right =>
      if left < right then some (left, right) else none

def localEdgePair (index : Nat) : LocalVertex × LocalVertex :=
  localEdgePairs.getD index (0, 0)

theorem localEdgePair_edgeVar (left right : LocalVertex)
    (hordered : left < right) :
    localEdgePair (edgeVar 9 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Pull back an ambient coloring along nine embedded vertices, complementing
it when `flip = true`. -/
def inducedColoring (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool) (index : Nat) : Bool :=
  let endpoints := localEdgePair index
  let ambient := ramseyEdge 18 coloring
    (embedding endpoints.1).val (embedding endpoints.2).val
  if flip then !ambient else ambient

theorem inducedColoring_edgeVar
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (left right : LocalVertex) (hordered : left < right) :
    inducedColoring embedding coloring flip (edgeVar 9 left.val right.val) =
      if flip then
        !(ramseyEdge 18 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 18 coloring (embedding left).val (embedding right).val := by
  simp [inducedColoring, localEdgePair_edgeVar left right hordered]

def embedNat (embedding : LocalVertex → AmbientVertex) (vertex : Nat) : Nat :=
  if hvertex : vertex < 9 then
    (embedding ⟨vertex, hvertex⟩).val
  else
    18 + vertex

@[simp] theorem embedNat_of_lt (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 9) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 9) :
    embedNat embedding vertex < 18 := by
  rw [embedNat_of_lt embedding hvertex]
  exact (embedding ⟨vertex, hvertex⟩).isLt

theorem embedNat_injective (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding) :
    Function.Injective (embedNat embedding) := by
  intro left right hequal
  by_cases hleft : left < 9
  · by_cases hright : right < 9
    · have hfin : embedding ⟨left, hleft⟩ = embedding ⟨right, hright⟩ := by
        apply Fin.ext
        simpa [embedNat, hleft, hright] using hequal
      exact congrArg Fin.val (hinjective hfin)
    · have hleftBound := embedNat_bound embedding hleft
      have hrightValue : embedNat embedding right = 18 + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < 9
    · have hleftValue : embedNat embedding left = 18 + left := by
        simp [embedNat, hleft]
      have hrightBound := embedNat_bound embedding hright
      omega
    · simpa [embedNat, hleft, hright] using hequal

theorem mapped_nodup (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map (embedNat embedding)).Nodup := by
  exact hnodup.map (embedNat embedding)
    (fun left right hne hequal =>
      hne (embedNat_injective embedding hinjective hequal))

theorem mapped_bound (embedding : LocalVertex → AmbientVertex)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9) :
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < 18 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem ramseyEdge_inducedColoring
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (left right : LocalVertex) (hne : left ≠ right) :
    ramseyEdge 9 (inducedColoring embedding coloring flip)
        left.val right.val =
      if flip then
        !(ramseyEdge 18 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 18 coloring (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      inducedColoring_edgeVar embedding coloring flip left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm 9 (inducedColoring embedding coloring flip)]
    rw [ramseyEdge_comm 18 coloring]
    simpa [ramseyEdge, hreverse] using
      inducedColoring_edgeVar embedding coloring flip right left hreverseFin

theorem local_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (_hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hall : ∀ i j, i ∈ vertices → j ∈ vertices → i < j →
      inducedColoring embedding coloring flip (edgeVar 9 i j) = true) :
    AllDistinctRelated
      (ramseyEdge 9 (inducedColoring embedding coloring flip)) vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem local_false_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (_hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hall : ∀ i j, i ∈ vertices → j ∈ vertices → i < j →
      inducedColoring embedding coloring flip (edgeVar 9 i j) = false) :
    AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 9 (inducedColoring embedding coloring flip) left right))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge 9 (inducedColoring embedding coloring flip) left right) = true
    rw [ramseyEdge_comm 9 (inducedColoring embedding coloring flip)]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem mapped_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hrelated : AllDistinctRelated
      (ramseyEdge 9 (inducedColoring embedding coloring flip)) vertices) :
    AllDistinctRelated
      (fun left right =>
        if flip then !(ramseyEdge 18 coloring left right)
        else ramseyEdge 18 coloring left right)
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
  have hedge := ramseyEdge_inducedColoring embedding coloring flip
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  rw [hedge] at hlocal
  simpa using hlocal

theorem mapped_false_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hrelated : AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 9 (inducedColoring embedding coloring flip) left right))
      vertices) :
    AllDistinctRelated
      (fun left right =>
        !(if flip then !(ramseyEdge 18 coloring left right)
          else ramseyEdge 18 coloring left right))
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
  have hedge := ramseyEdge_inducedColoring embedding coloring flip
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  change Bool.not (ramseyEdge 9 (inducedColoring embedding coloring flip)
    indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  simpa using hlocal

/-- Nine red neighbours inherit a `(3,4)`-free coloring.  Nine blue
neighbours inherit one after complementation. -/
theorem induced_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 18 4 4 coloring)
    (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (root : AmbientVertex) (flip : Bool)
    (hrootNe : ∀ index, root.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 18 coloring root.val (embedding index).val = !flip) :
    isRamseyFree 9 3 4 (inducedColoring embedding coloring flip) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := root.val :: mapped
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 18 := by
      exact mapped_bound embedding hbound
    have hrootNotMapped : root.val ∉ mapped := by
      intro hmem
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
      have hindexBound := hbound index hindex
      have hequal' : root.val = (embedding ⟨index, hindexBound⟩).val := by
        simpa [embedNat, hindexBound] using hequal.symm
      exact hrootNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 4 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < 18 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact root.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring flip hbound hall
    have hmapped := mapped_true_related embedding coloring flip hbound hlocal
    cases flip with
    | false =>
        have hmappedRed :
            AllDistinctRelated (ramseyEdge 18 coloring) mapped := by
          simpa using hmapped
        have hforbiddenRed :
            AllDistinctRelated (ramseyEdge 18 coloring) forbidden := by
          apply allDistinctRelated_cons
          · exact ramseyEdge_comm 18 coloring
          · exact hmappedRed
          · intro vertex hvertex
            obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
            have hindexBound := hbound index hindex
            rw [embedNat_of_lt embedding hindexBound]
            simpa using hneighbour ⟨index, hindexBound⟩
        apply hfree.1 forbidden hforbiddenLength hforbiddenBound
          hforbiddenNodup
        intro left right hleft hright hordered
        have hedge := hforbiddenRed left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge
    | true =>
        have hmappedBlue :
            AllDistinctRelated
              (fun left right => !(ramseyEdge 18 coloring left right))
              mapped := by
          simpa using hmapped
        have hforbiddenBlue :
            AllDistinctRelated
              (fun left right => !(ramseyEdge 18 coloring left right))
              forbidden := by
          apply allDistinctRelated_cons
          · intro left right
            rw [ramseyEdge_comm 18 coloring left right]
          · exact hmappedBlue
          · intro vertex hvertex
            obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
            have hindexBound := hbound index hindex
            rw [embedNat_of_lt embedding hindexBound]
            have hedge := hneighbour ⟨index, hindexBound⟩
            simp at hedge ⊢
            exact hedge
        apply hfree.2 forbidden hforbiddenLength hforbiddenBound
          hforbiddenNodup
        intro left right hleft hright hordered
        have hedge := hforbiddenBlue left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 18 := by
      exact mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring flip hbound hall
    have hmapped := mapped_false_related embedding coloring flip hbound hlocal
    cases flip with
    | false =>
        have hmappedBlue :
            AllDistinctRelated
              (fun left right => !(ramseyEdge 18 coloring left right))
              mapped := by
          simpa using hmapped
        apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound
          hmappedNodup
        intro left right hleft hright hordered
        have hedge := hmappedBlue left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge
    | true =>
        have hmappedRed :
            AllDistinctRelated (ramseyEdge 18 coloring) mapped := by
          simpa using hmapped
        apply hfree.1 mapped (by simp [mapped, hlength]) hmappedBound
          hmappedNodup
        intro left right hleft hright hordered
        have hedge := hmappedRed left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge

/-! ## The 17 edges at a root -/

/-- The other vertices of `K₁₈`, with the requested root-edge colour.
`flip = false` selects red neighbours; `flip = true` selects blue and
normalizes them by complementation. -/
def rootNeighbors (coloring : Nat → Bool) (flip : Bool) : List Nat :=
  (List.range' 1 17).filter fun vertex =>
    if flip then !(ramseyEdge 18 coloring 0 vertex)
    else ramseyEdge 18 coloring 0 vertex

@[simp] theorem mem_rootNeighbors (coloring : Nat → Bool)
    (flip : Bool) (vertex : Nat) :
    vertex ∈ rootNeighbors coloring flip ↔
      1 ≤ vertex ∧ vertex < 18 ∧
        ramseyEdge 18 coloring 0 vertex = !flip := by
  cases flip <;> simp [rootNeighbors, List.mem_range'_1, and_assoc]

theorem rootNeighbors_nodup (coloring : Nat → Bool) (flip : Bool) :
    (rootNeighbors coloring flip).Nodup := by
  exact (List.nodup_range' (s := 1) (n := 17)).filter _

theorem filter_bool_partition_length (vertices : List Nat)
    (predicate : Nat → Bool) :
    (vertices.filter predicate).length +
      (vertices.filter fun vertex => !(predicate vertex)).length =
        vertices.length := by
  induction vertices with
  | nil => simp
  | cons head tail ih =>
      cases hhead : predicate head <;> simp [hhead] <;> omega

theorem rootNeighbors_length_sum (coloring : Nat → Bool) :
    (rootNeighbors coloring false).length +
      (rootNeighbors coloring true).length = 17 := by
  simpa [rootNeighbors] using
    filter_bool_partition_length (List.range' 1 17)
      (fun vertex => ramseyEdge 18 coloring 0 vertex)

/-- Pigeonhole step in the recurrence: among 17 root edges, one colour
occurs at least nine times. -/
theorem nine_root_neighbors (coloring : Nat → Bool) :
    9 ≤ (rootNeighbors coloring false).length ∨
      9 ≤ (rootNeighbors coloring true).length := by
  have hsum := rootNeighbors_length_sum coloring
  omega

def chosenRootNeighbor (coloring : Nat → Bool) (flip : Bool)
    (hlength : 9 ≤ (rootNeighbors coloring flip).length)
    (index : LocalVertex) : Nat :=
  (rootNeighbors coloring flip)[index.val]'(by
    exact Nat.lt_of_lt_of_le index.isLt hlength)

theorem chosenRootNeighbor_mem (coloring : Nat → Bool) (flip : Bool)
    (hlength : 9 ≤ (rootNeighbors coloring flip).length)
    (index : LocalVertex) :
    chosenRootNeighbor coloring flip hlength index ∈
      rootNeighbors coloring flip := by
  exact List.getElem_mem _

def neighborEmbedding (coloring : Nat → Bool) (flip : Bool)
    (hlength : 9 ≤ (rootNeighbors coloring flip).length) :
    LocalVertex → AmbientVertex := fun index =>
  ⟨chosenRootNeighbor coloring flip hlength index,
    (mem_rootNeighbors coloring flip
      (chosenRootNeighbor coloring flip hlength index)).mp
        (chosenRootNeighbor_mem coloring flip hlength index) |>.2.1⟩

theorem neighborEmbedding_injective (coloring : Nat → Bool) (flip : Bool)
    (hlength : 9 ≤ (rootNeighbors coloring flip).length) :
    Function.Injective (neighborEmbedding coloring flip hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj (rootNeighbors_nodup coloring flip)).mp hvalues

theorem neighborEmbedding_ne_root (coloring : Nat → Bool) (flip : Bool)
    (hlength : 9 ≤ (rootNeighbors coloring flip).length)
    (index : LocalVertex) :
    0 ≠ (neighborEmbedding coloring flip hlength index).val := by
  have hmem := chosenRootNeighbor_mem coloring flip hlength index
  have hpositive := (mem_rootNeighbors coloring flip
    (chosenRootNeighbor coloring flip hlength index)).mp hmem |>.1
  change 0 ≠ chosenRootNeighbor coloring flip hlength index
  omega

theorem neighborEmbedding_color (coloring : Nat → Bool) (flip : Bool)
    (hlength : 9 ≤ (rootNeighbors coloring flip).length)
    (index : LocalVertex) :
    ramseyEdge 18 coloring 0
      (neighborEmbedding coloring flip hlength index).val = !flip := by
  have hmem := chosenRootNeighbor_mem coloring flip hlength index
  exact (mem_rootNeighbors coloring flip
    (chosenRootNeighbor coloring flip hlength index)).mp hmem |>.2.2

theorem contradiction_of_nine_root_neighbors
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 18 4 4 coloring)
    (hR34 : ¬ hasRamseyFreeColoring 9 3 4)
    (flip : Bool) (hlength : 9 ≤ (rootNeighbors coloring flip).length) :
    False := by
  let embedding := neighborEmbedding coloring flip hlength
  have hinjective : Function.Injective embedding := by
    exact neighborEmbedding_injective coloring flip hlength
  have hrootNe : ∀ index, 0 ≠ (embedding index).val := by
    exact neighborEmbedding_ne_root coloring flip hlength
  have hneighbour : ∀ index,
      ramseyEdge 18 coloring 0 (embedding index).val = !flip := by
    exact neighborEmbedding_color coloring flip hlength
  apply hR34
  exact ⟨inducedColoring embedding coloring flip,
    induced_isRamseyFree hfree embedding hinjective ⟨0, by omega⟩ flip
      hrootNe hneighbour⟩

/-- Specialized, kernel-checked Ramsey recurrence
`R(4,4) ≤ R(3,4) + R(4,3) ≤ 18`. -/
theorem r44_upper_of_r34_upper
    (hR34 : ¬ hasRamseyFreeColoring 9 3 4) :
    ¬ hasRamseyFreeColoring 18 4 4 := by
  intro hcounterexample
  obtain ⟨coloring, hfree⟩ := hcounterexample
  rcases nine_root_neighbors coloring with hred | hblue
  · exact contradiction_of_nine_root_neighbors hfree hR34 false hred
  · exact contradiction_of_nine_root_neighbors hfree hR34 true hblue

#print axioms r44_upper_of_r34_upper

end LRATCatcher.Tests.RamseyRecurrence
