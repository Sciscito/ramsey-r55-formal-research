import LRATCatcher.Tests.RamseyRecurrence

/-!
  # Degree reduction in a hypothetical `(4,5)`-free coloring of `K_25`

  Two external Ramsey upper bounds suffice to force a narrow degree window:

  * `R(3,5) ≤ 14` rules out fourteen red neighbours, so every red degree is
    at most thirteen;
  * `R(4,4) ≤ 18` rules out eighteen blue neighbours, so every blue degree is
    at most seventeen and every red degree is at least seven.

  The proof is semantic.  It restricts the coloring to a same-colour
  neighbourhood and explicitly transports forbidden cliques back to `K_25`.
-/

namespace LRATCatcher.Tests.R45DegreeReduction

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55DegreeBounds

abbrev AmbientVertex := Fin 25

/-! ## Generic finite restriction machinery -/

/-- Upper-triangle pairs in the row-major order used by `edgeVar`. -/
def localEdgePairs (order : Nat) : List (Fin order × Fin order) :=
  (List.finRange order).flatMap fun left =>
    (List.finRange order).filterMap fun right =>
      if left < right then some (left, right) else none

/-- Total decoder for local edge-variable indices. -/
def localEdgePair (order index : Nat) [NeZero order] : Fin order × Fin order :=
  (localEdgePairs order).getD index (0, 0)

/-- The finite decoder has the expected row-major round trip at order 14. -/
theorem localEdgePair_edgeVar_fourteen (left right : Fin 14)
    (hordered : left < right) :
    localEdgePair 14 (edgeVar 14 left.val right.val) = (left, right) := by
  native_decide +revert

/-- The finite decoder has the expected row-major round trip at order 18. -/
theorem localEdgePair_edgeVar_eighteen (left right : Fin 18)
    (hordered : left < right) :
    localEdgePair 18 (edgeVar 18 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Restrict an ambient coloring to an embedded local complete graph; when
`flip` is true, complement every local edge. -/
def inducedColoring (order : Nat) [NeZero order]
    (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool) (index : Nat) : Bool :=
  let endpoints := localEdgePair order index
  let ambient := ramseyEdge 25 coloring
    (embedding endpoints.1).val (embedding endpoints.2).val
  if flip then !ambient else ambient

theorem inducedColoring_edgeVar
    {order : Nat} [NeZero order] (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (left right : Fin order) (hordered : left < right) :
    inducedColoring order embedding coloring flip
        (edgeVar order left.val right.val) =
      if flip then
        !(ramseyEdge 25 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 25 coloring (embedding left).val (embedding right).val := by
  simp [inducedColoring, hdecoder left right hordered]

/-- Extend a finite embedding to naturals.  The out-of-range branch makes the
extension globally injective; semantic clique vertices all use the first
branch. -/
def embedNat {order : Nat} (embedding : Fin order → AmbientVertex)
    (vertex : Nat) : Nat :=
  if hvertex : vertex < order then
    (embedding ⟨vertex, hvertex⟩).val
  else
    25 + vertex

@[simp] theorem embedNat_of_lt {order : Nat}
    (embedding : Fin order → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < order) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound {order : Nat}
    (embedding : Fin order → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < order) :
    embedNat embedding vertex < 25 := by
  rw [embedNat_of_lt embedding hvertex]
  exact (embedding ⟨vertex, hvertex⟩).isLt

theorem embedNat_injective {order : Nat}
    (embedding : Fin order → AmbientVertex)
    (hinjective : Function.Injective embedding) :
    Function.Injective (embedNat embedding) := by
  intro left right hequal
  by_cases hleft : left < order
  · by_cases hright : right < order
    · have hfin : embedding ⟨left, hleft⟩ = embedding ⟨right, hright⟩ := by
        apply Fin.ext
        simpa [embedNat, hleft, hright] using hequal
      exact congrArg Fin.val (hinjective hfin)
    · have hleftBound := embedNat_bound embedding hleft
      have hrightValue : embedNat embedding right = 25 + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < order
    · have hleftValue : embedNat embedding left = 25 + left := by
        simp [embedNat, hleft]
      have hrightBound := embedNat_bound embedding hright
      omega
    · simpa [embedNat, hleft, hright] using hequal

theorem mapped_nodup {order : Nat}
    (embedding : Fin order → AmbientVertex)
    (hinjective : Function.Injective embedding)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map (embedNat embedding)).Nodup := by
  exact hnodup.map (embedNat embedding)
    (fun left right hne hequal =>
      hne (embedNat_injective embedding hinjective hequal))

theorem mapped_bound {order : Nat}
    (embedding : Fin order → AmbientVertex)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < order) :
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < 25 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem ramseyEdge_inducedColoring
    {order : Nat} [NeZero order] (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (left right : Fin order) (hne : left ≠ right) :
    ramseyEdge order (inducedColoring order embedding coloring flip)
        left.val right.val =
      if flip then
        !(ramseyEdge 25 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 25 coloring (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      inducedColoring_edgeVar embedding coloring flip hdecoder
        left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm order
      (inducedColoring order embedding coloring flip)]
    rw [ramseyEdge_comm 25 coloring]
    simpa [ramseyEdge, hreverse] using
      inducedColoring_edgeVar embedding coloring flip hdecoder
        right left hreverseFin

theorem local_true_related
    {order : Nat} [NeZero order] (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (hall : ∀ i j, i ∈ vertices → j ∈ vertices → i < j →
      inducedColoring order embedding coloring flip
        (edgeVar order i j) = true) :
    AllDistinctRelated
      (ramseyEdge order (inducedColoring order embedding coloring flip))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem local_false_related
    {order : Nat} [NeZero order] (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (hall : ∀ i j, i ∈ vertices → j ∈ vertices → i < j →
      inducedColoring order embedding coloring flip
        (edgeVar order i j) = false) :
    AllDistinctRelated
      (fun left right =>
        !(ramseyEdge order
          (inducedColoring order embedding coloring flip) left right))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge order (inducedColoring order embedding coloring flip)
        left right) = true
    rw [ramseyEdge_comm]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem mapped_true_related
    {order : Nat} [NeZero order] (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < order)
    (hrelated : AllDistinctRelated
      (ramseyEdge order (inducedColoring order embedding coloring flip))
      vertices) :
    AllDistinctRelated
      (fun left right =>
        if flip then !(ramseyEdge 25 coloring left right)
        else ramseyEdge 25 coloring left right)
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
  have hedge := ramseyEdge_inducedColoring embedding coloring flip hdecoder
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  rw [hedge] at hlocal
  simpa using hlocal

theorem mapped_false_related
    {order : Nat} [NeZero order] (embedding : Fin order → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < order)
    (hrelated : AllDistinctRelated
      (fun left right =>
        !(ramseyEdge order
          (inducedColoring order embedding coloring flip) left right))
      vertices) :
    AllDistinctRelated
      (fun left right =>
        !(if flip then !(ramseyEdge 25 coloring left right)
          else ramseyEdge 25 coloring left right))
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
  have hedge := ramseyEdge_inducedColoring embedding coloring flip hdecoder
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  change Bool.not
    (ramseyEdge order (inducedColoring order embedding coloring flip)
      indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  simpa using hlocal

/-! ## The two neighbourhood restrictions used by the degree argument -/

/-- Any injectively embedded red neighbourhood inherits a `(3,5)`-free
coloring, once the finite local edge decoder is known to round-trip. -/
theorem red_induced_isRamseyFree_of_decoder
    {order : Nat} [NeZero order]
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (embedding : Fin order → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (root : AmbientVertex)
    (hrootNe : ∀ index, root.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 25 coloring root.val (embedding index).val = true) :
    isRamseyFree order 3 5
      (inducedColoring order embedding coloring false) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := root.val :: mapped
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 25 := by
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
        ∀ vertex, vertex ∈ forbidden → vertex < 25 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact root.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring false hall
    have hmapped := mapped_true_related embedding coloring false
      hdecoder hbound hlocal
    have hmappedRed :
        AllDistinctRelated (ramseyEdge 25 coloring) mapped := by
      simpa using hmapped
    have hforbiddenRed :
        AllDistinctRelated (ramseyEdge 25 coloring) forbidden := by
      apply allDistinctRelated_cons
      · exact ramseyEdge_comm 25 coloring
      · exact hmappedRed
      · intro vertex hvertex
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
        have hindexBound := hbound index hindex
        rw [embedNat_of_lt embedding hindexBound]
        exact hneighbour ⟨index, hindexBound⟩
    apply hfree.1 forbidden hforbiddenLength hforbiddenBound
      hforbiddenNodup
    intro left right hleft hright hordered
    have hedge := hforbiddenRed left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 25 := by
      exact mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring false hall
    have hmapped := mapped_false_related embedding coloring false
      hdecoder hbound hlocal
    have hmappedBlue :
        AllDistinctRelated
          (fun left right => !(ramseyEdge 25 coloring left right))
          mapped := by
      simpa using hmapped
    apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedBlue left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge

/-- Fourteen red neighbours inherit a `(3,5)`-free coloring. -/
theorem red_induced_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (embedding : Fin 14 → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (root : AmbientVertex)
    (hrootNe : ∀ index, root.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 25 coloring root.val (embedding index).val = true) :
    isRamseyFree 14 3 5
      (inducedColoring 14 embedding coloring false) := by
  exact red_induced_isRamseyFree_of_decoder hfree embedding hinjective
    localEdgePair_edgeVar_fourteen root hrootNe hneighbour

/-- Any blue-neighbour restriction with a certified local edge decoder,
after complementation, inherits a `(4,4)`-free coloring. -/
theorem blue_induced_isRamseyFree_of_decoder
    {order : Nat} [NeZero order]
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (embedding : Fin order → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (root : AmbientVertex)
    (hrootNe : ∀ index, root.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 25 coloring root.val (embedding index).val = false) :
    isRamseyFree order 4 4
      (inducedColoring order embedding coloring true) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := root.val :: mapped
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 25 := by
      exact mapped_bound embedding hbound
    have hrootNotMapped : root.val ∉ mapped := by
      intro hmem
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
      have hindexBound := hbound index hindex
      have hequal' : root.val = (embedding ⟨index, hindexBound⟩).val := by
        simpa [embedNat, hindexBound] using hequal.symm
      exact hrootNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 5 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < 25 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact root.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring true hall
    have hmapped := mapped_true_related embedding coloring true
      hdecoder hbound hlocal
    have hmappedBlue :
        AllDistinctRelated
          (fun left right => !(ramseyEdge 25 coloring left right))
          mapped := by
      simpa using hmapped
    have hforbiddenBlue :
        AllDistinctRelated
          (fun left right => !(ramseyEdge 25 coloring left right))
          forbidden := by
      apply allDistinctRelated_cons
      · intro left right
        rw [ramseyEdge_comm 25 coloring left right]
      · exact hmappedBlue
      · intro vertex hvertex
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
        have hindexBound := hbound index hindex
        rw [embedNat_of_lt embedding hindexBound]
        have hedge := hneighbour ⟨index, hindexBound⟩
        simp [hedge]
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
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 25 := by
      exact mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring true hall
    have hmapped := mapped_false_related embedding coloring true
      hdecoder hbound hlocal
    have hmappedRed :
        AllDistinctRelated (ramseyEdge 25 coloring) mapped := by
      simpa using hmapped
    apply hfree.1 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedRed left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge

/-- Eighteen blue neighbours, after complementation, inherit a
`(4,4)`-free coloring. -/
theorem blue_induced_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (embedding : Fin 18 → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (root : AmbientVertex)
    (hrootNe : ∀ index, root.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 25 coloring root.val (embedding index).val = false) :
    isRamseyFree 18 4 4
      (inducedColoring 18 embedding coloring true) := by
  exact blue_induced_isRamseyFree_of_decoder hfree embedding hinjective
    localEdgePair_edgeVar_eighteen root hrootNe hneighbour

/-! ## Canonical red and blue neighbourhoods in `K_25` -/

/-- All vertices other than the chosen root. -/
def otherVertices (root : Nat) : List Nat :=
  (List.range 25).erase root

@[simp] theorem mem_otherVertices (root vertex : Nat) :
    vertex ∈ otherVertices root ↔ vertex < 25 ∧ vertex ≠ root := by
  have h := (List.nodup_range (n := 25)).mem_erase_iff
    (a := vertex) (b := root)
  simpa [otherVertices, and_comm] using h

theorem otherVertices_nodup (root : Nat) :
    (otherVertices root).Nodup := by
  exact (List.nodup_range (n := 25)).erase root

theorem otherVertices_length (root : Nat) (hroot : root < 25) :
    (otherVertices root).length = 24 := by
  have hmem : root ∈ List.range 25 := by simp [hroot]
  rw [otherVertices, List.length_erase_of_mem hmem]
  decide

/-- `flip = false` selects red neighbours; `flip = true` selects blue
neighbours and records that their root edge equals `!flip`. -/
def colorNeighbors (coloring : Nat → Bool) (root : Nat)
    (flip : Bool) : List Nat :=
  (otherVertices root).filter fun vertex =>
    if flip then !(ramseyEdge 25 coloring root vertex)
    else ramseyEdge 25 coloring root vertex

@[simp] theorem mem_colorNeighbors (coloring : Nat → Bool)
    (root vertex : Nat) (flip : Bool) :
    vertex ∈ colorNeighbors coloring root flip ↔
      vertex < 25 ∧ vertex ≠ root ∧
        ramseyEdge 25 coloring root vertex = !flip := by
  cases flip <;> simp [colorNeighbors, and_assoc]

theorem colorNeighbors_nodup (coloring : Nat → Bool)
    (root : Nat) (flip : Bool) :
    (colorNeighbors coloring root flip).Nodup := by
  exact (otherVertices_nodup root).filter _

theorem colorNeighbors_length_sum (coloring : Nat → Bool)
    (root : Nat) :
    (colorNeighbors coloring root false).length +
      (colorNeighbors coloring root true).length =
        (otherVertices root).length := by
  simpa [colorNeighbors] using
    LRATCatcher.Tests.RamseyRecurrence.filter_bool_partition_length
      (otherVertices root) (fun vertex => ramseyEdge 25 coloring root vertex)

theorem colorNeighbors_length_sum_twentyFour (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25) :
    (colorNeighbors coloring root false).length +
      (colorNeighbors coloring root true).length = 24 := by
  rw [colorNeighbors_length_sum, otherVertices_length root hroot]

def chosenNeighbor {order : Nat} (coloring : Nat → Bool)
    (root : Nat) (flip : Bool)
    (hlength : order ≤ (colorNeighbors coloring root flip).length)
    (index : Fin order) : Nat :=
  (colorNeighbors coloring root flip)[index.val]'(by
    exact Nat.lt_of_lt_of_le index.isLt hlength)

theorem chosenNeighbor_mem {order : Nat} (coloring : Nat → Bool)
    (root : Nat) (flip : Bool)
    (hlength : order ≤ (colorNeighbors coloring root flip).length)
    (index : Fin order) :
    chosenNeighbor coloring root flip hlength index ∈
      colorNeighbors coloring root flip := by
  exact List.getElem_mem _

def neighborEmbedding {order : Nat} (coloring : Nat → Bool)
    (root : Nat) (flip : Bool)
    (hlength : order ≤ (colorNeighbors coloring root flip).length) :
    Fin order → AmbientVertex := fun index =>
  ⟨chosenNeighbor coloring root flip hlength index,
    (mem_colorNeighbors coloring root
      (chosenNeighbor coloring root flip hlength index) flip).mp
        (chosenNeighbor_mem coloring root flip hlength index) |>.1⟩

theorem neighborEmbedding_injective {order : Nat}
    (coloring : Nat → Bool) (root : Nat) (flip : Bool)
    (hlength : order ≤ (colorNeighbors coloring root flip).length) :
    Function.Injective
      (neighborEmbedding coloring root flip hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj
    (colorNeighbors_nodup coloring root flip)).mp hvalues

theorem neighborEmbedding_ne_root {order : Nat}
    (coloring : Nat → Bool) (root : Nat) (flip : Bool)
    (hlength : order ≤ (colorNeighbors coloring root flip).length)
    (index : Fin order) :
    root ≠ (neighborEmbedding coloring root flip hlength index).val := by
  have hmem := chosenNeighbor_mem coloring root flip hlength index
  have hne := (mem_colorNeighbors coloring root
    (chosenNeighbor coloring root flip hlength index) flip).mp hmem |>.2.1
  exact hne.symm

theorem neighborEmbedding_color {order : Nat}
    (coloring : Nat → Bool) (root : Nat) (flip : Bool)
    (hlength : order ≤ (colorNeighbors coloring root flip).length)
    (index : Fin order) :
    ramseyEdge 25 coloring root
      (neighborEmbedding coloring root flip hlength index).val = !flip := by
  have hmem := chosenNeighbor_mem coloring root flip hlength index
  exact (mem_colorNeighbors coloring root
    (chosenNeighbor coloring root flip hlength index) flip).mp hmem |>.2.2

/-! ## The degree window -/

theorem redDegree_le_thirteen
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hR35 : ¬ hasRamseyFreeColoring 14 3 5)
    (root : Nat) (hroot : root < 25) :
    (colorNeighbors coloring root false).length ≤ 13 := by
  by_cases hlength :
      14 ≤ (colorNeighbors coloring root false).length
  · exfalso
    let embedding := neighborEmbedding
      (order := 14) coloring root false hlength
    have hinjective : Function.Injective embedding := by
      exact neighborEmbedding_injective coloring root false hlength
    have hrootNe : ∀ index, root ≠ (embedding index).val := by
      exact neighborEmbedding_ne_root coloring root false hlength
    have hneighbour : ∀ index,
        ramseyEdge 25 coloring root (embedding index).val = true := by
      intro index
      simpa using neighborEmbedding_color coloring root false hlength index
    apply hR35
    exact ⟨inducedColoring 14 embedding coloring false,
      red_induced_isRamseyFree hfree embedding hinjective
        ⟨root, hroot⟩ hrootNe hneighbour⟩
  · omega

theorem blueDegree_le_seventeen
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hR44 : ¬ hasRamseyFreeColoring 18 4 4)
    (root : Nat) (hroot : root < 25) :
    (colorNeighbors coloring root true).length ≤ 17 := by
  by_cases hlength :
      18 ≤ (colorNeighbors coloring root true).length
  · exfalso
    let embedding := neighborEmbedding
      (order := 18) coloring root true hlength
    have hinjective : Function.Injective embedding := by
      exact neighborEmbedding_injective coloring root true hlength
    have hrootNe : ∀ index, root ≠ (embedding index).val := by
      exact neighborEmbedding_ne_root coloring root true hlength
    have hneighbour : ∀ index,
        ramseyEdge 25 coloring root (embedding index).val = false := by
      intro index
      simpa using neighborEmbedding_color coloring root true hlength index
    apply hR44
    exact ⟨inducedColoring 18 embedding coloring true,
      blue_induced_isRamseyFree hfree embedding hinjective
        ⟨root, hroot⟩ hrootNe hneighbour⟩
  · omega

theorem redDegree_ge_seven
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hR44 : ¬ hasRamseyFreeColoring 18 4 4)
    (root : Nat) (hroot : root < 25) :
    7 ≤ (colorNeighbors coloring root false).length := by
  have hsum := colorNeighbors_length_sum_twentyFour coloring root hroot
  have hblue := blueDegree_le_seventeen hfree hR44 root hroot
  omega

/-- Main reusable reduction: in every hypothetical `(4,5)`-free coloring of
`K_25`, every red degree lies in the seven-to-thirteen window. -/
theorem allRedDegrees_between_seven_and_thirteen
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (hR35 : ¬ hasRamseyFreeColoring 14 3 5)
    (hR44 : ¬ hasRamseyFreeColoring 18 4 4) :
    ∀ root, root < 25 →
      7 ≤ (colorNeighbors coloring root false).length ∧
      (colorNeighbors coloring root false).length ≤ 13 := by
  intro root hroot
  exact ⟨redDegree_ge_seven hfree hR44 root hroot,
    redDegree_le_thirteen hfree hR35 root hroot⟩

#print axioms allRedDegrees_between_seven_and_thirteen

end LRATCatcher.Tests.R45DegreeReduction
