import LRATCatcher.Tests.R44RootedGraphReduction
import LRATCatcher.Tests.RamseyUpperBounds

/-!
  # Certified degree bounds for `R(4,4)`-free colorings of `K_12`

  Nine neighbours of either colour would induce an `R(3,4)`-free coloring
  on nine vertices, contradicting the certified bound `R(3,4) ≤ 9`.
  Since every vertex has eleven incident edges, every positive degree is at
  least three.  This is the bound used by the two-centre split.
-/

namespace LRATCatcher.Tests.R44OrderTwelveDegreeBounds

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44RootedGraphReduction

abbrev LocalVertex := Fin 9
abbrev AmbientVertex := Fin 12

def inducedColoring (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (index : Nat) : Bool :=
  let endpoints := LRATCatcher.Tests.RamseyRecurrence.localEdgePair index
  ramseyEdge 12 coloring
    (embedding endpoints.1).val (embedding endpoints.2).val

theorem inducedColoring_edgeVar
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool)
    (left right : LocalVertex) (hordered : left < right) :
    inducedColoring embedding coloring (edgeVar 9 left.val right.val) =
      ramseyEdge 12 coloring
        (embedding left).val (embedding right).val := by
  simp [inducedColoring,
    LRATCatcher.Tests.RamseyRecurrence.localEdgePair_edgeVar
      left right hordered]

def embedNat (embedding : LocalVertex → AmbientVertex)
    (vertex : Nat) : Nat :=
  if hvertex : vertex < 9 then
    (embedding ⟨vertex, hvertex⟩).val
  else
    12 + vertex

@[simp] theorem embedNat_of_lt (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 9) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 9) :
    embedNat embedding vertex < 12 := by
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
      have hrightValue : embedNat embedding right = 12 + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < 9
    · have hleftValue : embedNat embedding left = 12 + left := by
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
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < 12 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem ramseyEdge_inducedColoring
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool)
    (left right : LocalVertex) (hne : left ≠ right) :
    ramseyEdge 9 (inducedColoring embedding coloring)
        left.val right.val =
      ramseyEdge 12 coloring
        (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      inducedColoring_edgeVar embedding coloring left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm 9 (inducedColoring embedding coloring)]
    rw [ramseyEdge_comm 12 coloring]
    simpa [ramseyEdge, hreverse] using
      inducedColoring_edgeVar embedding coloring right left hreverseFin

theorem local_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hall : ∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      inducedColoring embedding coloring (edgeVar 9 left right) = true) :
    AllDistinctRelated
      (ramseyEdge 9 (inducedColoring embedding coloring)) vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem local_false_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hall : ∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      inducedColoring embedding coloring (edgeVar 9 left right) = false) :
    AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 9 (inducedColoring embedding coloring) left right))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge 9 (inducedColoring embedding coloring) left right) = true
    rw [ramseyEdge_comm 9 (inducedColoring embedding coloring)]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem mapped_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hrelated : AllDistinctRelated
      (ramseyEdge 9 (inducedColoring embedding coloring)) vertices) :
    AllDistinctRelated (ramseyEdge 12 coloring)
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
  have hedge := ramseyEdge_inducedColoring embedding coloring
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  rw [hedge] at hlocal
  exact hlocal

theorem mapped_false_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hrelated : AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 9 (inducedColoring embedding coloring) left right))
      vertices) :
    AllDistinctRelated (fun left right => !(ramseyEdge 12 coloring left right))
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
  have hedge := ramseyEdge_inducedColoring embedding coloring
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  change Bool.not
    (ramseyEdge 9 (inducedColoring embedding coloring)
      indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  exact hlocal

theorem trueNeighbor_induced_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (rootVertex : AmbientVertex)
    (hrootNe : ∀ index, rootVertex.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 12 coloring rootVertex.val (embedding index).val = true) :
    isRamseyFree 9 3 4 (inducedColoring embedding coloring) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := rootVertex.val :: mapped
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 12 :=
      mapped_bound embedding hbound
    have hrootNotMapped : rootVertex.val ∉ mapped := by
      intro hmember
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmember
      have hindexBound := hbound index hindex
      have hequal' : rootVertex.val =
          (embedding ⟨index, hindexBound⟩).val := by
        simpa [embedNat, hindexBound] using hequal.symm
      exact hrootNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 4 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < 12 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact rootVertex.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring hall
    have hmappedRed := mapped_true_related embedding coloring hbound hlocal
    have hforbiddenRed :
        AllDistinctRelated (ramseyEdge 12 coloring) forbidden := by
      apply allDistinctRelated_cons
      · exact ramseyEdge_comm 12 coloring
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
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 12 :=
      mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring hall
    have hmappedBlue := mapped_false_related embedding coloring hbound hlocal
    apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedBlue left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge

def otherVertices (root : AmbientVertex) : List Nat :=
  (List.range 12).filter fun vertex => vertex != root.val

def positiveNeighbors (coloring : Nat → Bool)
    (root : AmbientVertex) : List Nat :=
  (otherVertices root).filter fun vertex =>
    ramseyEdge 12 coloring root.val vertex

def negativeNeighbors (coloring : Nat → Bool)
    (root : AmbientVertex) : List Nat :=
  (otherVertices root).filter fun vertex =>
    !(ramseyEdge 12 coloring root.val vertex)

@[simp] theorem mem_positiveNeighbors (coloring : Nat → Bool)
    (root : AmbientVertex) (vertex : Nat) :
    vertex ∈ positiveNeighbors coloring root ↔
      vertex < 12 ∧ vertex ≠ root.val ∧
        ramseyEdge 12 coloring root.val vertex = true := by
  simp [positiveNeighbors, otherVertices, and_left_comm, and_comm]

@[simp] theorem mem_negativeNeighbors (coloring : Nat → Bool)
    (root : AmbientVertex) (vertex : Nat) :
    vertex ∈ negativeNeighbors coloring root ↔
      vertex < 12 ∧ vertex ≠ root.val ∧
        ramseyEdge 12 coloring root.val vertex = false := by
  simp [negativeNeighbors, otherVertices, and_left_comm, and_comm]

theorem positiveNeighbors_nodup (coloring : Nat → Bool)
    (root : AmbientVertex) :
    (positiveNeighbors coloring root).Nodup := by
  exact ((List.nodup_range (n := 12)).filter _).filter _

theorem negativeNeighbors_nodup (coloring : Nat → Bool)
    (root : AmbientVertex) :
    (negativeNeighbors coloring root).Nodup := by
  exact ((List.nodup_range (n := 12)).filter _).filter _

theorem otherVertices_length (root : AmbientVertex) :
    (otherVertices root).length = 11 := by
  native_decide +revert
theorem neighbor_length_sum (coloring : Nat → Bool)
    (root : AmbientVertex) :
    (positiveNeighbors coloring root).length +
      (negativeNeighbors coloring root).length = 11 := by
  have hpartition :=
    LRATCatcher.Tests.RamseyRecurrence.filter_bool_partition_length
      (otherVertices root)
      (fun vertex => ramseyEdge 12 coloring root.val vertex)
  have hlength := otherVertices_length root
  simpa [positiveNeighbors, negativeNeighbors, hlength] using hpartition

def chosenNegativeNeighbor (coloring : Nat → Bool)
    (root : AmbientVertex)
    (hlength : 9 ≤ (negativeNeighbors coloring root).length)
    (index : LocalVertex) : Nat :=
  (negativeNeighbors coloring root)[index.val]'(by
    exact Nat.lt_of_lt_of_le index.isLt hlength)

theorem chosenNegativeNeighbor_mem (coloring : Nat → Bool)
    (root : AmbientVertex)
    (hlength : 9 ≤ (negativeNeighbors coloring root).length)
    (index : LocalVertex) :
    chosenNegativeNeighbor coloring root hlength index ∈
      negativeNeighbors coloring root := by
  exact List.getElem_mem _

def negativeNeighborEmbedding (coloring : Nat → Bool)
    (root : AmbientVertex)
    (hlength : 9 ≤ (negativeNeighbors coloring root).length) :
    LocalVertex → AmbientVertex := fun index =>
  ⟨chosenNegativeNeighbor coloring root hlength index,
    (mem_negativeNeighbors coloring root
      (chosenNegativeNeighbor coloring root hlength index)).mp
        (chosenNegativeNeighbor_mem coloring root hlength index) |>.1⟩

theorem negativeNeighborEmbedding_injective (coloring : Nat → Bool)
    (root : AmbientVertex)
    (hlength : 9 ≤ (negativeNeighbors coloring root).length) :
    Function.Injective (negativeNeighborEmbedding coloring root hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj (negativeNeighbors_nodup coloring root)).mp hvalues

theorem negativeNeighborEmbedding_ne_root (coloring : Nat → Bool)
    (root : AmbientVertex)
    (hlength : 9 ≤ (negativeNeighbors coloring root).length)
    (index : LocalVertex) :
    root.val ≠ (negativeNeighborEmbedding coloring root hlength index).val := by
  exact ((mem_negativeNeighbors coloring root _).mp
    (chosenNegativeNeighbor_mem coloring root hlength index) |>.2.1).symm

theorem negativeNeighborEmbedding_color (coloring : Nat → Bool)
    (root : AmbientVertex)
    (hlength : 9 ≤ (negativeNeighbors coloring root).length)
    (index : LocalVertex) :
    ramseyEdge 12 coloring root.val
      (negativeNeighborEmbedding coloring root hlength index).val = false := by
  exact (mem_negativeNeighbors coloring root _).mp
    (chosenNegativeNeighbor_mem coloring root hlength index) |>.2.2

theorem ramseyEdge_complementColoring
    (coloring : Nat → Bool) (left right : Nat) (hne : left ≠ right) :
    ramseyEdge 12 (complementColoring coloring) left right =
      !(ramseyEdge 12 coloring left right) := by
  rcases Nat.lt_trichotomy left right with hordered | hequal | hreverse
  · simp [ramseyEdge, complementColoring, hordered]
  · exact absurd hequal hne
  · have hnotOrdered : ¬ left < right := by omega
    have hreverseOrdered : right < left := by omega
    simp [ramseyEdge, complementColoring, hnotOrdered, hreverseOrdered]
theorem negativeNeighbors_length_le_eight
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (root : AmbientVertex) :
    (negativeNeighbors coloring root).length ≤ 8 := by
  by_cases hlength : 9 ≤ (negativeNeighbors coloring root).length
  · exfalso
    apply LRATCatcher.Tests.RamseyUpperBounds.r34_upper
    let embedding := negativeNeighborEmbedding coloring root hlength
    have hcomplementFree := complementColoring_isRamseyFree hfree
    have hneighbour : ∀ index,
        ramseyEdge 12 (complementColoring coloring) root.val
          (embedding index).val = true := by
      intro index
      have hedge := negativeNeighborEmbedding_color coloring root hlength index
      change ramseyEdge 12 (complementColoring coloring) root.val
        (negativeNeighborEmbedding coloring root hlength index).val = true
      rw [ramseyEdge_complementColoring]
      · simp [hedge]
      · exact negativeNeighborEmbedding_ne_root coloring root hlength index
    exact ⟨inducedColoring embedding (complementColoring coloring),
      trueNeighbor_induced_isRamseyFree hcomplementFree embedding
        (negativeNeighborEmbedding_injective coloring root hlength)
        root
        (negativeNeighborEmbedding_ne_root coloring root hlength)
        hneighbour⟩
  · omega

theorem positiveDegree_ge_three
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (root : AmbientVertex) :
    3 ≤ (positiveNeighbors coloring root).length := by
  have hsum := neighbor_length_sum coloring root
  have hnegative := negativeNeighbors_length_le_eight hfree root
  omega

#print axioms negativeNeighbors_length_le_eight
#print axioms positiveDegree_ge_three

end LRATCatcher.Tests.R44OrderTwelveDegreeBounds
