import LRATCatcher.Tests.R44RootedGraphReduction
import LRATCatcher.Tests.RamseyUpperBounds

/-!
  # Degree split at a fixed root of an `R(4,4,16)` coloring

  At vertex `15`, the other vertices are the canonically ordered list
  `0, ..., 14`.  Nine neighbours of either color would induce an
  `R(3,4,9)` coloring (complementing first for the false color), contradicting
  the certified theorem `r34_upper`.  Consequently the two color degrees are
  seven and eight in some order.
-/

namespace LRATCatcher.Tests.R44RootedDegreeSplit

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44RootedGraphReduction

abbrev LocalVertex := Fin 9
abbrev AmbientVertex := Fin 16

def root : Nat := 15

/-! ## Restricting a coloring to nine embedded vertices -/

/-- Pull an order-sixteen coloring back along nine embedded vertices. -/
def inducedColoring (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (index : Nat) : Bool :=
  let endpoints :=
    LRATCatcher.Tests.RamseyRecurrence.localEdgePair index
  ramseyEdge 16 coloring
    (embedding endpoints.1).val (embedding endpoints.2).val

theorem inducedColoring_edgeVar
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool)
    (left right : LocalVertex) (hordered : left < right) :
    inducedColoring embedding coloring (edgeVar 9 left.val right.val) =
      ramseyEdge 16 coloring
        (embedding left).val (embedding right).val := by
  simp [inducedColoring,
    LRATCatcher.Tests.RamseyRecurrence.localEdgePair_edgeVar
      left right hordered]

/-- Extend the finite embedding to an injective total map on naturals. -/
def embedNat (embedding : LocalVertex → AmbientVertex) (vertex : Nat) : Nat :=
  if hvertex : vertex < 9 then
    (embedding ⟨vertex, hvertex⟩).val
  else
    16 + vertex

@[simp] theorem embedNat_of_lt (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 9) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 9) :
    embedNat embedding vertex < 16 := by
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
      have hrightValue : embedNat embedding right = 16 + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < 9
    · have hleftValue : embedNat embedding left = 16 + left := by
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
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < 16 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem ramseyEdge_inducedColoring
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool)
    (left right : LocalVertex) (hne : left ≠ right) :
    ramseyEdge 9 (inducedColoring embedding coloring)
        left.val right.val =
      ramseyEdge 16 coloring
        (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      inducedColoring_edgeVar embedding coloring left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm 9 (inducedColoring embedding coloring)]
    rw [ramseyEdge_comm 16 coloring]
    simpa [ramseyEdge, hreverse] using
      inducedColoring_edgeVar embedding coloring right left hreverseFin

theorem local_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool)
    {vertices : List Nat}
    (_hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
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
    (coloring : Nat → Bool)
    {vertices : List Nat}
    (_hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
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
    (coloring : Nat → Bool)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hrelated : AllDistinctRelated
      (ramseyEdge 9 (inducedColoring embedding coloring)) vertices) :
    AllDistinctRelated (ramseyEdge 16 coloring)
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
    (coloring : Nat → Bool)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 9)
    (hrelated : AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 9 (inducedColoring embedding coloring) left right))
      vertices) :
    AllDistinctRelated (fun left right => !(ramseyEdge 16 coloring left right))
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

/-- Nine true neighbours of a root in an `R(4,4,16)` coloring would inherit
an `R(3,4,9)` coloring. -/
theorem trueNeighbor_induced_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring)
    (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (rootVertex : AmbientVertex)
    (hrootNe : ∀ index, rootVertex.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 16 coloring rootVertex.val (embedding index).val = true) :
    isRamseyFree 9 3 4 (inducedColoring embedding coloring) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := rootVertex.val :: mapped
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 16 :=
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
        ∀ vertex, vertex ∈ forbidden → vertex < 16 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact rootVertex.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring hbound hall
    have hmappedRed := mapped_true_related embedding coloring hbound hlocal
    have hforbiddenRed :
        AllDistinctRelated (ramseyEdge 16 coloring) forbidden := by
      apply allDistinctRelated_cons
      · exact ramseyEdge_comm 16 coloring
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
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 16 :=
      mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring hbound hall
    have hmappedBlue := mapped_false_related embedding coloring hbound hlocal
    apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedBlue left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge

/-! ## The ordered root blocks -/

/-- Increasing list of the true neighbours of vertex `15`. -/
def trueNeighbors (coloring : Nat → Bool) : List Nat :=
  (List.range root).filter fun vertex =>
    ramseyEdge 16 coloring root vertex

/-- Increasing list of the false neighbours of vertex `15`. -/
def falseNeighbors (coloring : Nat → Bool) : List Nat :=
  (List.range root).filter fun vertex =>
    !(ramseyEdge 16 coloring root vertex)

@[simp] theorem mem_trueNeighbors (coloring : Nat → Bool) (vertex : Nat) :
    vertex ∈ trueNeighbors coloring ↔
      vertex < root ∧ ramseyEdge 16 coloring root vertex = true := by
  simp [trueNeighbors]

@[simp] theorem mem_falseNeighbors (coloring : Nat → Bool) (vertex : Nat) :
    vertex ∈ falseNeighbors coloring ↔
      vertex < root ∧ ramseyEdge 16 coloring root vertex = false := by
  simp [falseNeighbors]

theorem trueNeighbors_nodup (coloring : Nat → Bool) :
    (trueNeighbors coloring).Nodup :=
  (List.nodup_range (n := root)).filter _

theorem falseNeighbors_nodup (coloring : Nat → Bool) :
    (falseNeighbors coloring).Nodup :=
  (List.nodup_range (n := root)).filter _

theorem trueNeighbors_pairwise_lt (coloring : Nat → Bool) :
    (trueNeighbors coloring).Pairwise (· < ·) :=
  (List.pairwise_lt_range (n := root)).filter _

theorem falseNeighbors_pairwise_lt (coloring : Nat → Bool) :
    (falseNeighbors coloring).Pairwise (· < ·) :=
  (List.pairwise_lt_range (n := root)).filter _

theorem trueNeighbors_bound (coloring : Nat → Bool)
    {vertex : Nat} (hvertex : vertex ∈ trueNeighbors coloring) :
    vertex < 16 := by
  have := (mem_trueNeighbors coloring vertex).mp hvertex |>.1
  simp [root] at this
  omega

theorem falseNeighbors_bound (coloring : Nat → Bool)
    {vertex : Nat} (hvertex : vertex ∈ falseNeighbors coloring) :
    vertex < 16 := by
  have := (mem_falseNeighbors coloring vertex).mp hvertex |>.1
  simp [root] at this
  omega

theorem trueNeighbors_ne_root (coloring : Nat → Bool)
    {vertex : Nat} (hvertex : vertex ∈ trueNeighbors coloring) :
    vertex ≠ root := by
  have := (mem_trueNeighbors coloring vertex).mp hvertex |>.1
  omega

theorem falseNeighbors_ne_root (coloring : Nat → Bool)
    {vertex : Nat} (hvertex : vertex ∈ falseNeighbors coloring) :
    vertex ≠ root := by
  have := (mem_falseNeighbors coloring vertex).mp hvertex |>.1
  omega

theorem rootNeighbor_length_sum (coloring : Nat → Bool) :
    (trueNeighbors coloring).length + (falseNeighbors coloring).length = 15 := by
  simpa [trueNeighbors, falseNeighbors, root] using
    LRATCatcher.Tests.RamseyRecurrence.filter_bool_partition_length
      (List.range 15) (fun vertex => ramseyEdge 16 coloring 15 vertex)

/-! ## The certified degree bound -/

def chosenTrueNeighbor (coloring : Nat → Bool)
    (hlength : 9 ≤ (trueNeighbors coloring).length)
    (index : LocalVertex) : Nat :=
  (trueNeighbors coloring)[index.val]'(by
    exact Nat.lt_of_lt_of_le index.isLt hlength)

theorem chosenTrueNeighbor_mem (coloring : Nat → Bool)
    (hlength : 9 ≤ (trueNeighbors coloring).length)
    (index : LocalVertex) :
    chosenTrueNeighbor coloring hlength index ∈ trueNeighbors coloring := by
  exact List.getElem_mem _

def trueNeighborEmbedding (coloring : Nat → Bool)
    (hlength : 9 ≤ (trueNeighbors coloring).length) :
    LocalVertex → AmbientVertex := fun index =>
  ⟨chosenTrueNeighbor coloring hlength index,
    trueNeighbors_bound coloring
      (chosenTrueNeighbor_mem coloring hlength index)⟩

theorem trueNeighborEmbedding_injective (coloring : Nat → Bool)
    (hlength : 9 ≤ (trueNeighbors coloring).length) :
    Function.Injective (trueNeighborEmbedding coloring hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj (trueNeighbors_nodup coloring)).mp hvalues

theorem trueNeighborEmbedding_ne_root (coloring : Nat → Bool)
    (hlength : 9 ≤ (trueNeighbors coloring).length)
    (index : LocalVertex) :
    root ≠ (trueNeighborEmbedding coloring hlength index).val := by
  exact (trueNeighbors_ne_root coloring
    (chosenTrueNeighbor_mem coloring hlength index)).symm

theorem trueNeighborEmbedding_color (coloring : Nat → Bool)
    (hlength : 9 ≤ (trueNeighbors coloring).length)
    (index : LocalVertex) :
    ramseyEdge 16 coloring root
      (trueNeighborEmbedding coloring hlength index).val = true := by
  exact (mem_trueNeighbors coloring
    (chosenTrueNeighbor coloring hlength index)).mp
      (chosenTrueNeighbor_mem coloring hlength index) |>.2

/-- The certified bound `R(3,4) ≤ 9` rules out nine true neighbours. -/
theorem trueNeighbors_length_le_eight
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring) :
    (trueNeighbors coloring).length ≤ 8 := by
  by_cases hlength : 9 ≤ (trueNeighbors coloring).length
  · exfalso
    apply LRATCatcher.Tests.RamseyUpperBounds.r34_upper
    let embedding := trueNeighborEmbedding coloring hlength
    exact ⟨inducedColoring embedding coloring,
      trueNeighbor_induced_isRamseyFree hfree embedding
        (trueNeighborEmbedding_injective coloring hlength)
        ⟨root, by simp [root]⟩
        (trueNeighborEmbedding_ne_root coloring hlength)
        (trueNeighborEmbedding_color coloring hlength)⟩
  · omega

theorem trueNeighbors_complement_eq_falseNeighbors (coloring : Nat → Bool) :
    trueNeighbors (complementColoring coloring) = falseNeighbors coloring := by
  unfold trueNeighbors falseNeighbors
  apply List.filter_congr
  intro vertex hvertex
  have hbound := List.mem_range.mp hvertex
  have hbound15 : vertex < 15 := by
    simpa [root] using hbound
  have hnotReverse : ¬ 15 < vertex := by omega
  simp [root, ramseyEdge, complementColoring, hbound15, hnotReverse]

theorem falseNeighbors_complement_eq_trueNeighbors (coloring : Nat → Bool) :
    falseNeighbors (complementColoring coloring) = trueNeighbors coloring := by
  unfold falseNeighbors trueNeighbors
  apply List.filter_congr
  intro vertex hvertex
  have hbound := List.mem_range.mp hvertex
  have hbound15 : vertex < 15 := by
    simpa [root] using hbound
  have hnotReverse : ¬ 15 < vertex := by omega
  simp [root, ramseyEdge, complementColoring, hbound15, hnotReverse]

/-- The false degree obeys the same bound by color complementation. -/
theorem falseNeighbors_length_le_eight
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring) :
    (falseNeighbors coloring).length ≤ 8 := by
  have hbound := trueNeighbors_length_le_eight
    (complementColoring_isRamseyFree hfree)
  simpa only [trueNeighbors_complement_eq_falseNeighbors] using hbound

/-- At the fixed root, the two color degrees are seven and eight. -/
theorem rootNeighbor_length_split
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring) :
    ((trueNeighbors coloring).length = 7 ∧
      (falseNeighbors coloring).length = 8) ∨
    ((trueNeighbors coloring).length = 8 ∧
      (falseNeighbors coloring).length = 7) := by
  have hsum := rootNeighbor_length_sum coloring
  have htrue := trueNeighbors_length_le_eight hfree
  have hfalse := falseNeighbors_length_le_eight hfree
  omega

theorem trueNeighbors_length_eq_seven_or_eight
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring) :
    (trueNeighbors coloring).length = 7 ∨
      (trueNeighbors coloring).length = 8 := by
  rcases rootNeighbor_length_split hfree with hsplit | hsplit
  · exact Or.inl hsplit.1
  · exact Or.inr hsplit.1

/-! ## Oriented seven-plus-eight blocks -/

def orientedColoring (coloring : Nat → Bool) (flip : Bool) : Nat → Bool :=
  if flip then complementColoring coloring else coloring

def leftBlock (coloring : Nat → Bool) (flip : Bool) : List Nat :=
  trueNeighbors (orientedColoring coloring flip)

def antiBlock (coloring : Nat → Bool) (flip : Bool) : List Nat :=
  falseNeighbors (orientedColoring coloring flip)

theorem leftBlock_nodup (coloring : Nat → Bool) (flip : Bool) :
    (leftBlock coloring flip).Nodup :=
  trueNeighbors_nodup _

theorem antiBlock_nodup (coloring : Nat → Bool) (flip : Bool) :
    (antiBlock coloring flip).Nodup :=
  falseNeighbors_nodup _

theorem leftBlock_pairwise_lt (coloring : Nat → Bool) (flip : Bool) :
    (leftBlock coloring flip).Pairwise (· < ·) :=
  trueNeighbors_pairwise_lt _

theorem antiBlock_pairwise_lt (coloring : Nat → Bool) (flip : Bool) :
    (antiBlock coloring flip).Pairwise (· < ·) :=
  falseNeighbors_pairwise_lt _

theorem leftBlock_bound (coloring : Nat → Bool) (flip : Bool)
    {vertex : Nat} (hvertex : vertex ∈ leftBlock coloring flip) :
    vertex < 16 :=
  trueNeighbors_bound _ hvertex

theorem antiBlock_bound (coloring : Nat → Bool) (flip : Bool)
    {vertex : Nat} (hvertex : vertex ∈ antiBlock coloring flip) :
    vertex < 16 :=
  falseNeighbors_bound _ hvertex

def OrientedRootSplit (coloring : Nat → Bool) : Prop :=
  ∃ flip : Bool,
    isRamseyFree 16 4 4 (orientedColoring coloring flip) ∧
      (leftBlock coloring flip).length = 7 ∧
      (antiBlock coloring flip).length = 8

/-- Every `R(4,4,16)` coloring admits an orientation whose true and false
root blocks have respective orders seven and eight. -/
theorem exists_orientedRootSplit
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring) :
    OrientedRootSplit coloring := by
  rcases rootNeighbor_length_split hfree with hsplit | hsplit
  · refine ⟨false, ?_, ?_, ?_⟩
    · simpa [orientedColoring] using hfree
    · simpa [leftBlock, orientedColoring] using hsplit.1
    · simpa [antiBlock, orientedColoring] using hsplit.2
  · refine ⟨true, ?_, ?_, ?_⟩
    · simpa [orientedColoring] using
        (complementColoring_isRamseyFree hfree)
    · simpa [leftBlock, orientedColoring,
        trueNeighbors_complement_eq_falseNeighbors] using hsplit.2
    · simpa [antiBlock, orientedColoring,
        falseNeighbors_complement_eq_trueNeighbors] using hsplit.1

#print axioms trueNeighbors_length_le_eight
#print axioms rootNeighbor_length_split
#print axioms exists_orientedRootSplit

end LRATCatcher.Tests.R44RootedDegreeSplit
