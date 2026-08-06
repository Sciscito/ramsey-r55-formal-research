import LRATCatcher.Tests.R55CanonicalUnitsBridge
import LRATCatcher.Tests.R55ColoringPermutation

namespace LRATCatcher.Tests.R55

namespace CanonicalRelabeling

open DegreeTwentyCodegreeTenNeighborhood.ExactLists
open LRATCatcher.Ramsey
open CanonicalUnits
open LRATCatcher.Tests.R35

def eraseListed [BEq α] : List α → List α → List α
  | ambient, [] => ambient
  | ambient, head :: tail => eraseListed (ambient.erase head) tail

theorem cons_erase_perm [BEq α] [LawfulBEq α] {head : α} {ambient : List α}
    (hmem : head ∈ ambient) :
    (head :: ambient.erase head).Perm ambient := by
  induction ambient with
  | nil => simp at hmem
  | cons first tail ih =>
      by_cases hequal : head = first
      · subst first
        simp
      · have htail : head ∈ tail := by simpa [hequal] using hmem
        rw [List.erase_cons]
        rw [if_neg]
        · exact (List.Perm.swap head first (tail.erase head)).symm.trans
            (List.Perm.cons first (ih htail))
        · simpa using Ne.symm hequal

theorem append_eraseListed_perm [BEq α] [LawfulBEq α]
    {picked ambient : List α}
    (hpickedNodup : picked.Nodup)
    (hsubset : ∀ value, value ∈ picked → value ∈ ambient) :
    (picked ++ eraseListed ambient picked).Perm ambient := by
  induction picked generalizing ambient with
  | nil => simp [eraseListed]
  | cons head tail ih =>
      rw [List.nodup_cons] at hpickedNodup
      obtain ⟨hheadNotTail, htailNodup⟩ := hpickedNodup
      have hheadMem : head ∈ ambient := hsubset head (by simp)
      have htailSubset : ∀ value, value ∈ tail → value ∈ ambient.erase head := by
        intro value hvalue
        have hne : value ≠ head := by
          intro hequal
          subst value
          exact hheadNotTail hvalue
        exact (List.mem_erase_of_ne hne).2
          (hsubset value (by simp [hvalue]))
      have htailPerm := ih htailNodup htailSubset
      simp only [eraseListed, List.cons_append]
      exact (List.Perm.cons head htailPerm).trans (cons_erase_perm hheadMem)

/-- The eleven specially ordered root neighbours: anchor first, the ten
common red neighbours next. -/
def fixedRootNeighbors {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) : List Nat :=
  data.anchor :: data.commonNeighbors

theorem fixedRootNeighbors_nodup {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (fixedRootNeighbors data).Nodup := by
  have hanchorNotCommon : data.anchor ∉ data.commonNeighbors := by
    intro hmem
    have hred := data.commonNeighbors_red data.anchor hmem
    rw [ramseyEdge_self] at hred
    contradiction
  simp only [fixedRootNeighbors, List.nodup_cons]
  exact ⟨hanchorNotCommon, data.commonNeighbors_nodup⟩

theorem fixedRootNeighbors_subset {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    ∀ vertex, vertex ∈ fixedRootNeighbors data → vertex ∈ data.rootNeighbors := by
  intro vertex hvertex
  simp only [fixedRootNeighbors, List.mem_cons] at hvertex
  rcases hvertex with rfl | hcommon
  · exact data.anchor_mem
  · exact data.commonNeighbors_mem vertex hcommon

/-- All twenty root neighbours in canonical branch order: anchor, ten common
neighbours, then the nine remaining neighbours in their original list order. -/
def orderedRootNeighbors {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) : List Nat :=
  fixedRootNeighbors data ++ eraseListed data.rootNeighbors (fixedRootNeighbors data)

theorem orderedRootNeighbors_perm {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (orderedRootNeighbors data).Perm data.rootNeighbors := by
  exact append_eraseListed_perm (fixedRootNeighbors_nodup data)
    (fixedRootNeighbors_subset data)

@[simp] theorem orderedRootNeighbors_length {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (orderedRootNeighbors data).length = 20 := by
  exact (orderedRootNeighbors_perm data).length_eq.trans data.rootNeighbors_length

theorem orderedRootNeighbors_nodup {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (orderedRootNeighbors data).Nodup :=
  (orderedRootNeighbors_perm data).nodup_iff.mpr data.rootNeighbors_nodup

/-- All labels fixed at the root stage: root `0`, followed by its twenty red
neighbours `1, ..., 20`. -/
def pickedVertices {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) : List Nat :=
  data.root :: orderedRootNeighbors data

theorem pickedVertices_nodup {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (pickedVertices data).Nodup := by
  have hrootNotOrdered : data.root ∉ orderedRootNeighbors data := by
    intro hmem
    have hrootMem : data.root ∈ data.rootNeighbors :=
      (orderedRootNeighbors_perm data).mem_iff.mp hmem
    exact data.root_not_mem hrootMem
  simp only [pickedVertices, List.nodup_cons]
  exact ⟨hrootNotOrdered, orderedRootNeighbors_nodup data⟩

@[simp] theorem pickedVertices_length {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (pickedVertices data).length = 21 := by
  simp [pickedVertices]

theorem pickedVertices_bound {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    ∀ vertex, vertex ∈ pickedVertices data → vertex < 43 := by
  intro vertex hvertex
  simp only [pickedVertices, List.mem_cons] at hvertex
  rcases hvertex with rfl | hneighbor
  · exact data.root_bound
  · exact data.rootNeighbors_bound vertex
      ((orderedRootNeighbors_perm data).mem_iff.mp hneighbor)

/-- Complete the twelve distinguished vertices by the remaining ambient
vertices in increasing order. -/
def canonicalVertexOrder {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) : List Nat :=
  pickedVertices data ++ eraseListed (List.range 43) (pickedVertices data)

theorem canonicalVertexOrder_perm {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (canonicalVertexOrder data).Perm (List.range 43) := by
  apply append_eraseListed_perm (pickedVertices_nodup data)
  intro vertex hvertex
  exact List.mem_range.mpr (pickedVertices_bound data vertex hvertex)

@[simp] theorem canonicalVertexOrder_length {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (canonicalVertexOrder data).length = 43 := by
  exact (canonicalVertexOrder_perm data).length_eq.trans (by simp)

theorem canonicalVertexOrder_nodup {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (canonicalVertexOrder data).Nodup := by
  exact (canonicalVertexOrder_perm data).nodup_iff.mpr List.nodup_range

/-- The original ambient vertex carrying a canonical label.  Its range proof
is obtained from the permutation certificate above, not by truncation. -/
def vertexAt {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Fin 43) : Fin 43 :=
  let vertex := (canonicalVertexOrder data)[label.val]'(by simp)
  ⟨vertex, by
    have hmemOrder : vertex ∈ canonicalVertexOrder data :=
      List.getElem_mem (l := canonicalVertexOrder data) (n := label.val) (by simp)
    have hmemRange : vertex ∈ List.range 43 :=
      (canonicalVertexOrder_perm data).mem_iff.mp hmemOrder
    exact List.mem_range.mp hmemRange⟩

theorem vertexAt_injective {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    Function.Injective (vertexAt data) := by
  intro left right hequal
  apply Fin.ext
  have hvalues :
      (canonicalVertexOrder data)[left.val]'(by simp) =
        (canonicalVertexOrder data)[right.val]'(by simp) :=
    congrArg Fin.val hequal
  exact (List.getElem_inj (canonicalVertexOrder_nodup data)).mp hvalues

theorem vertexAt_surjective {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    Function.Surjective (vertexAt data) := by
  intro vertex
  have hmemRange : vertex.val ∈ List.range 43 := List.mem_range.mpr vertex.isLt
  have hmemOrder : vertex.val ∈ canonicalVertexOrder data :=
    (canonicalVertexOrder_perm data).mem_iff.mpr hmemRange
  obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hmemOrder
  have hindex43 : index < 43 := by simpa using hindex
  refine ⟨⟨index, hindex43⟩, ?_⟩
  apply Fin.ext
  exact hvalue

/-- `vertexAt` is a genuine permutation of the 43 vertices. -/
theorem vertexAt_bijective {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    Function.Injective (vertexAt data) ∧ Function.Surjective (vertexAt data) :=
  ⟨vertexAt_injective data, vertexAt_surjective data⟩

/-- Package the canonical order as the repository's genuine finite
permutation type.  The inverse is selected from the proved surjectivity and
both inverse laws are then discharged using injectivity. -/
noncomputable def vertexPermutation {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) : FinPermutation 43 where
  toFun := vertexAt data
  invFun := fun target => Classical.choose (vertexAt_surjective data target)
  left_inv := by
    intro source
    apply vertexAt_injective data
    exact Classical.choose_spec (vertexAt_surjective data (vertexAt data source))
  right_inv := by
    intro target
    exact Classical.choose_spec (vertexAt_surjective data target)

@[simp] theorem vertexPermutation_apply {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (vertex : Fin 43) :
    vertexPermutation data vertex = vertexAt data vertex := rfl

def rootNeighborLabel (index : Fin 20) : Fin 43 :=
  ⟨index.val + 1, by omega⟩

def commonNeighborLabel (index : Fin 10) : Fin 43 :=
  ⟨index.val + 2, by omega⟩

@[simp] theorem vertexAt_zero {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (vertexAt data ⟨0, by omega⟩).val = data.root := by
  simp [vertexAt, canonicalVertexOrder, pickedVertices]

@[simp] theorem vertexAt_rootNeighborLabel {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (index : Fin 20) :
    (vertexAt data (rootNeighborLabel index)).val =
      (orderedRootNeighbors data)[index.val]'(by simp) := by
  change
    (canonicalVertexOrder data)[index.val + 1]'(by simp; omega) =
      (orderedRootNeighbors data)[index.val]'(by simp)
  unfold canonicalVertexOrder pickedVertices
  rw [List.getElem_append_left (by simp; omega)]
  simp only [List.getElem_cons_succ]

@[simp] theorem vertexAt_one {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    (vertexAt data ⟨1, by omega⟩).val = data.anchor := by
  have hlabel : (⟨1, by omega⟩ : Fin 43) = rootNeighborLabel ⟨0, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hlabel, vertexAt_rootNeighborLabel]
  simp [orderedRootNeighbors, fixedRootNeighbors]

@[simp] theorem vertexAt_commonNeighborLabel {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (index : Fin 10) :
    (vertexAt data (commonNeighborLabel index)).val =
      data.commonNeighbors[index.val]'(by
        rw [data.commonNeighbors_length]
        exact index.isLt) := by
  rw [show commonNeighborLabel index = rootNeighborLabel ⟨index.val + 1, by omega⟩ by
    apply Fin.ext
    simp [commonNeighborLabel, rootNeighborLabel]]
  rw [vertexAt_rootNeighborLabel]
  unfold orderedRootNeighbors fixedRootNeighbors
  rw [List.getElem_append_left (by
    simp [data.commonNeighbors_length]
    omega)]
  simp only [List.getElem_cons_succ]

theorem vertexAt_rootNeighbor_mem {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (index : Fin 20) :
    (vertexAt data (rootNeighborLabel index)).val ∈ data.rootNeighbors := by
  rw [vertexAt_rootNeighborLabel]
  have hmemOrdered :
      (orderedRootNeighbors data)[index.val]'(by simp) ∈ orderedRootNeighbors data :=
    List.getElem_mem (by simp)
  exact (orderedRootNeighbors_perm data).mem_iff.mp hmemOrdered

theorem vertexAt_commonNeighbor_mem {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (index : Fin 10) :
    (vertexAt data (commonNeighborLabel index)).val ∈ data.commonNeighbors := by
  rw [vertexAt_commonNeighborLabel]
  exact List.getElem_mem (by
    rw [data.commonNeighbors_length]
    exact index.isLt)

theorem vertexAt_rootNeighbor_mem_of_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 1 ≤ label) (hupper : label ≤ 20) :
    (vertexAt data ⟨label, by omega⟩).val ∈ data.rootNeighbors := by
  let index : Fin 20 := ⟨label - 1, by omega⟩
  have hlabel : rootNeighborLabel index = ⟨label, by omega⟩ := by
    apply Fin.ext
    simp [rootNeighborLabel, index]
    omega
  rw [← hlabel]
  exact vertexAt_rootNeighbor_mem data index

theorem vertexAt_commonNeighbor_mem_of_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 2 ≤ label) (hupper : label ≤ 11) :
    (vertexAt data ⟨label, by omega⟩).val ∈ data.commonNeighbors := by
  let index : Fin 10 := ⟨label - 2, by omega⟩
  have hlabel : commonNeighborLabel index = ⟨label, by omega⟩ := by
    apply Fin.ext
    simp [commonNeighborLabel, index]
    omega
  rw [← hlabel]
  exact vertexAt_commonNeighbor_mem data index

theorem vertexAt_not_rootNeighbor_of_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 21 ≤ label) (hupper : label < 43) :
    (vertexAt data ⟨label, hupper⟩).val ∉ data.rootNeighbors := by
  intro hmem
  have hordered :
      (vertexAt data ⟨label, hupper⟩).val ∈ orderedRootNeighbors data :=
    (orderedRootNeighbors_perm data).mem_iff.mpr hmem
  obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hordered
  have hindex20 : index < 20 := by simpa using hindex
  let oldLabel := rootNeighborLabel ⟨index, hindex20⟩
  have hvertices : vertexAt data oldLabel = vertexAt data ⟨label, hupper⟩ := by
    apply Fin.ext
    simpa [oldLabel] using hvalue
  have hlabels := vertexAt_injective data hvertices
  have hvalEq : index + 1 = label := by
    simpa [oldLabel, rootNeighborLabel] using congrArg Fin.val hlabels
  omega

theorem vertexAt_not_commonNeighbor_of_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 12 ≤ label) (hupper : label < 43) :
    (vertexAt data ⟨label, hupper⟩).val ∉ data.commonNeighbors := by
  intro hmem
  obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hmem
  have hindex10 : index < 10 := by
    simpa [data.commonNeighbors_length] using hindex
  let oldLabel := commonNeighborLabel ⟨index, hindex10⟩
  have hvertices : vertexAt data oldLabel = vertexAt data ⟨label, hupper⟩ := by
    apply Fin.ext
    simpa [oldLabel] using hvalue
  have hlabels := vertexAt_injective data hvertices
  have hvalEq : index + 2 = label := by
    simpa [oldLabel, commonNeighborLabel] using congrArg Fin.val hlabels
  omega

theorem root_edge_at_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 1 ≤ label) (hupper : label ≤ 20) :
    ramseyEdge 43 coloring data.root (vertexAt data ⟨label, by omega⟩).val = true := by
  apply data.rootNeighbors_red
  exact vertexAt_rootNeighbor_mem_of_label data label hlower hupper

theorem root_edge_false_at_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 21 ≤ label) (hupper : label < 43) :
    ramseyEdge 43 coloring data.root (vertexAt data ⟨label, hupper⟩).val = false := by
  cases hedge : ramseyEdge 43 coloring data.root (vertexAt data ⟨label, hupper⟩).val with
  | false => rfl
  | true =>
      exfalso
      exact vertexAt_not_rootNeighbor_of_label data label hlower hupper
        (data.rootNeighbors_complete _ (vertexAt data ⟨label, hupper⟩).isLt hedge)

theorem anchor_edge_at_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 2 ≤ label) (hupper : label ≤ 11) :
    ramseyEdge 43 coloring data.anchor (vertexAt data ⟨label, by omega⟩).val = true := by
  apply data.commonNeighbors_red
  exact vertexAt_commonNeighbor_mem_of_label data label hlower hupper

theorem anchor_edge_false_at_label {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (label : Nat)
    (hlower : 12 ≤ label) (hupper : label ≤ 20) :
    ramseyEdge 43 coloring data.anchor (vertexAt data ⟨label, by omega⟩).val = false := by
  cases hedge : ramseyEdge 43 coloring data.anchor (vertexAt data ⟨label, by omega⟩).val with
  | false => rfl
  | true =>
      exfalso
      apply vertexAt_not_commonNeighbor_of_label data label hlower (by omega)
      apply data.commonNeighbors_complete
      · exact vertexAt_rootNeighbor_mem_of_label data label (by omega) hupper
      · exact hedge

/-- Global recoloring induced by the genuine vertex permutation. -/
noncomputable def canonicalUnitRelabeling {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) : Nat → Bool :=
  ColoringPermutation.permuteColoring (vertexPermutation data) coloring

theorem edgeVar_root_row (vertex : Nat) :
    edgeVar 43 0 vertex = vertex - 1 := by
  simp [edgeVar]

theorem edgeVar_anchor_row (vertex : Nat) (hlower : 2 ≤ vertex) :
    edgeVar 43 1 vertex = vertex + 40 := by
  simp [edgeVar]
  omega

/-- Every canonical edge is transported by the full vertex permutation. -/
@[simp] theorem canonicalUnitRelabeling_edge {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring)
    (left right : Fin 43) (hlt : left.val < right.val) :
    canonicalUnitRelabeling data (edgeVar 43 left.val right.val) =
      ramseyEdge 43 coloring
        (vertexAt data left).val (vertexAt data right).val := by
  rw [canonicalUnitRelabeling,
    ColoringPermutation.permuteColoring_edgeVar
      (vertexPermutation data) coloring left right hlt]
  simp

/-- The global canonical recoloring preserves and reflects the full
K₅/K₅-free semantic predicate. -/
theorem canonicalUnitRelabeling_ramseyFree_iff {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    isRamseyFree 43 5 5 coloring ↔
      isRamseyFree 43 5 5 (canonicalUnitRelabeling data) := by
  simpa only [canonicalUnitRelabeling] using
    ColoringPermutation.isRamseyFree_permute_iff
      (vertexPermutation data) coloring

@[simp] theorem canonicalUnitRelabeling_root_edge {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (vertex : Nat)
    (hlower : 1 ≤ vertex) (hupper : vertex < 43) :
    canonicalUnitRelabeling data (edgeVar 43 0 vertex) =
      ramseyEdge 43 coloring data.root
        (vertexAt data ⟨vertex, hupper⟩).val := by
  have hpair : (⟨0, by omega⟩ : Fin 43).val < (⟨vertex, hupper⟩ : Fin 43).val := by
    change 0 < vertex
    omega
  rw [canonicalUnitRelabeling_edge data
    ⟨0, by omega⟩ ⟨vertex, hupper⟩ hpair, vertexAt_zero]

@[simp] theorem canonicalUnitRelabeling_anchor_edge {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) (vertex : Nat)
    (hlower : 2 ≤ vertex) (hupper : vertex ≤ 20) :
    canonicalUnitRelabeling data (edgeVar 43 1 vertex) =
      ramseyEdge 43 coloring data.anchor
        (vertexAt data ⟨vertex, by omega⟩).val := by
  have hpair : (⟨1, by omega⟩ : Fin 43).val <
      (⟨vertex, by omega⟩ : Fin 43).val := by
    change 1 < vertex
    omega
  rw [canonicalUnitRelabeling_edge data
    ⟨1, by omega⟩ ⟨vertex, by omega⟩ hpair, vertexAt_one]

/-- The relabelled coloring satisfies all 42 root units and all 19 anchor
units, hence exactly the `CanonicalD20C10Units` interface used by the
catalogue/SAT bridge. -/
theorem canonicalUnitRelabeling_units {coloring : Nat → Bool}
    (data : ExactD20C10NeighborhoodLists coloring) :
    CanonicalD20C10Units (canonicalUnitRelabeling data) := by
  constructor
  · intro literal hliteral
    obtain ⟨vertex, hvertex, rfl⟩ := List.mem_map.mp hliteral
    obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hvertex
    simp only [Nat.one_mul] at hvertex hliteral ⊢
    have hlower : 1 ≤ 1 + offset := by omega
    have hupper : 1 + offset < 43 := by omega
    by_cases hred : 1 + offset ≤ 20
    · rw [show canonicalRootUnit (1 + offset) =
          positiveEdgeLiteral 43 0 (1 + offset) by
        simp [canonicalRootUnit, hred]]
      apply (positiveEdgeUnit_iff (canonicalUnitRelabeling data)
        43 0 (1 + offset)).2
      rw [canonicalUnitRelabeling_root_edge data (1 + offset) hlower hupper]
      exact root_edge_at_label data (1 + offset) hlower hred
    · rw [show canonicalRootUnit (1 + offset) =
          negativeEdgeLiteral 43 0 (1 + offset) by
        simp [canonicalRootUnit, hred]]
      apply (negativeEdgeUnit_iff (canonicalUnitRelabeling data)
        43 0 (1 + offset)).2
      rw [canonicalUnitRelabeling_root_edge data (1 + offset) hlower hupper]
      exact root_edge_false_at_label data (1 + offset) (by omega) hupper
  · intro literal hliteral
    obtain ⟨vertex, hvertex, rfl⟩ := List.mem_map.mp hliteral
    obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hvertex
    simp only [Nat.one_mul] at hvertex hliteral ⊢
    have hlower : 2 ≤ 2 + offset := by omega
    have hupper : 2 + offset ≤ 20 := by omega
    by_cases hred : 2 + offset ≤ 11
    · rw [show canonicalAnchorUnit (2 + offset) =
          positiveEdgeLiteral 43 1 (2 + offset) by
        simp [canonicalAnchorUnit, hred]]
      apply (positiveEdgeUnit_iff (canonicalUnitRelabeling data)
        43 1 (2 + offset)).2
      rw [canonicalUnitRelabeling_anchor_edge data (2 + offset) hlower hupper]
      exact anchor_edge_at_label data (2 + offset) hlower hred
    · rw [show canonicalAnchorUnit (2 + offset) =
          negativeEdgeLiteral 43 1 (2 + offset) by
        simp [canonicalAnchorUnit, hred]]
      apply (negativeEdgeUnit_iff (canonicalUnitRelabeling data)
        43 1 (2 + offset)).2
      rw [canonicalUnitRelabeling_anchor_edge data (2 + offset) hlower hupper]
      exact anchor_edge_false_at_label data (2 + offset) (by omega) hupper

/-- Requested WLOG entry point.  The only hypotheses are the local facts
stored by `LocalD20C10Witness`: an in-range root of red degree 20, an anchor
among its red neighbours, and root/anchor red codegree 10.  Lean constructs
both the vertex permutation and a recoloring satisfying the 61 canonical
DIMACS units. -/
theorem LocalD20C10Witness.canonical_relabeling_units
    {coloring : Nat → Bool} (witness : LocalD20C10Witness coloring) :
    CanonicalD20C10Units
      (canonicalUnitRelabeling witness.toExactLists) :=
  canonicalUnitRelabeling_units witness.toExactLists

theorem LocalD20C10Witness.canonical_vertex_permutation
    {coloring : Nat → Bool} (witness : LocalD20C10Witness coloring) :
    Function.Injective (vertexAt witness.toExactLists) ∧
      Function.Surjective (vertexAt witness.toExactLists) :=
  vertexAt_bijective witness.toExactLists

/-- Combined, proof-carrying WLOG package: a genuine permutation and the
canonical 61-unit recoloring produced from the local witness alone. -/
theorem LocalD20C10Witness.has_canonical_relabeling
    {coloring : Nat → Bool} (witness : LocalD20C10Witness coloring) :
    (Function.Injective (vertexAt witness.toExactLists) ∧
      Function.Surjective (vertexAt witness.toExactLists)) ∧
    CanonicalD20C10Units
      (canonicalUnitRelabeling witness.toExactLists) :=
  ⟨LocalD20C10Witness.canonical_vertex_permutation witness,
    LocalD20C10Witness.canonical_relabeling_units witness⟩

theorem LocalD20C10Witness.canonical_relabeling_preserves_ramseyFree
    {coloring : Nat → Bool} (witness : LocalD20C10Witness coloring) :
    isRamseyFree 43 5 5 coloring ↔
      isRamseyFree 43 5 5
        (canonicalUnitRelabeling witness.toExactLists) :=
  canonicalUnitRelabeling_ramseyFree_iff witness.toExactLists

/-- End-to-end local WLOG result used by the next SAT bridge: a Ramsey-free
coloring with a degree-20/codegree-10 witness is transformed into another
Ramsey-free coloring satisfying all 61 canonical units. -/
theorem LocalD20C10Witness.canonical_ramseyFree_and_units
    {coloring : Nat → Bool} (witness : LocalD20C10Witness coloring)
    (hfree : isRamseyFree 43 5 5 coloring) :
    isRamseyFree 43 5 5
        (canonicalUnitRelabeling witness.toExactLists) ∧
      CanonicalD20C10Units
        (canonicalUnitRelabeling witness.toExactLists) := by
  exact ⟨(LocalD20C10Witness.canonical_relabeling_preserves_ramseyFree witness).mp
      hfree,
    LocalD20C10Witness.canonical_relabeling_units witness⟩

/-- The relabelled canonical branch immediately enters the already certified
order-ten catalogue bridge. -/
theorem LocalD20C10Witness.canonical_relabeling_covered_by_orderTenCatalogue
    {coloring : Nat → Bool} (witness : LocalD20C10Witness coloring)
    (hfree : isRamseyFree 43 5 5 coloring) :
    let units := canonicalUnitRelabeling_units witness.toExactLists
    ∃ representative,
      representative ∈ LRATCatcher.Tests.R35.catalogues.getD 10 [] ∧
      LRATCatcher.Tests.R35.GraphIsomorphicFin
        (inducedGraph units.toLocalWitness.toExactLists) representative := by
  dsimp only
  have hcanonical :=
    LocalD20C10Witness.canonical_ramseyFree_and_units witness hfree
  exact CanonicalD20C10Units.covered_by_orderTenCatalogue
    hcanonical.1 (canonicalUnitRelabeling_units witness.toExactLists)

end CanonicalRelabeling

end LRATCatcher.Tests.R55
