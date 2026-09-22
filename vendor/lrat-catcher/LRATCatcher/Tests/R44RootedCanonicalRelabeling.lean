import LRATCatcher.Tests.R44RootedBlockCatalogues
import LRATCatcher.Tests.R44RootedMixedClauses

/-!
  # Global canonical relabeling for rooted `R(4,4,16)` colorings

  A `RootBlockCatalogueWitness` supplies strong isomorphisms from the two
  ordered root blocks to their order-seven and order-eight catalogue
  representatives.  This file assembles their inverse permutations into a
  single permutation of all sixteen vertices, packs the 56 transported cross
  edges into the classifier mask, and proves the resulting global graph
  isomorphism.

  The final isomorphism is directed from the canonical graph to the graph of
  the oriented coloring.  Thus its permutation sends a canonical label
  (`L = 0,...,6`, `A = 7,...,14`, root `= 15`) to the corresponding ambient
  vertex.
-/

namespace LRATCatcher.Tests.R44RootedCanonicalRelabeling

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44RootedDegreeSplit
open LRATCatcher.Tests.R44RootedBlockCatalogues
open LRATCatcher.Tests.R44RootedGen4416Semantics
open LRATCatcher.Tests.R44RootedMixedClauses

abbrev AmbientVertex := Fin 16

/-! ## Reindexing the two catalogue permutations -/

/-- Transport a finite permutation across an equality of its order. -/
def reindexPermutation {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder) :
    FinPermutation targetOrder := by
  subst targetOrder
  exact permutation

@[simp] theorem reindexPermutation_apply_val
    {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder)
    (vertex : Fin targetOrder) :
    (reindexPermutation horder permutation vertex).val =
      (permutation (Fin.cast horder.symm vertex)).val := by
  subst targetOrder
  rfl

@[simp] theorem reindexPermutation_symm_apply_val
    {sourceOrder targetOrder : Nat}
    (horder : sourceOrder = targetOrder)
    (permutation : FinPermutation sourceOrder)
    (vertex : Fin targetOrder) :
    ((reindexPermutation horder permutation).symm vertex).val =
      (permutation.symm (Fin.cast horder.symm vertex)).val := by
  subst targetOrder
  rfl

theorem leftIsomorphism_order_eq
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    data.leftIsomorphism.order = 7 := by
  have hsource := data.leftIsomorphism.sourceOrder
  simpa using hsource.symm

theorem antiIsomorphism_order_eq
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    data.antiIsomorphism.order = 8 := by
  have hsource := data.antiIsomorphism.sourceOrder
  simpa using hsource.symm

/-- Source-to-representative permutation, expressed on the concrete type
`Fin 7`. -/
def leftPermutation {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) : FinPermutation 7 :=
  reindexPermutation (leftIsomorphism_order_eq data)
    data.leftIsomorphism.permutation

/-- Source-to-representative permutation, expressed on the concrete type
`Fin 8`. -/
def antiPermutation {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) : FinPermutation 8 :=
  reindexPermutation (antiIsomorphism_order_eq data)
    data.antiIsomorphism.permutation

theorem leftPermutation_map_edge
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left right : Fin 7) :
    edge (leftInducedGraph coloring data.flip data.leftLength)
        left.val right.val =
      edge (r34Catalogue7.getD data.leftIndex [])
        (leftPermutation data left).val
        (leftPermutation data right).val := by
  let horder := leftIsomorphism_order_eq data
  have hmap := data.leftIsomorphism.map_edge
    (Fin.cast horder.symm left) (Fin.cast horder.symm right)
  simpa [leftPermutation, horder] using hmap

theorem antiPermutation_map_edge
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left right : Fin 8) :
    edge (antiInducedGraph coloring data.flip data.antiLength)
        left.val right.val =
      edge (r34Catalogue8.getD data.antiIndex [])
        (antiPermutation data left).val
        (antiPermutation data right).val := by
  let horder := antiIsomorphism_order_eq data
  have hmap := data.antiIsomorphism.map_edge
    (Fin.cast horder.symm left) (Fin.cast horder.symm right)
  simpa [antiPermutation, horder] using hmap

/-! ## Canonical labels inside the two ambient blocks -/

/-- Ambient vertex carrying a canonical order-seven label. -/
def canonicalLeftVertex {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 7) :
    AmbientVertex :=
  leftVertex coloring data.flip data.leftLength
    ((leftPermutation data).symm label)

/-- Ambient vertex carrying a canonical order-eight label. -/
def canonicalAntiVertex {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 8) :
    AmbientVertex :=
  antiVertex coloring data.flip data.antiLength
    ((antiPermutation data).symm label)

theorem canonicalLeftVertex_injective
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    Function.Injective (canonicalLeftVertex data) := by
  intro left right hequal
  have hsources := leftVertex_injective coloring data.flip data.leftLength
    (by simpa [canonicalLeftVertex] using hequal)
  exact (leftPermutation data).symm.injective hsources

theorem canonicalAntiVertex_injective
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    Function.Injective (canonicalAntiVertex data) := by
  intro left right hequal
  have hsources := antiVertex_injective coloring data.flip data.antiLength
    (by simpa [canonicalAntiVertex] using hequal)
  exact (antiPermutation data).symm.injective hsources

theorem canonicalLeftVertex_mem
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 7) :
    (canonicalLeftVertex data label).val ∈ leftBlock coloring data.flip :=
  by
    simpa [canonicalLeftVertex] using
      leftVertex_mem coloring data.flip data.leftLength
        ((leftPermutation data).symm label)

theorem canonicalAntiVertex_mem
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 8) :
    (canonicalAntiVertex data label).val ∈ antiBlock coloring data.flip :=
  by
    simpa [canonicalAntiVertex] using
      antiVertex_mem coloring data.flip data.antiLength
        ((antiPermutation data).symm label)

theorem canonicalLeftVertex_lt_root
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 7) :
    (canonicalLeftVertex data label).val < root :=
  (mem_trueNeighbors _ _).mp (canonicalLeftVertex_mem data label) |>.1

theorem canonicalAntiVertex_lt_root
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 8) :
    (canonicalAntiVertex data label).val < root :=
  (mem_falseNeighbors _ _).mp (canonicalAntiVertex_mem data label) |>.1

@[simp] theorem canonicalLeftVertex_root_edge
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 7) :
    ramseyEdge 16 (orientedColoring coloring data.flip) root
      (canonicalLeftVertex data label).val = true :=
  (mem_trueNeighbors _ _).mp (canonicalLeftVertex_mem data label) |>.2

@[simp] theorem canonicalAntiVertex_root_edge
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (label : Fin 8) :
    ramseyEdge 16 (orientedColoring coloring data.flip) root
      (canonicalAntiVertex data label).val = false :=
  (mem_falseNeighbors _ _).mp (canonicalAntiVertex_mem data label) |>.2

theorem canonicalLeftVertex_edge
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left right : Fin 7) (hne : left ≠ right) :
    ramseyEdge 16 (orientedColoring coloring data.flip)
        (canonicalLeftVertex data left).val
        (canonicalLeftVertex data right).val =
      edge (r34Catalogue7.getD data.leftIndex []) left.val right.val := by
  let sourceLeft := (leftPermutation data).symm left
  let sourceRight := (leftPermutation data).symm right
  have hsourceNe : sourceLeft ≠ sourceRight := by
    intro hequal
    exact hne ((leftPermutation data).symm.injective hequal)
  rw [canonicalLeftVertex, canonicalLeftVertex]
  rw [← edge_leftInducedGraph coloring data.flip data.leftLength
    sourceLeft sourceRight hsourceNe]
  have hmap := leftPermutation_map_edge data sourceLeft sourceRight
  simpa [sourceLeft, sourceRight] using hmap

theorem canonicalAntiVertex_edge
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left right : Fin 8) (hne : left ≠ right) :
    ramseyEdge 16 (orientedColoring coloring data.flip)
        (canonicalAntiVertex data left).val
        (canonicalAntiVertex data right).val =
      !(edge (r34Catalogue8.getD data.antiIndex []) left.val right.val) := by
  let sourceLeft := (antiPermutation data).symm left
  let sourceRight := (antiPermutation data).symm right
  have hsourceNe : sourceLeft ≠ sourceRight := by
    intro hequal
    exact hne ((antiPermutation data).symm.injective hequal)
  rw [canonicalAntiVertex, canonicalAntiVertex]
  have hlocal := edge_antiInducedGraph coloring data.flip data.antiLength
    sourceLeft sourceRight hsourceNe
  have hmap := antiPermutation_map_edge data sourceLeft sourceRight
  rw [hmap] at hlocal
  simpa [sourceLeft, sourceRight] using (congrArg Bool.not hlocal).symm

/-! ## The exact 56-bit cross-edge mask -/

def crossLeft (bit : Fin 56) : Fin 7 :=
  ⟨bit.val / 8, by omega⟩

def crossAnti (bit : Fin 56) : Fin 8 :=
  ⟨bit.val % 8, Nat.mod_lt _ (by omega)⟩

def crossEdge {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left : Fin 7) (anti : Fin 8) : Bool :=
  ramseyEdge 16 (orientedColoring coloring data.flip)
    (canonicalLeftVertex data left).val
    (canonicalAntiVertex data anti).val

def crossMaskBits {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) : List Bool :=
  List.ofFn fun bit : Fin 56 =>
    crossEdge data (crossLeft bit) (crossAnti bit)

/-- Little-endian packing of the 7 by 8 transported cross-edge matrix. -/
def crossMask {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) : Nat :=
  (BitVec.ofBoolListLE (crossMaskBits data)).toNat

@[simp] theorem crossMaskBits_length
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    (crossMaskBits data).length = 56 := by
  simp [crossMaskBits]

theorem crossMask_lt_two_pow
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    crossMask data < 2 ^ 56 := by
  unfold crossMask
  simpa using (BitVec.ofBoolListLE (crossMaskBits data)).isLt

theorem crossMask_testBit
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (bit : Fin 56) :
    (crossMask data).testBit bit.val =
      crossEdge data (crossLeft bit) (crossAnti bit) := by
  let bits := crossMaskBits data
  have hindex : bit.val < bits.length := by simp [bits]
  unfold crossMask
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD (l := bits) (i := bit.val)
    (h := hindex) false]
  change (crossMaskBits data)[bit.val] = _
  unfold crossMaskBits
  rw [List.getElem_ofFn]

theorem maskBit_eq_testBit (mask bit : Nat) :
    maskBit mask bit = mask.testBit bit := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hbit : mask / 2 ^ bit % 2 = 1 <;> simp [maskBit, hbit]

/-- Exact classifier bit law: bit `8 * left + anti` is precisely the
transported ambient cross edge. -/
@[simp] theorem crossMask_maskBit
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left : Fin 7) (anti : Fin 8) :
    maskBit (crossMask data) (8 * left.val + anti.val) =
      crossEdge data left anti := by
  rw [maskBit_eq_testBit]
  have hbit : 8 * left.val + anti.val < 56 := by omega
  let encoded : Fin 56 := ⟨8 * left.val + anti.val, hbit⟩
  have hleftIndex : (8 * left.val + anti.val) / 8 = left.val := by
    rw [Nat.mul_add_div (by omega) left.val anti.val]
    simp [Nat.div_eq_of_lt anti.isLt]
  have hantiIndex : (8 * left.val + anti.val) % 8 = anti.val := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt anti.isLt
  have hread := crossMask_testBit data encoded
  have hleft : crossLeft encoded = left := by
    apply Fin.ext
    exact hleftIndex
  have hanti : crossAnti encoded = anti := by
    apply Fin.ext
    exact hantiIndex
  simpa [encoded, hleft, hanti] using hread

/-! ## The global permutation of sixteen vertices -/

def vertexAt {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (label : AmbientVertex) : AmbientVertex :=
  if hleft : label.val < 7 then
    canonicalLeftVertex data ⟨label.val, hleft⟩
  else if hanti : label.val < 15 then
    canonicalAntiVertex data ⟨label.val - 7, by omega⟩
  else
    ⟨root, by simp [root]⟩

@[simp] theorem vertexAt_of_lt_seven
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (label : AmbientVertex) (hlabel : label.val < 7) :
    vertexAt data label = canonicalLeftVertex data ⟨label.val, hlabel⟩ := by
  simp [vertexAt, hlabel]

@[simp] theorem vertexAt_of_seven_le_of_lt_fifteen
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (label : AmbientVertex) (hlower : 7 ≤ label.val)
    (hupper : label.val < 15) :
    vertexAt data label =
      canonicalAntiVertex data ⟨label.val - 7, by omega⟩ := by
  simp [vertexAt, show ¬label.val < 7 by omega, hupper]

@[simp] theorem vertexAt_of_eq_root
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (label : AmbientVertex) (hlabel : label.val = root) :
    vertexAt data label = ⟨root, by simp [root]⟩ := by
  have hvalue : label.val = 15 := by simpa [root] using hlabel
  have hnotLeft : ¬label.val < 7 := by omega
  have hnotAnti : ¬label.val < 15 := by omega
  simp [vertexAt, hnotLeft, hnotAnti]

theorem vertexAt_injective
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    Function.Injective (vertexAt data) := by
  intro left right hequal
  by_cases hleftL : left.val < 7
  · by_cases hrightL : right.val < 7
    · rw [vertexAt_of_lt_seven data left hleftL,
          vertexAt_of_lt_seven data right hrightL] at hequal
      have hindices := canonicalLeftVertex_injective data hequal
      apply Fin.ext
      exact congrArg (fun vertex : Fin 7 => vertex.val) hindices
    · by_cases hrightA : right.val < 15
      · rw [vertexAt_of_lt_seven data left hleftL,
            vertexAt_of_seven_le_of_lt_fifteen data right (by omega) hrightA]
            at hequal
        have hred := canonicalLeftVertex_root_edge data ⟨left.val, hleftL⟩
        have hblue := canonicalAntiVertex_root_edge data
          ⟨right.val - 7, by omega⟩
        rw [hequal] at hred
        simp [hblue] at hred
      · rw [vertexAt_of_lt_seven data left hleftL,
            vertexAt_of_eq_root data right (by simp [root]; omega)] at hequal
        have hbound := canonicalLeftVertex_lt_root data ⟨left.val, hleftL⟩
        have hvalues := congrArg Fin.val hequal
        simp [root] at hbound hvalues
        omega
  · by_cases hleftA : left.val < 15
    · by_cases hrightL : right.val < 7
      · rw [vertexAt_of_seven_le_of_lt_fifteen data left (by omega) hleftA,
            vertexAt_of_lt_seven data right hrightL] at hequal
        have hblue := canonicalAntiVertex_root_edge data
          ⟨left.val - 7, by omega⟩
        have hred := canonicalLeftVertex_root_edge data ⟨right.val, hrightL⟩
        rw [hequal] at hblue
        simp [hred] at hblue
      · by_cases hrightA : right.val < 15
        · rw [vertexAt_of_seven_le_of_lt_fifteen data left (by omega) hleftA,
              vertexAt_of_seven_le_of_lt_fifteen data right (by omega) hrightA]
              at hequal
          have hindices := canonicalAntiVertex_injective data hequal
          apply Fin.ext
          have hvalues := congrArg Fin.val hindices
          simp at hvalues
          omega
        · rw [vertexAt_of_seven_le_of_lt_fifteen data left (by omega) hleftA,
              vertexAt_of_eq_root data right (by simp [root]; omega)] at hequal
          have hbound := canonicalAntiVertex_lt_root data
            ⟨left.val - 7, by omega⟩
          have hvalues := congrArg Fin.val hequal
          simp [root] at hbound hvalues
          omega
    · have hleftRoot : left.val = root := by simp [root]; omega
      by_cases hrightL : right.val < 7
      · rw [vertexAt_of_eq_root data left hleftRoot,
            vertexAt_of_lt_seven data right hrightL] at hequal
        have hbound := canonicalLeftVertex_lt_root data ⟨right.val, hrightL⟩
        have hvalues := congrArg Fin.val hequal
        simp [root] at hbound hvalues
        omega
      · by_cases hrightA : right.val < 15
        · rw [vertexAt_of_eq_root data left hleftRoot,
              vertexAt_of_seven_le_of_lt_fifteen data right (by omega) hrightA]
              at hequal
          have hbound := canonicalAntiVertex_lt_root data
            ⟨right.val - 7, by omega⟩
          have hvalues := congrArg Fin.val hequal
          simp [root] at hbound hvalues
          omega
        · apply Fin.ext
          simp [root] at hleftRoot
          have hrightRoot : right.val = 15 := by omega
          omega
theorem vertexAt_surjective
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    Function.Surjective (vertexAt data) := by
  intro target
  by_cases hroot : target.val = root
  · refine ⟨⟨root, by simp [root]⟩, ?_⟩
    rw [vertexAt_of_eq_root data _ rfl]
    exact Fin.ext hroot.symm
  · have htargetLt : target.val < root := by
      have := target.isLt
      simp [root] at hroot ⊢
      omega
    by_cases hedge :
        ramseyEdge 16 (orientedColoring coloring data.flip) root target.val
    · have hmember : target.val ∈ leftBlock coloring data.flip := by
        exact (mem_trueNeighbors _ _).mpr ⟨htargetLt, hedge⟩
      obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hmember
      have hindex7 : index < 7 := by simpa [data.leftLength] using hindex
      let source : Fin 7 := ⟨index, hindex7⟩
      let label : Fin 7 := leftPermutation data source
      let global : Fin 16 := ⟨label.val, Nat.lt_trans label.isLt (by omega)⟩
      refine ⟨global, ?_⟩
      have hglobal : global.val < 7 := by simpa [global] using label.isLt
      rw [vertexAt_of_lt_seven data global hglobal]
      apply Fin.ext
      simpa [global, canonicalLeftVertex, label, source] using hvalue
    · have hedgeFalse :
          ramseyEdge 16 (orientedColoring coloring data.flip) root target.val =
            false := by simpa using hedge
      have hmember : target.val ∈ antiBlock coloring data.flip := by
        exact (mem_falseNeighbors _ _).mpr ⟨htargetLt, hedgeFalse⟩
      obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hmember
      have hindex8 : index < 8 := by simpa [data.antiLength] using hindex
      let source : Fin 8 := ⟨index, hindex8⟩
      let label : Fin 8 := antiPermutation data source
      have hlabelBound : label.val < 8 := label.isLt
      let global : Fin 16 := ⟨7 + label.val, by omega⟩
      refine ⟨global, ?_⟩
      have hglobalLower : 7 ≤ global.val := by simp [global]
      have hglobalUpper : global.val < 15 := by simp [global]; omega
      rw [vertexAt_of_seven_le_of_lt_fifteen data global
        hglobalLower hglobalUpper]
      apply Fin.ext
      simpa [global, canonicalAntiVertex, label, source] using hvalue

/-- Genuine global permutation sending canonical labels to ambient vertices. -/
noncomputable def vertexPermutation
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) : FinPermutation 16 where
  toFun := vertexAt data
  invFun := fun target => Classical.choose (vertexAt_surjective data target)
  left_inv := by
    intro source
    apply vertexAt_injective data
    exact Classical.choose_spec (vertexAt_surjective data (vertexAt data source))
  right_inv := by
    intro target
    exact Classical.choose_spec (vertexAt_surjective data target)

@[simp] theorem vertexPermutation_apply
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) (vertex : AmbientVertex) :
    vertexPermutation data vertex = vertexAt data vertex := rfl

/-! ## Global edge preservation -/

theorem coloringEdge_eq_ramseyEdge
    (order : Nat) (coloring : Nat → Bool) (left right : Nat) :
    coloringEdge order coloring left right =
      ramseyEdge order coloring left right := rfl

theorem canonical_edge_to_oriented_edge_of_lt
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring)
    (left right : AmbientVertex) (hordered : left < right) :
    edge (coloringGraph 16
        (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
        left.val right.val =
      edge (coloringGraph 16 (orientedColoring coloring data.flip))
        (vertexAt data left).val (vertexAt data right).val := by
  rw [edge_coloringGraph, edge_coloringGraph]
  have horderedNat : left.val < right.val := hordered
  rw [show coloringEdge 16
      (canonicalColoring data.leftIndex data.antiIndex (crossMask data))
        left.val right.val =
      canonicalColoring data.leftIndex data.antiIndex (crossMask data)
        (edgeVar 16 left.val right.val) by
    simp [coloringEdge, horderedNat]]
  rw [coloringEdge_eq_ramseyEdge]
  by_cases hrightLeft : right.val < 7
  · have hleftLeft : left.val < 7 := by omega
    let left7 : Fin 7 := ⟨left.val, hleftLeft⟩
    let right7 : Fin 7 := ⟨right.val, hrightLeft⟩
    have hne : left7 ≠ right7 := by
      intro hequal
      have hvalues : left.val = right.val := by
        simpa [left7, right7] using
          congrArg (fun vertex : Fin 7 => vertex.val) hequal
      omega
    rw [canonicalColoring_left_edge _ _ _ _ _ horderedNat hrightLeft]
    rw [vertexAt_of_lt_seven data left hleftLeft,
      vertexAt_of_lt_seven data right hrightLeft]
    simpa [left7, right7] using
      (canonicalLeftVertex_edge data left7 right7 hne).symm
  · by_cases hleftLeft : left.val < 7
    · by_cases hrightAnti : right.val < 15
      · let left7 : Fin 7 := ⟨left.val, hleftLeft⟩
        let right8 : Fin 8 := ⟨right.val - 7, by omega⟩
        have hrightValue : right.val = 7 + right8.val := by
          simp [right8]
          omega
        rw [hrightValue]
        rw [canonicalColoring_cross_edge _ _ _ left7.val right8.val
          left7.isLt right8.isLt]
        rw [vertexAt_of_lt_seven data left hleftLeft,
          vertexAt_of_seven_le_of_lt_fifteen data right (by omega) hrightAnti]
        simpa [crossEdge, left7, right8] using
          (crossMask_maskBit data left7 right8)
      · have hrightRoot : right.val = root := by simp [root]; omega
        have hright15 : right.val = 15 := by simpa [root] using hrightRoot
        rw [hright15]
        rw [canonicalColoring_left_root _ _ _ _ hleftLeft]
        rw [vertexAt_of_lt_seven data left hleftLeft,
          vertexAt_of_eq_root data right hrightRoot]
        rw [ramseyEdge_comm]
        simpa [root] using (canonicalLeftVertex_root_edge data _).symm
    · by_cases hrightAnti : right.val < 15
      · have hleftAnti : left.val < 15 := by omega
        let left8 : Fin 8 := ⟨left.val - 7, by omega⟩
        let right8 : Fin 8 := ⟨right.val - 7, by omega⟩
        have hleftValue : left.val = 7 + left8.val := by
          simp [left8]
          omega
        have hrightValue : right.val = 7 + right8.val := by
          simp [right8]
          omega
        have hantiOrdered : left8 < right8 := by
          change left.val - 7 < right.val - 7
          omega
        have hantiNe : left8 ≠ right8 := by
          intro hequal
          have hvalues : left8.val = right8.val :=
            congrArg (fun vertex : Fin 8 => vertex.val) hequal
          exact (Nat.ne_of_lt hantiOrdered) hvalues
        rw [hleftValue, hrightValue]
        rw [canonicalColoring_anti_edge _ _ _ left8.val right8.val
          hantiOrdered left8.isLt right8.isLt]
        rw [vertexAt_of_seven_le_of_lt_fifteen data left (by omega) hleftAnti,
          vertexAt_of_seven_le_of_lt_fifteen data right (by omega) hrightAnti]
        simpa [left8, right8] using
          (canonicalAntiVertex_edge data left8 right8 hantiNe).symm
      · have hrightRoot : right.val = root := by simp [root]; omega
        have hright15 : right.val = 15 := by simpa [root] using hrightRoot
        have hleftAnti : left.val < 15 := by omega
        let left8 : Fin 8 := ⟨left.val - 7, by omega⟩
        have hleftValue : left.val = 7 + left8.val := by
          simp [left8]
          omega
        rw [hleftValue, hright15]
        rw [canonicalColoring_anti_root _ _ _ left8.val left8.isLt]
        rw [vertexAt_of_seven_le_of_lt_fifteen data left (by omega) hleftAnti,
          vertexAt_of_eq_root data right hrightRoot]
        rw [ramseyEdge_comm]
        simpa [root] using (canonicalAntiVertex_root_edge data _).symm
/-- Global semantic relabeling.  The source is the canonical classifier graph
and the target is the graph of the oriented coloring. -/
noncomputable def canonicalToOrientedGraphIso
    {coloring : Nat → Bool}
    (data : RootBlockCatalogueWitness coloring) :
    GraphIsoFin
      (coloringGraph 16
        (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
      (coloringGraph 16 (orientedColoring coloring data.flip)) := by
  refine {
    order := 16
    sourceOrder := coloringGraph_length 16 _
    targetOrder := coloringGraph_length 16 _
    permutation := vertexPermutation data
    map_edge := ?_
  }
  intro left right
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · exact canonical_edge_to_oriented_edge_of_lt data left right hordered
  · have hvertices : left = right := Fin.ext hequal
    subst right
    rw [edge_coloringGraph, edge_coloringGraph]
    simp
  · calc
      edge (coloringGraph 16
          (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
          left.val right.val =
          edge (coloringGraph 16
            (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
            right.val left.val := by
              rw [edge_coloringGraph, edge_coloringGraph]
              exact coloringEdge_comm 16 _ _ _
      _ = edge (coloringGraph 16 (orientedColoring coloring data.flip))
            (vertexAt data right).val (vertexAt data left).val :=
        canonical_edge_to_oriented_edge_of_lt data right left hreverse
      _ = edge (coloringGraph 16 (orientedColoring coloring data.flip))
            (vertexAt data left).val (vertexAt data right).val := by
              rw [edge_coloringGraph, edge_coloringGraph]
              exact coloringEdge_comm 16 _ _ _

/-- Starting only from the semantic root split, obtain concrete selectors, a
56-bit mask with its exact bit law, and the global strong isomorphism. -/
theorem orientedRootSplit_has_canonical_relabeling
    {coloring : Nat → Bool} (split : OrientedRootSplit coloring) :
    ∃ data : RootBlockCatalogueWitness coloring,
      crossMask data < 2 ^ 56 ∧
      GraphIsomorphicFin
        (coloringGraph 16
          (canonicalColoring data.leftIndex data.antiIndex (crossMask data)))
        (coloringGraph 16 (orientedColoring coloring data.flip)) := by
  obtain ⟨data⟩ := rooted_blocks_enter_catalogues split
  exact ⟨data, crossMask_lt_two_pow data,
    ⟨canonicalToOrientedGraphIso data⟩⟩

#print axioms crossMask_maskBit
#print axioms canonicalToOrientedGraphIso
#print axioms orientedRootSplit_has_canonical_relabeling

end LRATCatcher.Tests.R44RootedCanonicalRelabeling
