import LRATCatcher.Tests.R45DegreeEightBridge

/-!
  # Global block permutations for the degree-eight `R(4,5,25)` branch

  This module is deliberately independent of the SAT leaves.  It packages a
  root, an eight-vertex block, and a sixteen-vertex block which partition
  `Fin 25`, then conjugates arbitrary permutations of the two local blocks to
  a genuine ambient `FinPermutation 25` fixing the root.
-/

namespace LRATCatcher.Tests.R45DegreeEightGlobalPermutation

open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeEightBridge

/-- Coordinates for a rooted `1 + 8 + 16` partition. -/
inductive RootedBlockCoordinate where
  | root
  | red (index : Fin 8)
  | blue (index : Fin 16)
  deriving DecidableEq

/-- Abstract data needed to assemble block-diagonal permutations of
`Fin 25`.  The final field states that the three displayed pieces cover the
ambient vertices. -/
structure RootedEightSixteenPartition where
  root : Fin 25
  redVertex : Fin 8 → Fin 25
  blueVertex : Fin 16 → Fin 25
  redInjective : Function.Injective redVertex
  blueInjective : Function.Injective blueVertex
  root_ne_red : ∀ index, root ≠ redVertex index
  root_ne_blue : ∀ index, root ≠ blueVertex index
  red_ne_blue : ∀ redIndex blueIndex,
    redVertex redIndex ≠ blueVertex blueIndex
  exhaustive : ∀ vertex,
    vertex = root ∨
      (∃ index, vertex = redVertex index) ∨
      ∃ index, vertex = blueVertex index

/-- Interpret a rooted block coordinate as an ambient vertex. -/
def coordinateVertex (partition : RootedEightSixteenPartition) :
    RootedBlockCoordinate → Fin 25
  | .root => partition.root
  | .red index => partition.redVertex index
  | .blue index => partition.blueVertex index

theorem coordinateVertex_injective
    (partition : RootedEightSixteenPartition) :
    Function.Injective (coordinateVertex partition) := by
  intro left right hequal
  cases left with
  | root =>
      cases right with
      | root => rfl
      | red index => exact (partition.root_ne_red index hequal).elim
      | blue index => exact (partition.root_ne_blue index hequal).elim
  | red leftIndex =>
      cases right with
      | root => exact (partition.root_ne_red leftIndex hequal.symm).elim
      | red rightIndex =>
          exact congrArg RootedBlockCoordinate.red
            (partition.redInjective hequal)
      | blue rightIndex =>
          exact (partition.red_ne_blue leftIndex rightIndex hequal).elim
  | blue leftIndex =>
      cases right with
      | root => exact (partition.root_ne_blue leftIndex hequal.symm).elim
      | red rightIndex =>
          exact (partition.red_ne_blue rightIndex leftIndex hequal.symm).elim
      | blue rightIndex =>
          exact congrArg RootedBlockCoordinate.blue
            (partition.blueInjective hequal)

theorem coordinateVertex_surjective
    (partition : RootedEightSixteenPartition) :
    Function.Surjective (coordinateVertex partition) := by
  intro vertex
  rcases partition.exhaustive vertex with hroot | hred | hblue
  · exact ⟨.root, hroot.symm⟩
  · obtain ⟨index, hindex⟩ := hred
    exact ⟨.red index, hindex.symm⟩
  · obtain ⟨index, hindex⟩ := hblue
    exact ⟨.blue index, hindex.symm⟩

/-- The unique rooted-block coordinate of an ambient vertex. -/
noncomputable def coordinateOf (partition : RootedEightSixteenPartition)
    (vertex : Fin 25) : RootedBlockCoordinate :=
  Classical.choose (coordinateVertex_surjective partition vertex)

@[simp] theorem coordinateVertex_coordinateOf
    (partition : RootedEightSixteenPartition) (vertex : Fin 25) :
    coordinateVertex partition (coordinateOf partition vertex) = vertex :=
  Classical.choose_spec (coordinateVertex_surjective partition vertex)

@[simp] theorem coordinateOf_coordinateVertex
    (partition : RootedEightSixteenPartition)
    (coordinate : RootedBlockCoordinate) :
    coordinateOf partition (coordinateVertex partition coordinate) =
      coordinate := by
  apply coordinateVertex_injective partition
  exact coordinateVertex_coordinateOf partition _

/-- Apply the two local permutations without mixing the rooted blocks. -/
def permuteCoordinate (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    RootedBlockCoordinate → RootedBlockCoordinate
  | .root => .root
  | .red index => .red (redPermutation index)
  | .blue index => .blue (bluePermutation index)

@[simp] theorem permuteCoordinate_symm_apply
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16)
    (coordinate : RootedBlockCoordinate) :
    permuteCoordinate redPermutation.symm bluePermutation.symm
        (permuteCoordinate redPermutation bluePermutation coordinate) =
      coordinate := by
  cases coordinate <;> simp [permuteCoordinate]

@[simp] theorem permuteCoordinate_apply_symm
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16)
    (coordinate : RootedBlockCoordinate) :
    permuteCoordinate redPermutation bluePermutation
        (permuteCoordinate redPermutation.symm bluePermutation.symm coordinate) =
      coordinate := by
  cases coordinate <;> simp [permuteCoordinate]

/-- Ambient action obtained by decoding a vertex, permuting inside its local
block, and encoding it again. -/
noncomputable def blockDiagonalVertex
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (vertex : Fin 25) : Fin 25 :=
  coordinateVertex partition
    (permuteCoordinate redPermutation bluePermutation
      (coordinateOf partition vertex))

@[simp] theorem blockDiagonalVertex_root
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    blockDiagonalVertex partition redPermutation bluePermutation
      partition.root = partition.root := by
  change blockDiagonalVertex partition redPermutation bluePermutation
    (coordinateVertex partition .root) = coordinateVertex partition .root
  simp [blockDiagonalVertex, permuteCoordinate]

@[simp] theorem blockDiagonalVertex_red
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 8) :
    blockDiagonalVertex partition redPermutation bluePermutation
      (partition.redVertex index) =
        partition.redVertex (redPermutation index) := by
  change blockDiagonalVertex partition redPermutation bluePermutation
    (coordinateVertex partition (.red index)) =
      coordinateVertex partition (.red (redPermutation index))
  simp [blockDiagonalVertex, permuteCoordinate]

@[simp] theorem blockDiagonalVertex_blue
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 16) :
    blockDiagonalVertex partition redPermutation bluePermutation
      (partition.blueVertex index) =
        partition.blueVertex (bluePermutation index) := by
  change blockDiagonalVertex partition redPermutation bluePermutation
    (coordinateVertex partition (.blue index)) =
      coordinateVertex partition (.blue (bluePermutation index))
  simp [blockDiagonalVertex, permuteCoordinate]

private theorem blockDiagonalVertex_left_inverse
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (vertex : Fin 25) :
    blockDiagonalVertex partition redPermutation.symm bluePermutation.symm
        (blockDiagonalVertex partition redPermutation bluePermutation vertex) =
      vertex := by
  unfold blockDiagonalVertex
  rw [coordinateOf_coordinateVertex, permuteCoordinate_symm_apply,
    coordinateVertex_coordinateOf]

private theorem blockDiagonalVertex_right_inverse
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (vertex : Fin 25) :
    blockDiagonalVertex partition redPermutation bluePermutation
        (blockDiagonalVertex partition redPermutation.symm
          bluePermutation.symm vertex) = vertex := by
  unfold blockDiagonalVertex
  rw [coordinateOf_coordinateVertex, permuteCoordinate_apply_symm,
    coordinateVertex_coordinateOf]

/-- Genuine ambient block-diagonal permutation. -/
noncomputable def blockDiagonalPermutation
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) : FinPermutation 25 where
  toFun := blockDiagonalVertex partition redPermutation bluePermutation
  invFun := blockDiagonalVertex partition redPermutation.symm
    bluePermutation.symm
  left_inv := blockDiagonalVertex_left_inverse partition
    redPermutation bluePermutation
  right_inv := blockDiagonalVertex_right_inverse partition
    redPermutation bluePermutation

@[simp] theorem blockDiagonalPermutation_root
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    blockDiagonalPermutation partition redPermutation bluePermutation
      partition.root = partition.root :=
  blockDiagonalVertex_root partition redPermutation bluePermutation

@[simp] theorem blockDiagonalPermutation_red
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 8) :
    blockDiagonalPermutation partition redPermutation bluePermutation
      (partition.redVertex index) =
        partition.redVertex (redPermutation index) :=
  blockDiagonalVertex_red partition redPermutation bluePermutation index

@[simp] theorem blockDiagonalPermutation_blue
    (partition : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 16) :
    blockDiagonalPermutation partition redPermutation bluePermutation
      (partition.blueVertex index) =
        partition.blueVertex (bluePermutation index) :=
  blockDiagonalVertex_blue partition redPermutation bluePermutation index

/-! ## Transport between two rooted partitions -/

/-- Relabel an ambient vertex from `source` coordinates to `target`
coordinates, while independently permuting the two non-root blocks. -/
noncomputable def transportVertex
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (vertex : Fin 25) : Fin 25 :=
  coordinateVertex target
    (permuteCoordinate redPermutation bluePermutation
      (coordinateOf source vertex))

@[simp] theorem transportVertex_root
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    transportVertex source target redPermutation bluePermutation
      source.root = target.root := by
  change transportVertex source target redPermutation bluePermutation
    (coordinateVertex source .root) = coordinateVertex target .root
  simp [transportVertex, permuteCoordinate]

@[simp] theorem transportVertex_red
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 8) :
    transportVertex source target redPermutation bluePermutation
      (source.redVertex index) =
        target.redVertex (redPermutation index) := by
  change transportVertex source target redPermutation bluePermutation
    (coordinateVertex source (.red index)) =
      coordinateVertex target (.red (redPermutation index))
  simp [transportVertex, permuteCoordinate]

@[simp] theorem transportVertex_blue
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 16) :
    transportVertex source target redPermutation bluePermutation
      (source.blueVertex index) =
        target.blueVertex (bluePermutation index) := by
  change transportVertex source target redPermutation bluePermutation
    (coordinateVertex source (.blue index)) =
      coordinateVertex target (.blue (bluePermutation index))
  simp [transportVertex, permuteCoordinate]

private theorem transportVertex_left_inverse
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (vertex : Fin 25) :
    transportVertex target source redPermutation.symm bluePermutation.symm
        (transportVertex source target redPermutation bluePermutation vertex) =
      vertex := by
  unfold transportVertex
  rw [coordinateOf_coordinateVertex, permuteCoordinate_symm_apply,
    coordinateVertex_coordinateOf]

private theorem transportVertex_right_inverse
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (vertex : Fin 25) :
    transportVertex source target redPermutation bluePermutation
        (transportVertex target source redPermutation.symm
          bluePermutation.symm vertex) = vertex := by
  unfold transportVertex
  rw [coordinateOf_coordinateVertex, permuteCoordinate_apply_symm,
    coordinateVertex_coordinateOf]

/-- A genuine permutation transporting `source` to `target`. Its inverse
transports `target` back to `source` using the inverse local permutations. -/
noncomputable def transportPermutation
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) : FinPermutation 25 where
  toFun := transportVertex source target redPermutation bluePermutation
  invFun := transportVertex target source redPermutation.symm
    bluePermutation.symm
  left_inv := transportVertex_left_inverse source target
    redPermutation bluePermutation
  right_inv := transportVertex_right_inverse source target
    redPermutation bluePermutation

@[simp] theorem transportPermutation_root
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    transportPermutation source target redPermutation bluePermutation
      source.root = target.root :=
  transportVertex_root source target redPermutation bluePermutation

@[simp] theorem transportPermutation_red
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 8) :
    transportPermutation source target redPermutation bluePermutation
      (source.redVertex index) =
        target.redVertex (redPermutation index) :=
  transportVertex_red source target redPermutation bluePermutation index

@[simp] theorem transportPermutation_blue
    (source target : RootedEightSixteenPartition)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 16) :
    transportPermutation source target redPermutation bluePermutation
      (source.blueVertex index) =
        target.blueVertex (bluePermutation index) :=
  transportVertex_blue source target redPermutation bluePermutation index

/-! ## Canonical and degree-eight partitions -/

/-- The SAT convention `root = 0`, red block `1, ..., 8`, blue block
`9, ..., 24`. -/
def canonicalDegreeEightPartition : RootedEightSixteenPartition where
  root := ⟨0, by omega⟩
  redVertex := fun index => ⟨index.val + 1, by omega⟩
  blueVertex := fun index => ⟨index.val + 9, by omega⟩
  redInjective := by
    intro left right hequal
    apply Fin.ext
    have hvalues := congrArg Fin.val hequal
    simp only [Fin.val_mk] at hvalues
    omega
  blueInjective := by
    intro left right hequal
    apply Fin.ext
    have hvalues := congrArg Fin.val hequal
    simp only [Fin.val_mk] at hvalues
    omega
  root_ne_red := by
    intro index hequal
    have hvalues := congrArg Fin.val hequal
    simp only [Fin.val_mk] at hvalues
    omega
  root_ne_blue := by
    intro index hequal
    have hvalues := congrArg Fin.val hequal
    simp only [Fin.val_mk] at hvalues
    omega
  red_ne_blue := by
    intro redIndex blueIndex hequal
    have hvalues := congrArg Fin.val hequal
    simp only [Fin.val_mk] at hvalues
    omega
  exhaustive := by
    intro vertex
    by_cases hzero : vertex.val = 0
    · left
      apply Fin.ext
      exact hzero
    by_cases hred : vertex.val < 9
    · right
      left
      let index : Fin 8 := ⟨vertex.val - 1, by omega⟩
      refine ⟨index, ?_⟩
      apply Fin.ext
      simp only [Fin.val_mk]
      dsimp [index]
      omega
    · right
      right
      let index : Fin 16 := ⟨vertex.val - 9, by omega⟩
      refine ⟨index, ?_⟩
      apply Fin.ext
      simp only [Fin.val_mk]
      dsimp [index]
      omega

/-- The actual root, its eight red neighbours, and its sixteen blue
neighbours form a rooted partition of `Fin 25`. -/
def degreeEightPartition (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    RootedEightSixteenPartition where
  root := ⟨root, hroot⟩
  redVertex := redDegreeEightEmbedding coloring root hdegree
  blueVertex := blueDegreeSixteenEmbedding coloring root hroot hdegree
  redInjective := redDegreeEightEmbedding_injective coloring root hdegree
  blueInjective := blueDegreeSixteenEmbedding_injective coloring root hroot hdegree
  root_ne_red := by
    intro index hequal
    apply redDegreeEightEmbedding_ne_root coloring root hdegree index
    exact congrArg Fin.val hequal
  root_ne_blue := by
    intro index hequal
    apply blueDegreeSixteenEmbedding_ne_root coloring root hroot hdegree index
    exact congrArg Fin.val hequal
  red_ne_blue := by
    intro redIndex blueIndex hequal
    have hred := redDegreeEightEmbedding_color coloring root hdegree redIndex
    have hvalues := congrArg Fin.val hequal
    rw [hvalues] at hred
    have hblue := blueDegreeSixteenEmbedding_color coloring root hroot
      hdegree blueIndex
    rw [hblue] at hred
    simp at hred
  exhaustive := by
    intro vertex
    by_cases hrootValue : vertex.val = root
    · left
      apply Fin.ext
      exact hrootValue
    cases hedge :
        LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring root
          vertex.val with
    | false =>
        have hmember :
            vertex.val ∈ colorNeighbors coloring root true := by
          exact (mem_colorNeighbors coloring root vertex.val true).mpr
            ⟨vertex.isLt, hrootValue, by simpa using hedge⟩
        obtain ⟨position, hposition, hvalue⟩ :=
          List.getElem_of_mem hmember
        have hposition16 : position < 16 := by
          simpa [blueDegreeSixteen_length coloring root hroot hdegree] using
            hposition
        let index : Fin 16 := ⟨position, hposition16⟩
        right
        right
        refine ⟨index, ?_⟩
        apply Fin.ext
        simpa [blueDegreeSixteenEmbedding, neighborEmbedding,
          chosenNeighbor, index] using hvalue.symm
    | true =>
        have hmember :
            vertex.val ∈ colorNeighbors coloring root false := by
          exact (mem_colorNeighbors coloring root vertex.val false).mpr
            ⟨vertex.isLt, hrootValue, by simpa using hedge⟩
        obtain ⟨position, hposition, hvalue⟩ :=
          List.getElem_of_mem hmember
        have hposition8 : position < 8 := by
          simpa [hdegree] using hposition
        let index : Fin 8 := ⟨position, hposition8⟩
        right
        left
        refine ⟨index, ?_⟩
        apply Fin.ext
        simpa [redDegreeEightEmbedding, neighborEmbedding,
          chosenNeighbor, index] using hvalue.symm

/-- The global SAT relabeling: canonical label `0` goes to `root`, labels
`1, ..., 8` go to the red neighbours, and labels `9, ..., 24` go to the
blue neighbours. -/
noncomputable def degreeEightGlobalPermutation
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) : FinPermutation 25 :=
  transportPermutation canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree)
    redPermutation bluePermutation

@[simp] theorem degreeEightGlobalPermutation_root
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) :
    degreeEightGlobalPermutation coloring root hroot hdegree redPermutation
      bluePermutation ⟨0, by omega⟩ = ⟨root, hroot⟩ := by
  change transportPermutation canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree) redPermutation
      bluePermutation canonicalDegreeEightPartition.root =
        (degreeEightPartition coloring root hroot hdegree).root
  exact transportPermutation_root canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree) redPermutation
      bluePermutation

@[simp] theorem degreeEightGlobalPermutation_red
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 8) :
    degreeEightGlobalPermutation coloring root hroot hdegree redPermutation
        bluePermutation ⟨index.val + 1, by omega⟩ =
      redDegreeEightEmbedding coloring root hdegree
        (redPermutation index) := by
  change transportPermutation canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree) redPermutation
      bluePermutation (canonicalDegreeEightPartition.redVertex index) =
        (degreeEightPartition coloring root hroot hdegree).redVertex
          (redPermutation index)
  exact transportPermutation_red canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree) redPermutation
      bluePermutation index

@[simp] theorem degreeEightGlobalPermutation_blue
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (redPermutation : FinPermutation 8)
    (bluePermutation : FinPermutation 16) (index : Fin 16) :
    degreeEightGlobalPermutation coloring root hroot hdegree redPermutation
        bluePermutation ⟨index.val + 9, by omega⟩ =
      blueDegreeSixteenEmbedding coloring root hroot hdegree
        (bluePermutation index) := by
  change transportPermutation canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree) redPermutation
      bluePermutation (canonicalDegreeEightPartition.blueVertex index) =
        (degreeEightPartition coloring root hroot hdegree).blueVertex
          (bluePermutation index)
  exact transportPermutation_blue canonicalDegreeEightPartition
    (degreeEightPartition coloring root hroot hdegree) redPermutation
      bluePermutation index

#print axioms degreeEightPartition
#print axioms degreeEightGlobalPermutation
#print axioms degreeEightGlobalPermutation_root
#print axioms degreeEightGlobalPermutation_red
#print axioms degreeEightGlobalPermutation_blue
#print axioms transportPermutation
#print axioms transportPermutation_root
#print axioms transportPermutation_red
#print axioms transportPermutation_blue
#print axioms blockDiagonalPermutation
#print axioms blockDiagonalPermutation_root
#print axioms blockDiagonalPermutation_red
#print axioms blockDiagonalPermutation_blue

end LRATCatcher.Tests.R45DegreeEightGlobalPermutation
