import LRATCatcher.Tests.R45DegreeTwelveBridge

/-!
  # Global permutations for the degree-twelve `R(4,5,25)` branch

  The SAT convention fixes the root at ambient label zero and orders its
  twelve red neighbours before its twelve blue neighbours.  This module
  builds the genuine permutation of `Fin 25` realizing that convention,
  while allowing independent relabelings inside the two order-twelve
  blocks.

  The construction is factored through a rooted `1 + 24` partition.  This
  keeps the global transport independent of the SAT leaves and makes the
  only degree-twelve-specific ingredient the block-diagonal permutation of
  `Fin 24`.
-/

namespace LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation

open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45RootDegreeCore
open LRATCatcher.Tests.R45DegreeTwelveBridge

/-! ## Rooted `1 + 24` transport -/

inductive RootedNonRootCoordinate where
  | root
  | nonRoot (index : Fin 24)
  deriving DecidableEq

/-- A root and an ordered list of all other ambient vertices. -/
structure RootedNonRootPartition where
  root : Fin 25
  nonRootVertex : Fin 24 → Fin 25
  nonRootInjective : Function.Injective nonRootVertex
  root_ne_nonRoot : ∀ index, root ≠ nonRootVertex index
  exhaustive : ∀ vertex,
    vertex = root ∨ ∃ index, vertex = nonRootVertex index

def coordinateVertex (partition : RootedNonRootPartition) :
    RootedNonRootCoordinate → Fin 25
  | .root => partition.root
  | .nonRoot index => partition.nonRootVertex index

theorem coordinateVertex_injective (partition : RootedNonRootPartition) :
    Function.Injective (coordinateVertex partition) := by
  intro left right hequal
  cases left with
  | root =>
      cases right with
      | root => rfl
      | nonRoot index => exact (partition.root_ne_nonRoot index hequal).elim
  | nonRoot leftIndex =>
      cases right with
      | root =>
          exact (partition.root_ne_nonRoot leftIndex hequal.symm).elim
      | nonRoot rightIndex =>
          exact congrArg RootedNonRootCoordinate.nonRoot
            (partition.nonRootInjective hequal)

theorem coordinateVertex_surjective (partition : RootedNonRootPartition) :
    Function.Surjective (coordinateVertex partition) := by
  intro vertex
  rcases partition.exhaustive vertex with hroot | hnonRoot
  · exact ⟨.root, hroot.symm⟩
  · obtain ⟨index, hindex⟩ := hnonRoot
    exact ⟨.nonRoot index, hindex.symm⟩

noncomputable def coordinateOf (partition : RootedNonRootPartition)
    (vertex : Fin 25) : RootedNonRootCoordinate :=
  Classical.choose (coordinateVertex_surjective partition vertex)

@[simp] theorem coordinateVertex_coordinateOf
    (partition : RootedNonRootPartition) (vertex : Fin 25) :
    coordinateVertex partition (coordinateOf partition vertex) = vertex :=
  Classical.choose_spec (coordinateVertex_surjective partition vertex)

@[simp] theorem coordinateOf_coordinateVertex
    (partition : RootedNonRootPartition)
    (coordinate : RootedNonRootCoordinate) :
    coordinateOf partition (coordinateVertex partition coordinate) =
      coordinate := by
  apply coordinateVertex_injective partition
  exact coordinateVertex_coordinateOf partition _

def permuteCoordinate (permutation : FinPermutation 24) :
    RootedNonRootCoordinate → RootedNonRootCoordinate
  | .root => .root
  | .nonRoot index => .nonRoot (permutation index)

@[simp] theorem permuteCoordinate_symm_apply
    (permutation : FinPermutation 24)
    (coordinate : RootedNonRootCoordinate) :
    permuteCoordinate permutation.symm
        (permuteCoordinate permutation coordinate) = coordinate := by
  cases coordinate <;> simp [permuteCoordinate]

@[simp] theorem permuteCoordinate_apply_symm
    (permutation : FinPermutation 24)
    (coordinate : RootedNonRootCoordinate) :
    permuteCoordinate permutation
        (permuteCoordinate permutation.symm coordinate) = coordinate := by
  cases coordinate <;> simp [permuteCoordinate]

noncomputable def transportVertex
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) (vertex : Fin 25) : Fin 25 :=
  coordinateVertex target
    (permuteCoordinate permutation (coordinateOf source vertex))

@[simp] theorem transportVertex_root
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) :
    transportVertex source target permutation source.root = target.root := by
  change transportVertex source target permutation
    (coordinateVertex source .root) = coordinateVertex target .root
  simp [transportVertex, permuteCoordinate]

@[simp] theorem transportVertex_nonRoot
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) (index : Fin 24) :
    transportVertex source target permutation (source.nonRootVertex index) =
      target.nonRootVertex (permutation index) := by
  change transportVertex source target permutation
    (coordinateVertex source (.nonRoot index)) =
      coordinateVertex target (.nonRoot (permutation index))
  simp [transportVertex, permuteCoordinate]

private theorem transportVertex_left_inverse
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) (vertex : Fin 25) :
    transportVertex target source permutation.symm
        (transportVertex source target permutation vertex) = vertex := by
  unfold transportVertex
  rw [coordinateOf_coordinateVertex, permuteCoordinate_symm_apply,
    coordinateVertex_coordinateOf]

private theorem transportVertex_right_inverse
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) (vertex : Fin 25) :
    transportVertex source target permutation
        (transportVertex target source permutation.symm vertex) = vertex := by
  unfold transportVertex
  rw [coordinateOf_coordinateVertex, permuteCoordinate_apply_symm,
    coordinateVertex_coordinateOf]

/-- The ambient permutation transporting one rooted partition to another. -/
noncomputable def transportPermutation
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) : FinPermutation 25 where
  toFun := transportVertex source target permutation
  invFun := transportVertex target source permutation.symm
  left_inv := transportVertex_left_inverse source target permutation
  right_inv := transportVertex_right_inverse source target permutation

@[simp] theorem transportPermutation_root
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) :
    transportPermutation source target permutation source.root = target.root :=
  transportVertex_root source target permutation

@[simp] theorem transportPermutation_nonRoot
    (source target : RootedNonRootPartition)
    (permutation : FinPermutation 24) (index : Fin 24) :
    transportPermutation source target permutation
        (source.nonRootVertex index) =
      target.nonRootVertex (permutation index) :=
  transportVertex_nonRoot source target permutation index

/-! ## Independent permutations of the two twelve-vertex blocks -/

def blockVertex (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 24) : Fin 24 :=
  if hred : index.val < 12 then
    ⟨(redPermutation ⟨index.val, hred⟩).val, by omega⟩
  else
    ⟨(bluePermutation ⟨index.val - 12, by omega⟩).val + 12, by omega⟩

private theorem blockVertex_left_inverse
    (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 24) :
    blockVertex redPermutation.symm bluePermutation.symm
        (blockVertex redPermutation bluePermutation index) = index := by
  apply Fin.ext
  by_cases hred : index.val < 12
  · simp [blockVertex, hred]
  · have hblue : ¬
        (bluePermutation ⟨index.val - 12, by omega⟩).val + 12 < 12 := by
      omega
    simp [blockVertex, hred, hblue]
    omega

private theorem blockVertex_right_inverse
    (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 24) :
    blockVertex redPermutation bluePermutation
        (blockVertex redPermutation.symm bluePermutation.symm index) = index := by
  apply Fin.ext
  by_cases hred : index.val < 12
  · simp [blockVertex, hred]
  · have hblue : ¬
        (bluePermutation.symm ⟨index.val - 12, by omega⟩).val + 12 < 12 := by
      omega
    simp [blockVertex, hred, hblue]
    omega

/-- Block-diagonal permutation of the 24 non-root SAT labels. -/
def blockPermutation (redPermutation bluePermutation : FinPermutation 12) :
    FinPermutation 24 where
  toFun := blockVertex redPermutation bluePermutation
  invFun := blockVertex redPermutation.symm bluePermutation.symm
  left_inv := blockVertex_left_inverse redPermutation bluePermutation
  right_inv := blockVertex_right_inverse redPermutation bluePermutation

@[simp] theorem blockPermutation_red
    (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 12) :
    blockPermutation redPermutation bluePermutation
        ⟨index.val, by omega⟩ =
      ⟨(redPermutation index).val, by omega⟩ := by
  apply Fin.ext
  simp [blockPermutation, blockVertex]

@[simp] theorem blockPermutation_blue
    (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 12) :
    blockPermutation redPermutation bluePermutation
        ⟨index.val + 12, by omega⟩ =
      ⟨(bluePermutation index).val + 12, by omega⟩ := by
  apply Fin.ext
  have hnot : ¬ index.val + 12 < 12 := by omega
  simp [blockPermutation, blockVertex, hnot]

/-! ## Canonical and neighborhood partitions -/

def canonicalDegreeTwelvePartition : RootedNonRootPartition where
  root := ⟨0, by omega⟩
  nonRootVertex := canonicalNonRootVertex
  nonRootInjective := canonicalNonRootVertex_injective
  root_ne_nonRoot := by
    intro index hequal
    have hvalues := congrArg Fin.val hequal
    simp [canonicalNonRootVertex] at hvalues
  exhaustive := by
    intro vertex
    by_cases hzero : vertex.val = 0
    · left
      apply Fin.ext
      exact hzero
    · right
      let index : Fin 24 := ⟨vertex.val - 1, by omega⟩
      refine ⟨index, ?_⟩
      apply Fin.ext
      simp [canonicalNonRootVertex, index]
      omega

/-- The actual root followed by its canonical red-neighbor and blue-neighbor
enumerations. -/
def degreeTwelvePartition (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    RootedNonRootPartition where
  root := ⟨root, hroot⟩
  nonRootVertex :=
    degreeTwelveNonRootEmbedding coloring root hroot hdegree
  nonRootInjective :=
    degreeTwelveNonRootEmbedding_injective coloring root hroot hdegree
  root_ne_nonRoot := by
    intro index hequal
    apply degreeTwelveNonRootEmbedding_ne_root coloring root hroot hdegree index
    exact congrArg Fin.val hequal
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
        have hposition12 : position < 12 := by
          simpa [blueDegreeTwelve_length coloring root hroot hdegree] using
            hposition
        let index : Fin 12 := ⟨position, hposition12⟩
        right
        refine ⟨⟨index.val + 12, by omega⟩, ?_⟩
        rw [degreeTwelveNonRootEmbedding_blue]
        apply Fin.ext
        simpa [blueDegreeTwelveEmbedding, blueNeighborEmbedding,
          neighborEmbedding, chosenNeighbor, index] using hvalue.symm
    | true =>
        have hmember :
            vertex.val ∈ colorNeighbors coloring root false := by
          exact (mem_colorNeighbors coloring root vertex.val false).mpr
            ⟨vertex.isLt, hrootValue, by simpa using hedge⟩
        obtain ⟨position, hposition, hvalue⟩ :=
          List.getElem_of_mem hmember
        have hposition12 : position < 12 := by
          simpa [hdegree] using hposition
        let index : Fin 12 := ⟨position, hposition12⟩
        right
        refine ⟨⟨index.val, by omega⟩, ?_⟩
        rw [degreeTwelveNonRootEmbedding_red]
        apply Fin.ext
        simpa [redDegreeTwelveEmbedding, redNeighborEmbedding,
          neighborEmbedding, chosenNeighbor, index] using hvalue.symm

/-- Global relabeling sending canonical root/red/blue labels to the actual
rooted coloring, with independent local permutations in both blocks. -/
noncomputable def degreeTwelveGlobalPermutation
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation bluePermutation : FinPermutation 12) :
    FinPermutation 25 :=
  transportPermutation canonicalDegreeTwelvePartition
    (degreeTwelvePartition coloring root hroot hdegree)
    (blockPermutation redPermutation bluePermutation)

@[simp] theorem degreeTwelveGlobalPermutation_root
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation bluePermutation : FinPermutation 12) :
    degreeTwelveGlobalPermutation coloring root hroot hdegree
        redPermutation bluePermutation ⟨0, by omega⟩ =
      ⟨root, hroot⟩ := by
  change transportPermutation canonicalDegreeTwelvePartition
    (degreeTwelvePartition coloring root hroot hdegree)
      (blockPermutation redPermutation bluePermutation)
      canonicalDegreeTwelvePartition.root =
        (degreeTwelvePartition coloring root hroot hdegree).root
  exact transportPermutation_root canonicalDegreeTwelvePartition
    (degreeTwelvePartition coloring root hroot hdegree)
      (blockPermutation redPermutation bluePermutation)

@[simp] theorem degreeTwelveGlobalPermutation_red
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 12) :
    degreeTwelveGlobalPermutation coloring root hroot hdegree
        redPermutation bluePermutation ⟨index.val + 1, by omega⟩ =
      redDegreeTwelveEmbedding coloring root hdegree
        (redPermutation index) := by
  change transportPermutation canonicalDegreeTwelvePartition
    (degreeTwelvePartition coloring root hroot hdegree)
      (blockPermutation redPermutation bluePermutation)
      (canonicalDegreeTwelvePartition.nonRootVertex
        ⟨index.val, by omega⟩) =
        redDegreeTwelveEmbedding coloring root hdegree
          (redPermutation index)
  rw [transportPermutation_nonRoot, blockPermutation_red]
  change degreeTwelveNonRootEmbedding coloring root hroot hdegree
      ⟨(redPermutation index).val, by omega⟩ =
    redDegreeTwelveEmbedding coloring root hdegree (redPermutation index)
  exact degreeTwelveNonRootEmbedding_red coloring root hroot hdegree
    (redPermutation index)

@[simp] theorem degreeTwelveGlobalPermutation_blue
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation bluePermutation : FinPermutation 12)
    (index : Fin 12) :
    degreeTwelveGlobalPermutation coloring root hroot hdegree
        redPermutation bluePermutation ⟨index.val + 13, by omega⟩ =
      blueDegreeTwelveEmbedding coloring root hroot hdegree
        (bluePermutation index) := by
  change transportPermutation canonicalDegreeTwelvePartition
    (degreeTwelvePartition coloring root hroot hdegree)
      (blockPermutation redPermutation bluePermutation)
      (canonicalDegreeTwelvePartition.nonRootVertex
        ⟨index.val + 12, by omega⟩) =
        blueDegreeTwelveEmbedding coloring root hroot hdegree
          (bluePermutation index)
  rw [transportPermutation_nonRoot, blockPermutation_blue]
  change degreeTwelveNonRootEmbedding coloring root hroot hdegree
      ⟨(bluePermutation index).val + 12, by omega⟩ =
    blueDegreeTwelveEmbedding coloring root hroot hdegree
      (bluePermutation index)
  exact degreeTwelveNonRootEmbedding_blue coloring root hroot hdegree
    (bluePermutation index)

#print axioms blockPermutation
#print axioms degreeTwelvePartition
#print axioms degreeTwelveGlobalPermutation
#print axioms degreeTwelveGlobalPermutation_root
#print axioms degreeTwelveGlobalPermutation_red
#print axioms degreeTwelveGlobalPermutation_blue

end LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation
