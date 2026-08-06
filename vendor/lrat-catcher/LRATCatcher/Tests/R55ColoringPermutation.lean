import LRATCatcher.Tests.R55CommonNeighborhoodBridge

/-!
  Invariance of the semantic `R(5,5)` predicate under a permutation of the
  43 vertices.

  The Ramsey encoding stores only upper-triangle edge variables.  We decode
  such a variable back to its endpoints, transport those endpoints through a
  genuine permutation of `Fin 43`, and read the original symmetric
  `ramseyEdge` relation.  The final theorem says that this relabelling
  preserves and reflects `isRamseyFree 43 5 5`.
-/

namespace LRATCatcher.Tests.R55

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35

namespace ColoringPermutation

abbrev Vertex := Fin 43

/-- Upper-triangle pairs, in exactly the row-major order used by `edgeVar`. -/
def edgePairs : List (Vertex × Vertex) :=
  (List.finRange 43).flatMap fun left =>
    (List.finRange 43).filterMap fun right =>
      if left < right then some (left, right) else none

/-- Decode an edge-variable index.  The default is irrelevant on the 903
actual edge variables, and makes the transported coloring total on `Nat`. -/
def edgePair (index : Nat) : Vertex × Vertex :=
  edgePairs.getD index (0, 0)

/-- The finite, executable round-trip fact connecting the semantic decoder
to the arithmetic `edgeVar` used by the Ramsey CNF. -/
theorem edgePair_edgeVar (left right : Vertex) (hordered : left < right) :
    edgePair (edgeVar 43 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Relabel an ambient natural-number vertex inside `Fin 43`; values outside
the ambient graph are deliberately left fixed. -/
def relabelVertex (permutation : FinPermutation 43) (vertex : Nat) : Nat :=
  if hbound : vertex < 43 then
    (permutation ⟨vertex, hbound⟩).val
  else
    vertex

@[simp] theorem relabelVertex_of_lt (permutation : FinPermutation 43)
    {vertex : Nat} (hbound : vertex < 43) :
    relabelVertex permutation vertex = (permutation ⟨vertex, hbound⟩).val := by
  simp [relabelVertex, hbound]

theorem relabelVertex_lt (permutation : FinPermutation 43)
    {vertex : Nat} (hbound : vertex < 43) :
    relabelVertex permutation vertex < 43 := by
  rw [relabelVertex_of_lt permutation hbound]
  exact (permutation ⟨vertex, hbound⟩).isLt

theorem relabelVertex_injective (permutation : FinPermutation 43) :
    Function.Injective (relabelVertex permutation) := by
  intro left right hequal
  by_cases hleft : left < 43
  · by_cases hright : right < 43
    · have hfin :
          permutation ⟨left, hleft⟩ = permutation ⟨right, hright⟩ := by
        apply Fin.ext
        simpa [relabelVertex, hleft, hright] using hequal
      exact congrArg Fin.val (permutation.injective hfin)
    · have houtputLeft : relabelVertex permutation left < 43 :=
        relabelVertex_lt permutation hleft
      have houtputRight : relabelVertex permutation right = right := by
        simp [relabelVertex, hright]
      omega
  · by_cases hright : right < 43
    · have houtputLeft : relabelVertex permutation left = left := by
        simp [relabelVertex, hleft]
      have houtputRight : relabelVertex permutation right < 43 :=
        relabelVertex_lt permutation hright
      omega
    · simpa [relabelVertex, hleft, hright] using hequal

theorem relabelVertex_symm_left (permutation : FinPermutation 43)
    {vertex : Nat} (hbound : vertex < 43) :
    relabelVertex permutation
        (relabelVertex permutation.symm vertex) = vertex := by
  have hinverseBound : relabelVertex permutation.symm vertex < 43 :=
    relabelVertex_lt permutation.symm hbound
  rw [relabelVertex_of_lt permutation hinverseBound]
  have hinner :
      (⟨relabelVertex permutation.symm vertex, hinverseBound⟩ : Vertex) =
        permutation.symm ⟨vertex, hbound⟩ := by
    apply Fin.ext
    exact relabelVertex_of_lt permutation.symm hbound
  rw [hinner, FinPermutation.apply_symm_apply]

/-- Pull the original coloring back along a vertex permutation. -/
def permuteColoring (permutation : FinPermutation 43)
    (coloring : Nat → Bool) (index : Nat) : Bool :=
  let endpoints := edgePair index
  ramseyEdge 43 coloring
    (permutation endpoints.1).val (permutation endpoints.2).val

theorem permuteColoring_edgeVar (permutation : FinPermutation 43)
    (coloring : Nat → Bool) (left right : Vertex) (hordered : left < right) :
    permuteColoring permutation coloring (edgeVar 43 left.val right.val) =
      ramseyEdge 43 coloring
        (permutation left).val (permutation right).val := by
  simp [permuteColoring, edgePair_edgeVar left right hordered]

theorem ramseyEdge_permuteColoring (permutation : FinPermutation 43)
    (coloring : Nat → Bool) (left right : Vertex) :
    ramseyEdge 43 (permuteColoring permutation coloring) left.val right.val =
      ramseyEdge 43 coloring
        (permutation left).val (permutation right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simp [ramseyEdge, hordered,
      permuteColoring_edgeVar permutation coloring left right hordered]
  · have : left = right := Fin.ext hequal
    subst right
    simp
  · have hreverseNat : right.val < left.val := hreverse
    rw [ramseyEdge_comm 43 (permuteColoring permutation coloring) left.val right.val]
    rw [show ramseyEdge 43 (permuteColoring permutation coloring)
        right.val left.val =
          permuteColoring permutation coloring
            (edgeVar 43 right.val left.val) by
      simp [ramseyEdge, hreverseNat]]
    rw [permuteColoring_edgeVar permutation coloring right left hreverse]
    exact ramseyEdge_comm 43 coloring _ _

/-- A monochromatic-clique exclusion is preserved by pulling a coloring back
along a permutation.  Stating the common red/blue argument once keeps the
final Ramsey theorem small and makes the orientation reversal explicit. -/
theorem noMonochromaticClique_permute_forward
    (permutation : FinPermutation 43) (coloring : Nat → Bool)
    (target : Bool) (size : Nat)
    (hfree : ∀ vertices : List Nat,
      vertices.length = size →
      (∀ vertex ∈ vertices, vertex < 43) →
      vertices.Nodup →
      ¬(∀ left right,
        left ∈ vertices → right ∈ vertices → left < right →
        coloring (edgeVar 43 left right) = target)) :
    ∀ vertices : List Nat,
      vertices.length = size →
      (∀ vertex ∈ vertices, vertex < 43) →
      vertices.Nodup →
      ¬(∀ left right,
        left ∈ vertices → right ∈ vertices → left < right →
        permuteColoring permutation coloring (edgeVar 43 left right) = target) := by
  intro vertices hlength hbound hnodup hmonochromatic
  let mapped := vertices.map (relabelVertex permutation)
  have hmappedLength : mapped.length = size := by
    simp [mapped, hlength]
  have hmappedBound : ∀ vertex ∈ mapped, vertex < 43 := by
    intro vertex hvertex
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hvertex
    exact relabelVertex_lt permutation (hbound original horiginal)
  have hmappedNodup : mapped.Nodup := by
    exact hnodup.map (relabelVertex permutation)
      (fun left right hne hequal =>
        hne (relabelVertex_injective permutation hequal))
  apply hfree mapped hmappedLength hmappedBound hmappedNodup
  intro left right hleft hright hordered
  obtain ⟨originalLeft, horiginalLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨originalRight, horiginalRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound : originalLeft < 43 :=
    hbound originalLeft horiginalLeft
  have hrightBound : originalRight < 43 :=
    hbound originalRight horiginalRight
  have hne : originalLeft ≠ originalRight := by
    intro hequal
    subst originalRight
    omega
  by_cases horiginalOrder : originalLeft < originalRight
  · have htransported := hmonochromatic originalLeft originalRight
        horiginalLeft horiginalRight horiginalOrder
    rw [permuteColoring_edgeVar permutation coloring
      ⟨originalLeft, hleftBound⟩ ⟨originalRight, hrightBound⟩
      horiginalOrder] at htransported
    have hedge :
        ramseyEdge 43 coloring
          (relabelVertex permutation originalLeft)
          (relabelVertex permutation originalRight) = target := by
      simpa [relabelVertex, hleftBound, hrightBound] using htransported
    simpa [ramseyEdge, hordered] using hedge
  · have hreverse : originalRight < originalLeft := by omega
    have htransported := hmonochromatic originalRight originalLeft
        horiginalRight horiginalLeft hreverse
    rw [permuteColoring_edgeVar permutation coloring
      ⟨originalRight, hrightBound⟩ ⟨originalLeft, hleftBound⟩
      hreverse] at htransported
    have hedgeReverse :
        ramseyEdge 43 coloring
          (relabelVertex permutation originalRight)
          (relabelVertex permutation originalLeft) = target := by
      simpa [relabelVertex, hleftBound, hrightBound] using htransported
    have hedge :
        ramseyEdge 43 coloring
          (relabelVertex permutation originalLeft)
          (relabelVertex permutation originalRight) = target := by
      rw [ramseyEdge_comm]
      exact hedgeReverse
    simpa [ramseyEdge, hordered] using hedge

/-- Both forbidden colors are preserved by a vertex relabelling. -/
theorem isRamseyFree_permute_forward
    (permutation : FinPermutation 43) (coloring : Nat → Bool) :
    isRamseyFree 43 5 5 coloring →
      isRamseyFree 43 5 5 (permuteColoring permutation coloring) := by
  intro hfree
  constructor
  · exact noMonochromaticClique_permute_forward
      permutation coloring true 5 hfree.1
  · exact noMonochromaticClique_permute_forward
      permutation coloring false 5 hfree.2

/-- Pulling back along the inverse permutation after pulling back along the
original one recovers every genuine upper-triangle edge variable. -/
theorem permuteColoring_symm_permuteColoring_edgeVar
    (permutation : FinPermutation 43) (coloring : Nat → Bool)
    (left right : Vertex) (hordered : left < right) :
    permuteColoring permutation.symm
        (permuteColoring permutation coloring)
        (edgeVar 43 left.val right.val) =
      coloring (edgeVar 43 left.val right.val) := by
  rw [permuteColoring_edgeVar permutation.symm
    (permuteColoring permutation coloring) left right hordered]
  rw [ramseyEdge_permuteColoring permutation coloring
    (permutation.symm left) (permutation.symm right)]
  simp only [FinPermutation.apply_symm_apply]
  have horderedNat : left.val < right.val := hordered
  simp [ramseyEdge, horderedNat]

/-- Semantic `R(5,5)`-freeness is exactly invariant under every genuine
permutation of the 43 vertices. -/
theorem isRamseyFree_permute_iff
    (permutation : FinPermutation 43) (coloring : Nat → Bool) :
    isRamseyFree 43 5 5 coloring ↔
      isRamseyFree 43 5 5 (permuteColoring permutation coloring) := by
  constructor
  · exact isRamseyFree_permute_forward permutation coloring
  · intro hpermuted
    have hdouble :
        isRamseyFree 43 5 5
          (permuteColoring permutation.symm
            (permuteColoring permutation coloring)) :=
      isRamseyFree_permute_forward permutation.symm
        (permuteColoring permutation coloring) hpermuted
    constructor
    · intro vertices hlength hbound hnodup hmonochromatic
      apply hdouble.1 vertices hlength hbound hnodup
      intro left right hleft hright hordered
      have hleftBound : left < 43 := hbound left hleft
      have hrightBound : right < 43 := hbound right hright
      rw [permuteColoring_symm_permuteColoring_edgeVar
        permutation coloring ⟨left, hleftBound⟩ ⟨right, hrightBound⟩
        hordered]
      exact hmonochromatic left right hleft hright hordered
    · intro vertices hlength hbound hnodup hmonochromatic
      apply hdouble.2 vertices hlength hbound hnodup
      intro left right hleft hright hordered
      have hleftBound : left < 43 := hbound left hleft
      have hrightBound : right < 43 := hbound right hright
      rw [permuteColoring_symm_permuteColoring_edgeVar
        permutation coloring ⟨left, hleftBound⟩ ⟨right, hrightBound⟩
        hordered]
      exact hmonochromatic left right hleft hright hordered

#print axioms isRamseyFree_permute_iff

end ColoringPermutation

end LRATCatcher.Tests.R55
