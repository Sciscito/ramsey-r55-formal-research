import LRATCatcher.Tests.R44OrderTwelveRootSymmetry

/-!
  # Certified transport for the order-twelve root symmetry break

  This module connects the finite 11-bit root pattern to arbitrary Ramsey
  colorings, proves the ten prefix clauses, and transports both `R(4,4)`
  freeness and labelled induced-motif occurrences.
-/

namespace LRATCatcher.Tests.R44OrderTwelveRootSymmetry

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44Gen4416Classification

theorem sortedLabels_getD_nonRoot (pattern : RootPattern)
    (position : Fin 11) :
    (sortedLabels pattern).getD (position.val + 1) 12 =
      ((sortedNonRoot pattern).getD position.val 0).val + 1 := by
  native_decide +revert

theorem sortedNonRoot_prefix (pattern : RootPattern) (position : Fin 10) :
    patternColor pattern
        ((sortedNonRoot pattern).getD position.val 0) = true ∨
      patternColor pattern
        ((sortedNonRoot pattern).getD (position.val + 1) 0) = false := by
  native_decide +revert

/-- The permutation maps each new label to the corresponding old label in
the root-color-sorted list. -/
noncomputable def rootSortPermutationForPattern
    (pattern : RootPattern) : FinPermutation 12 :=
  listPermutationToFin (sortedLabels pattern) 12
    (sortedLabels_isPermutation pattern)

@[simp] theorem rootSortPermutationForPattern_zero (pattern : RootPattern) :
    rootSortPermutationForPattern pattern (0 : Vertex) = (0 : Vertex) := by
  apply Fin.ext
  change
    (listPermutationToFin (sortedLabels pattern) 12
      (sortedLabels_isPermutation pattern) (0 : Vertex)).val = 0
  rw [listPermutationToFin_apply_val]
  simp [sortedLabels]

theorem rootSortPermutationForPattern_nonRoot_val
    (pattern : RootPattern) (position : Fin 11) :
    (rootSortPermutationForPattern pattern
      ⟨position.val + 1, by omega⟩).val =
        ((sortedNonRoot pattern).getD position.val 0).val + 1 := by
  rw [rootSortPermutationForPattern, listPermutationToFin_apply_val]
  exact sortedLabels_getD_nonRoot pattern position

/-! ## Connecting the finite pattern to an arbitrary coloring -/

def rootPatternBits (coloring : Nat -> Bool) : List Bool :=
  List.ofFn fun vertex : Fin 11 =>
    coloringEdge 12 coloring 0 (vertex.val + 1)

def rootPattern (coloring : Nat -> Bool) : RootPattern :=
  BitVec.cast (by simp [rootPatternBits])
    (BitVec.ofBoolListLE (rootPatternBits coloring))

theorem patternColor_rootPattern (coloring : Nat -> Bool)
    (vertex : Fin 11) :
    patternColor (rootPattern coloring) vertex =
      coloringEdge 12 coloring 0 (vertex.val + 1) := by
  unfold patternColor rootPattern
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := rootPatternBits coloring) (i := vertex.val)
    (h := by simp [rootPatternBits]) false]
  change
    (List.ofFn fun vertex : Fin 11 =>
      coloringEdge 12 coloring 0 (vertex.val + 1))[vertex.val] = _
  rw [List.getElem_ofFn]

/-- Canonical root-fixing permutation selected from the eleven incident
edge colors of an arbitrary coloring. -/
noncomputable def rootSortPermutation
    (coloring : Nat -> Bool) : FinPermutation 12 :=
  rootSortPermutationForPattern (rootPattern coloring)

@[simp] theorem rootSortPermutation_zero (coloring : Nat -> Bool) :
    rootSortPermutation coloring (0 : Vertex) = (0 : Vertex) :=
  rootSortPermutationForPattern_zero (rootPattern coloring)

theorem rootSortPermutation_nonRoot_val (coloring : Nat -> Bool)
    (position : Fin 11) :
    (rootSortPermutation coloring
      ⟨position.val + 1, by omega⟩).val =
        ((sortedNonRoot (rootPattern coloring)).getD position.val 0).val + 1 :=
  rootSortPermutationForPattern_nonRoot_val (rootPattern coloring) position

/-- Semantic prefix monotonicity of the eleven root edges. -/
theorem rootSort_prefix (coloring : Nat -> Bool) (position : Fin 10) :
    coloringEdge 12
        (permuteColoring (rootSortPermutation coloring) coloring)
        0 (position.val + 1) = true ∨
      coloringEdge 12
        (permuteColoring (rootSortPermutation coloring) coloring)
        0 (position.val + 2) = false := by
  let left : Fin 11 := ⟨position.val, by omega⟩
  let right : Fin 11 := ⟨position.val + 1, by omega⟩
  have hpref := sortedNonRoot_prefix (rootPattern coloring) position
  rw [patternColor_rootPattern coloring
        ((sortedNonRoot (rootPattern coloring)).getD position.val 0),
      patternColor_rootPattern coloring
        ((sortedNonRoot (rootPattern coloring)).getD
          (position.val + 1) 0)] at hpref
  have hleft := coloringEdge_permuteColoring
    (rootSortPermutation coloring) coloring (0 : Vertex)
      ⟨position.val + 1, by omega⟩
  have hright := coloringEdge_permuteColoring
    (rootSortPermutation coloring) coloring (0 : Vertex)
      ⟨position.val + 2, by omega⟩
  rw [rootSortPermutation_zero,
      rootSortPermutation_nonRoot_val coloring left] at hleft
  rw [rootSortPermutation_zero,
      rootSortPermutation_nonRoot_val coloring right] at hright
  exact Or.imp (fun hedge => hleft.trans hedge)
    (fun hedge => hright.trans hedge) hpref

/-- Exact SAT-clause presentation: `x(0,i) ∨ ¬x(0,i+1)` for the ten
adjacent non-root positions. -/
theorem rootSort_sat_clause (coloring : Nat -> Bool) (position : Fin 10) :
    permuteColoring (rootSortPermutation coloring) coloring
        (edgeVar 12 0 (position.val + 1)) = true ∨
      permuteColoring (rootSortPermutation coloring) coloring
        (edgeVar 12 0 (position.val + 2)) = false := by
  simpa [coloringEdge, show 0 < position.val + 1 by omega,
    show 0 < position.val + 2 by omega] using
      rootSort_prefix coloring position

/-! ## Ramsey-freeness transport through packed graphs -/

def coloringGraphPermutationIso (permutation : FinPermutation 12)
    (coloring : Nat -> Bool) :
    GraphIsoFin
      (coloringGraph 12 (permuteColoring permutation coloring))
      (coloringGraph 12 coloring) where
  order := 12
  sourceOrder := coloringGraph_length 12 _
  targetOrder := coloringGraph_length 12 _
  permutation := permutation
  map_edge := by
    intro left right
    rw [edge_coloringGraph, edge_coloringGraph]
    exact coloringEdge_permuteColoring permutation coloring left right

theorem isRamseyFree_permute_iff (permutation : FinPermutation 12)
    (coloring : Nat -> Bool) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4 (permuteColoring permutation coloring) := by
  constructor
  · intro hfree
    apply isRamseyFree_of_coloringGraph_r44_validAt 12
    exact r44GraphValidAt_of_graphIsoFin
      (coloringGraphPermutationIso permutation coloring).symm
      (coloringGraph_wellFormed 12 _)
      (coloringGraph_r44_validAt 12 coloring hfree)
  · intro hfree
    apply isRamseyFree_of_coloringGraph_r44_validAt 12
    exact r44GraphValidAt_of_graphIsoFin
      (coloringGraphPermutationIso permutation coloring)
      (coloringGraph_wellFormed 12 _)
      (coloringGraph_r44_validAt 12
        (permuteColoring permutation coloring) hfree)

theorem rootSort_isRamseyFree_iff (coloring : Nat -> Bool) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4
        (permuteColoring (rootSortPermutation coloring) coloring) :=
  isRamseyFree_permute_iff (rootSortPermutation coloring) coloring

/-! ## Induced motif occurrence transport -/

/-- A labelled induced occurrence of a packed motif inside a twelve-vertex
coloring.  Equality is required for every ordered pair, so both edges and
non-edges are preserved. -/
structure InducedMotifOccurrenceWitness (motifOrder : Nat)
    (coloring : Nat -> Bool) (motif : Graph) where
  motif_length : motif.length = motifOrder
  embedding : Fin motifOrder -> Vertex
  embedding_injective : Function.Injective embedding
  map_edge : ∀ left right : Fin motifOrder,
    edge motif left.val right.val =
      coloringEdge 12 coloring
        (embedding left).val (embedding right).val

def InducedMotifOccurrence (motifOrder : Nat)
    (coloring : Nat -> Bool) (motif : Graph) : Prop :=
  Nonempty (InducedMotifOccurrenceWitness motifOrder coloring motif)

theorem inducedMotifOccurrence_permute_forward
    {motifOrder : Nat} {coloring : Nat -> Bool} {motif : Graph}
    (permutation : FinPermutation 12)
    (occurrence : InducedMotifOccurrence motifOrder coloring motif) :
    InducedMotifOccurrence motifOrder
      (permuteColoring permutation coloring) motif := by
  obtain ⟨occurrence⟩ := occurrence
  refine ⟨⟨occurrence.motif_length,
    fun vertex => permutation.symm (occurrence.embedding vertex), ?_, ?_⟩⟩
  · intro left right hequal
    exact occurrence.embedding_injective
      (FinPermutation.injective permutation.symm hequal)
  · intro left right
    calc
      edge motif left.val right.val =
          coloringEdge 12 coloring
            (occurrence.embedding left).val
            (occurrence.embedding right).val := occurrence.map_edge left right
      _ = coloringEdge 12 (permuteColoring permutation coloring)
            (permutation.symm (occurrence.embedding left)).val
            (permutation.symm (occurrence.embedding right)).val := by
          simpa using (coloringEdge_permuteColoring permutation coloring
            (permutation.symm (occurrence.embedding left))
            (permutation.symm (occurrence.embedding right))).symm

theorem inducedMotifOccurrence_permute_backward
    {motifOrder : Nat} {coloring : Nat -> Bool} {motif : Graph}
    (permutation : FinPermutation 12)
    (occurrence : InducedMotifOccurrence motifOrder
      (permuteColoring permutation coloring) motif) :
    InducedMotifOccurrence motifOrder coloring motif := by
  obtain ⟨occurrence⟩ := occurrence
  refine ⟨⟨occurrence.motif_length,
    fun vertex => permutation (occurrence.embedding vertex), ?_, ?_⟩⟩
  · intro left right hequal
    exact occurrence.embedding_injective
      (FinPermutation.injective permutation hequal)
  · intro left right
    calc
      edge motif left.val right.val =
          coloringEdge 12 (permuteColoring permutation coloring)
            (occurrence.embedding left).val
            (occurrence.embedding right).val := occurrence.map_edge left right
      _ = coloringEdge 12 coloring
            (permutation (occurrence.embedding left)).val
            (permutation (occurrence.embedding right)).val :=
          coloringEdge_permuteColoring permutation coloring
            (occurrence.embedding left) (occurrence.embedding right)

theorem inducedMotifOccurrence_permute_iff
    {motifOrder : Nat} (permutation : FinPermutation 12)
    (coloring : Nat -> Bool) (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (permuteColoring permutation coloring) motif :=
  ⟨inducedMotifOccurrence_permute_forward permutation,
    inducedMotifOccurrence_permute_backward permutation⟩

/-- Complete symmetry-breaking package for an arbitrary coloring and motif. -/
theorem exists_root_prefix_permutation
    (coloring : Nat -> Bool) (motifOrder : Nat) (motif : Graph) :
    ∃ permutation : FinPermutation 12,
      permutation (0 : Vertex) = 0 ∧
      (∀ position : Fin 10,
        permuteColoring permutation coloring
            (edgeVar 12 0 (position.val + 1)) = true ∨
          permuteColoring permutation coloring
            (edgeVar 12 0 (position.val + 2)) = false) ∧
      (isRamseyFree 12 4 4 coloring ↔
        isRamseyFree 12 4 4 (permuteColoring permutation coloring)) ∧
      (InducedMotifOccurrence motifOrder coloring motif ↔
        InducedMotifOccurrence motifOrder
          (permuteColoring permutation coloring) motif) := by
  refine ⟨rootSortPermutation coloring, rootSortPermutation_zero coloring,
    rootSort_sat_clause coloring, rootSort_isRamseyFree_iff coloring, ?_⟩
  exact inducedMotifOccurrence_permute_iff
    (rootSortPermutation coloring) coloring motif

#print axioms sortedLabels_isPermutation
#print axioms rootSortPermutation
#print axioms rootSort_sat_clause
#print axioms isRamseyFree_permute_iff
#print axioms inducedMotifOccurrence_permute_iff
#print axioms exists_root_prefix_permutation

end LRATCatcher.Tests.R44OrderTwelveRootSymmetry
