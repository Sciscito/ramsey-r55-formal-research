import LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization

/-!
  # Direct cover6 oracle for the degree-seven R(3,4) catalogue

  The first incremental-CNF branch is the graph6 record `FG`Xo`.  In the
  frozen structural catalogue this is representative index one, because the
  incremental order swaps catalogue indices zero and one.  That representative
  is itself one of the six forbidden cover6 motifs, so no SAT certificate is
  needed for this branch: the positive root block on ambient labels `1, ..., 7`
  is already an induced occurrence.
-/

namespace LRATCatcher.Tests.R44Cover6DegreeSevenR34Oracle

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6SemanticComposition
open LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization

/-! ## Frozen orientation audit -/

/-- `FG`Xo` is position zero in the incremental order and position one in the
structural catalogue. -/
theorem r34IcnfOracle_index_orientation :
    r34IndexSwap (0 : Fin 9) = (1 : Fin 9) := by
  native_decide

/-- The representative selected by the oracle's incremental position is
definitionally the decoded cover6 motif `FG`Xo`. -/
theorem r34IcnfOracle_graph_eq_motif :
    r34Catalogue7Representative (r34IndexSwap (0 : Fin 9)) =
      motifFGBacktickXo := by
  native_decide

theorem r34CatalogueOracle_graph_eq_motif :
    r34Catalogue7Representative (1 : Fin 9) = motifFGBacktickXo := by
  simpa only [r34IcnfOracle_index_orientation] using
    r34IcnfOracle_graph_eq_motif

/-! ## The labels `1, ..., 7` as an ambient motif embedding -/

def d7PositiveEmbedding : MotifEmbedding := d7PositiveLabel

theorem d7PositiveEmbedding_injective :
    Function.Injective d7PositiveEmbedding := by
  intro left right hequal
  apply Fin.ext
  have hval := congrArg Fin.val hequal
  simpa [d7PositiveEmbedding, d7PositiveLabel] using hval

@[simp] theorem d7PositiveEmbedding_val (vertex : Fin 7) :
    (d7PositiveEmbedding vertex).val = vertex.val + 1 := by
  rfl

/-! ## Direct semantic closure of the oracle branch -/

/-- Once the positive block has been relabelled to the catalogue
representative at index one, its seven vertices are immediately an induced
`FG`Xo` occurrence.  The embedding is exactly the ambient labels `1, ..., 7`.
-/
theorem d7R34Relabeled_oracle_has_motif
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring (1 : Fin 9)
      sourceToRepresentative) :
    InducedMotifOccurrence 7
      (d7R34RelabeledColoring coloring sourceToRepresentative)
      motifFGBacktickXo := by
  refine Nonempty.intro {
    motif_length := cover6Motif_length (by simp [cover6Motifs])
    embedding := d7PositiveEmbedding
    embedding_injective := d7PositiveEmbedding_injective
    map_edge := ?_
  }
  intro left right
  by_cases hne : left ≠ right
  · calc
      edge motifFGBacktickXo left.val right.val =
          edge (r34Catalogue7Representative (1 : Fin 9))
            left.val right.val := by
          rw [r34CatalogueOracle_graph_eq_motif]
      _ = coloringEdge 12
            (d7R34RelabeledColoring coloring sourceToRepresentative)
            (d7PositiveEmbedding left).val
            (d7PositiveEmbedding right).val := by
          simpa [d7PositiveEmbedding] using
            (d7R34Relabeled_internal_edge coloring (1 : Fin 9)
              sourceToRepresentative hmap left right hne).symm
  · have hequal : left = right := by
      exact Classical.byContradiction (fun hne' => hne hne')
    subst right
    have hwellFormed : wellFormedGraph 7 motifFGBacktickXo = true :=
      cover6Motif_wellFormed (by simp [cover6Motifs])
    rw [wellFormedGraph_loop_false hwellFormed left.isLt]
    exact (coloringEdge_self 12
      (d7R34RelabeledColoring coloring sourceToRepresentative)
      (d7PositiveEmbedding left).val).symm

/-- Index-zero form, aligned with the future `Fin 9` incremental dispatch. -/
theorem d7R34Relabeled_iCNFOracle_has_motif
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring (r34IndexSwap (0 : Fin 9))
      sourceToRepresentative) :
    InducedMotifOccurrence 7
      (d7R34RelabeledColoring coloring sourceToRepresentative)
      motifFGBacktickXo := by
  rw [r34IcnfOracle_index_orientation] at hmap
  exact d7R34Relabeled_oracle_has_motif coloring
    sourceToRepresentative hmap

/-- Consequently the oracle branch is incompatible with the cover6-avoidance
hypothesis used by the global degree-seven dispatch. -/
theorem d7R34Relabeled_oracle_not_avoidsCover6
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring (1 : Fin 9)
      sourceToRepresentative) :
    ¬ (AvoidsCover6
      (d7R34RelabeledColoring coloring sourceToRepresentative)) := by
  intro havoid
  exact havoid motifFGBacktickXo (by simp [cover6Motifs])
    (d7R34Relabeled_oracle_has_motif coloring sourceToRepresentative hmap)

/-- Transporting the direct occurrence back through the structural
relabeling closes the same oracle branch in the original coloring. -/
theorem d7R34_oracle_has_motif
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring (1 : Fin 9)
      sourceToRepresentative) :
    InducedMotifOccurrence 7 coloring motifFGBacktickXo := by
  exact (d7R34Relabeled_inducedMotifOccurrence_iff coloring
    sourceToRepresentative motifFGBacktickXo).mpr
      (d7R34Relabeled_oracle_has_motif coloring
        sourceToRepresentative hmap)

#print axioms r34IcnfOracle_index_orientation
#print axioms r34IcnfOracle_graph_eq_motif
#print axioms r34CatalogueOracle_graph_eq_motif
#print axioms d7PositiveEmbedding_injective
#print axioms d7R34Relabeled_oracle_has_motif
#print axioms d7R34Relabeled_iCNFOracle_has_motif
#print axioms d7R34Relabeled_oracle_not_avoidsCover6
#print axioms d7R34_oracle_has_motif

end LRATCatcher.Tests.R44Cover6DegreeSevenR34Oracle
