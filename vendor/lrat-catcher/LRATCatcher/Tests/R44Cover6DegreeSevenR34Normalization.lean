import LRATCatcher.Tests.R44Cover6DegreeSevenMinCenter
import LRATCatcher.Tests.R44Cover6DegreeSevenNormalization
import LRATCatcher.Tests.R44RootedBlockCatalogues
import LRATCatcher.Tests.R44Cover6SemanticComposition
import LRATCatcher.Tests.R55CanonicalUnitsBridge

/-!
  # Structural R(3,4) normalization of the degree-seven root block

  This module contains no SAT result.  It joins the certified low-centre
  theorem, the purely structural degree-seven normalization, and the certified
  nine-element order-seven R(3,4) catalogue.  The local catalogue isomorphism
  points from the source graph to its representative; consequently the ambient
  pullback uses its inverse permutation.
-/

namespace LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44OrderTwelveTwoCenterCases
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedBlockCatalogues
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6SemanticComposition
open LRATCatcher.Tests.R55.CanonicalUnits

abbrev AmbientVertex := Fin 12

/-! ## Direct bridge from `MinCenter` to the structural normalization -/

theorem d7InternalDegree_eq_minCenter
    (coloring : Nat -> Bool) (center : Fin 7) :
    R44Cover6DegreeSevenNormalization.d7NormalizedInternalDegree
        coloring center =
      R44Cover6DegreeSevenMinCenter.normalizedDegreeSevenInternalDegree
        coloring center := by
  unfold R44Cover6DegreeSevenNormalization.d7NormalizedInternalDegree
    R44Cover6DegreeSevenMinCenter.normalizedDegreeSevenInternalDegree
  rfl

theorem degreeSeven_lowCenterExists
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    R44Cover6DegreeSevenNormalization.D7LowCenterExists coloring := by
  obtain ⟨center, hlower, hupper⟩ :=
    R44Cover6DegreeSevenMinCenter.degreeSeven_has_internal_degree_one_or_two
      coloring hfree hdegree
  refine ⟨center, ?_, ?_⟩
  · rwa [d7InternalDegree_eq_minCenter]
  · rwa [d7InternalDegree_eq_minCenter]

noncomputable def degreeSevenChosenNormalizedColoring
    (coloring : Nat -> Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) : Nat -> Bool :=
  R44Cover6DegreeSevenNormalization.d7ChosenNormalizedColoring coloring
    (degreeSeven_lowCenterExists hfree hdegree)

theorem degreeSevenChosenNormalized_isRamseyFree
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    isRamseyFree 12 4 4
      (degreeSevenChosenNormalizedColoring coloring hfree hdegree) := by
  exact (R44Cover6DegreeSevenNormalization.d7ChosenNormalized_isRamseyFree_iff
      coloring
      (degreeSeven_lowCenterExists hfree hdegree)).mp hfree

theorem degreeSevenChosenNormalized_avoidsCover6_iff
    (coloring : Nat -> Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    AvoidsCover6 coloring ↔
      AvoidsCover6
        (degreeSevenChosenNormalizedColoring coloring hfree hdegree) := by
  constructor
  · intro havoid motif hmotif hoccurrence
    exact havoid motif hmotif
      ((R44Cover6DegreeSevenNormalization.d7ChosenNormalized_inducedMotifOccurrence_iff
          coloring
          (degreeSeven_lowCenterExists hfree hdegree) motif).mpr hoccurrence)
  · intro havoid motif hmotif hoccurrence
    exact havoid motif hmotif
      ((R44Cover6DegreeSevenNormalization.d7ChosenNormalized_inducedMotifOccurrence_iff
          coloring
          (degreeSeven_lowCenterExists hfree hdegree) motif).mp hoccurrence)

theorem degreeSevenChosenNormalized_enters_nine_cases
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    let hexists := degreeSeven_lowCenterExists hfree hdegree
    R44Cover6DegreeSevenNormalization.D7NineCases
        (R44Cover6DegreeSevenNormalization.d7PValue coloring
          (R44Cover6DegreeSevenNormalization.d7ChosenCenter coloring hexists))
        (R44Cover6DegreeSevenNormalization.d7QValue coloring
          (R44Cover6DegreeSevenNormalization.d7ChosenCenter coloring hexists)) ∧
      R44Cover6DegreeSevenNormalization.D7TwoCenterBranch
        (degreeSevenChosenNormalizedColoring coloring hfree hdegree)
        (R44Cover6DegreeSevenNormalization.d7PValue coloring
          (R44Cover6DegreeSevenNormalization.d7ChosenCenter coloring hexists))
        (R44Cover6DegreeSevenNormalization.d7QValue coloring
          (R44Cover6DegreeSevenNormalization.d7ChosenCenter coloring hexists)) := by
  simpa [degreeSevenChosenNormalizedColoring] using
    R44Cover6DegreeSevenNormalization.d7ChosenNormalized_enters_nine_cases
        hfree hdegree
        (degreeSeven_lowCenterExists hfree hdegree)

theorem degreeSevenChosenNormalized_satisfies_exact_nine_clauses
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7)
    (position : Fin 9) :
    CNF.Clause.eval
        (degreeSevenChosenNormalizedColoring coloring hfree hdegree)
        (R44Cover6DegreeSevenNormalization.d7DimacsClause
          (R44Cover6DegreeSevenNormalization.d7ExtraDimacsClauses.getD
            position.val [])) = true := by
  simpa [degreeSevenChosenNormalizedColoring] using
    R44Cover6DegreeSevenNormalization.d7ChosenNormalized_satisfies_exact_nine_clauses
        hfree hdegree
        (degreeSeven_lowCenterExists hfree hdegree) position

/-! ## Frozen catalogue identity and incremental-CNF order -/

def r34Catalogue7Graph6Records : List String :=
  ["FCUj_", "FG`Xo", "FK`Xo", "F_GZ_", "F`AZO",
    "F`GOW", "FoDPO", "FoDPW", "FqOxo"]

def r34IcnfGraph6Records : List String :=
  ["FG`Xo", "FCUj_", "FK`Xo", "F_GZ_", "F`AZO",
    "F`GOW", "FoDPO", "FoDPW", "FqOxo"]

theorem r34Catalogue7_eq_frozen_records :
    r34Catalogue7 = r34Catalogue7Graph6Records.map decodeGraph6Seven := by
  native_decide

theorem r34Catalogue7Graph6Records_length :
    r34Catalogue7Graph6Records.length = 9 := by native_decide

theorem r34IcnfGraph6Records_length :
    r34IcnfGraph6Records.length = 9 := by native_decide

/-- The unique nontrivial order change: the incremental formula moves the
shared cover6 oracle from catalogue position one to position zero. -/
def r34IndexSwap (index : Fin 9) : Fin 9 :=
  if index = 0 then 1 else if index = 1 then 0 else index

theorem r34IndexSwap_values :
    (List.ofFn r34IndexSwap).map (fun index => index.val) =
      [1, 0, 2, 3, 4, 5, 6, 7, 8] := by
  native_decide

@[simp] theorem r34IndexSwap_involutive (index : Fin 9) :
    r34IndexSwap (r34IndexSwap index) = index := by
  native_decide +revert

theorem r34IcnfRecord_eq_catalogueRecord (index : Fin 9) :
    r34IcnfGraph6Records.getD index.val "" =
      r34Catalogue7Graph6Records.getD (r34IndexSwap index).val "" := by
  native_decide +revert

theorem r34CatalogueRecord_eq_iCNFRecord (index : Fin 9) :
    r34Catalogue7Graph6Records.getD index.val "" =
      r34IcnfGraph6Records.getD (r34IndexSwap index).val "" := by
  simpa using
    (r34IcnfRecord_eq_catalogueRecord (r34IndexSwap index)).symm

def r34Catalogue7Representative (index : Fin 9) : Graph :=
  decodeGraph6Seven
    (r34Catalogue7Graph6Records.getD index.val "")

theorem r34Catalogue7Representative_eq_catalogue (index : Fin 9) :
    r34Catalogue7Representative index =
      r34Catalogue7.getD index.val [] := by
  native_decide +revert

theorem r34IcnfGraph_eq_catalogueGraph (index : Fin 9) :
    decodeGraph6Seven (r34IcnfGraph6Records.getD index.val "") =
      r34Catalogue7Representative (r34IndexSwap index) := by
  native_decide +revert

theorem r34CatalogueGraph_eq_iCNFGraph (index : Fin 9) :
    r34Catalogue7Representative index =
      decodeGraph6Seven
        (r34IcnfGraph6Records.getD (r34IndexSwap index).val "") := by
  simpa using (r34IcnfGraph_eq_catalogueGraph (r34IndexSwap index)).symm

/-! ## Catalogue extraction from the degree-seven pattern -/

noncomputable def degreeSevenPatternGraph (coloring : Nat -> Bool) : Graph :=
  coloringGraph 7
    (R44Cover6DegreeSevenMinCenter.sevenPatternColor
      (R44Cover6DegreeSevenMinCenter.degreeSevenPattern coloring))

theorem degreeSevenPatternGraph_r34_valid
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    R34GraphValidAt 7 (degreeSevenPatternGraph coloring) := by
  exact coloringGraph_r34_validAt 7 _
    (R44Cover6DegreeSevenMinCenter.degreeSevenPattern_isRamseyFree
      hfree hdegree)

theorem degreeSevenPattern_has_catalogueIso
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    ∃ catalogueIndex : Fin 9,
      Nonempty (GraphIsoFin (degreeSevenPatternGraph coloring)
        (r34Catalogue7Representative catalogueIndex)) := by
  obtain ⟨representative, hmember, ⟨isomorphism⟩⟩ :=
    r34_catalogue_seven_complete (degreeSevenPatternGraph coloring)
      (degreeSevenPatternGraph_r34_valid hfree hdegree)
  obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hmember
  have hindexNine : index < 9 := by
    simpa [r34Catalogue7_length_eq_nine] using hindex
  let catalogueIndex : Fin 9 := ⟨index, hindexNine⟩
  have hgetD : r34Catalogue7.getD index [] = representative := by
    rw [← List.getElem_eq_getD (l := r34Catalogue7) (i := index)
      (h := hindex) []]
    exact hget
  have hcatalogueIso : GraphIsoFin (degreeSevenPatternGraph coloring)
      (r34Catalogue7.getD catalogueIndex.val []) := by
    simpa only [catalogueIndex, Fin.val_mk, hgetD] using isomorphism
  have hfrozenIso : GraphIsoFin (degreeSevenPatternGraph coloring)
      (r34Catalogue7Representative catalogueIndex) := by
    rw [r34Catalogue7Representative_eq_catalogue]
    exact hcatalogueIso
  exact ⟨catalogueIndex, ⟨hfrozenIso⟩⟩

def D7R34FixedIsoData
    (coloring : Nat -> Bool) (catalogueIndex : Fin 9)
    (sourceToRepresentative : FinPermutation 7) : Prop :=
  ∀ left right : Fin 7,
    edge (degreeSevenPatternGraph coloring) left.val right.val =
      edge (r34Catalogue7Representative catalogueIndex)
        (sourceToRepresentative left).val
        (sourceToRepresentative right).val

theorem graphIsoFin_seven_has_fixedPermutation
    {coloring : Nat -> Bool} {catalogueIndex : Fin 9}
    (isomorphism : GraphIsoFin (degreeSevenPatternGraph coloring)
      (r34Catalogue7Representative catalogueIndex)) :
    ∃ sourceToRepresentative : FinPermutation 7,
      D7R34FixedIsoData coloring catalogueIndex sourceToRepresentative := by
  rcases isomorphism with
    ⟨order, sourceOrder, targetOrder, permutation, mapEdge⟩
  have horder : order = 7 := by
    calc
      order = (degreeSevenPatternGraph coloring).length := sourceOrder.symm
      _ = 7 := coloringGraph_length 7 _
  subst order
  exact ⟨permutation, mapEdge⟩

theorem degreeSevenPattern_has_fixedCataloguePermutation
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    ∃ catalogueIndex : Fin 9,
      ∃ sourceToRepresentative : FinPermutation 7,
        D7R34FixedIsoData coloring catalogueIndex sourceToRepresentative := by
  obtain ⟨catalogueIndex, ⟨isomorphism⟩⟩ :=
    degreeSevenPattern_has_catalogueIso hfree hdegree
  obtain ⟨sourceToRepresentative, hmap⟩ :=
    graphIsoFin_seven_has_fixedPermutation isomorphism
  exact ⟨catalogueIndex, sourceToRepresentative, hmap⟩

/-! ## Block-diagonal lift of the seven-vertex catalogue permutation -/

def d7PositiveLabel (vertex : Fin 7) : AmbientVertex :=
  ⟨vertex.val + 1, by omega⟩

def d7RightLabel (vertex : Fin 4) : AmbientVertex :=
  ⟨vertex.val + 8, by omega⟩

/-- Lift a permutation of labels `1, ..., 7`, fixing the root and labels
`8, ..., 11`. -/
def liftD7Vertex (permutation : FinPermutation 7)
    (vertex : AmbientVertex) : AmbientVertex :=
  if hblock : 1 ≤ vertex.val ∧ vertex.val ≤ 7 then
    d7PositiveLabel
      (permutation ⟨vertex.val - 1, by omega⟩)
  else
    vertex

@[simp] theorem liftD7Vertex_zero (permutation : FinPermutation 7) :
    liftD7Vertex permutation (0 : AmbientVertex) = 0 := by
  simp [liftD7Vertex]

@[simp] theorem liftD7Vertex_positive
    (permutation : FinPermutation 7) (vertex : Fin 7) :
    liftD7Vertex permutation (d7PositiveLabel vertex) =
      d7PositiveLabel (permutation vertex) := by
  unfold liftD7Vertex
  rw [dif_pos]
  · congr 2
  · simp [d7PositiveLabel]
    omega

@[simp] theorem liftD7Vertex_right
    (permutation : FinPermutation 7) (vertex : Fin 4) :
    liftD7Vertex permutation (d7RightLabel vertex) =
      d7RightLabel vertex := by
  unfold liftD7Vertex
  rw [dif_neg]
  simp [d7RightLabel]

theorem liftD7Vertex_symm_apply
    (permutation : FinPermutation 7) (vertex : AmbientVertex) :
    liftD7Vertex permutation.symm
        (liftD7Vertex permutation vertex) = vertex := by
  by_cases hblock : 1 ≤ vertex.val ∧ vertex.val ≤ 7
  · let localVertex : Fin 7 := ⟨vertex.val - 1, by omega⟩
    have hvertex : vertex = d7PositiveLabel localVertex := by
      apply Fin.ext
      simp [d7PositiveLabel, localVertex]
      omega
    rw [hvertex, liftD7Vertex_positive, liftD7Vertex_positive,
      FinPermutation.symm_apply_apply]
  · simp [liftD7Vertex, hblock]

theorem liftD7Vertex_apply_symm
    (permutation : FinPermutation 7) (vertex : AmbientVertex) :
    liftD7Vertex permutation
        (liftD7Vertex permutation.symm vertex) = vertex := by
  simpa only using liftD7Vertex_symm_apply permutation.symm vertex

def liftD7Permutation (permutation : FinPermutation 7) :
    FinPermutation 12 where
  toFun := liftD7Vertex permutation
  invFun := liftD7Vertex permutation.symm
  left_inv := liftD7Vertex_symm_apply permutation
  right_inv := liftD7Vertex_apply_symm permutation

@[simp] theorem liftD7Permutation_zero
    (permutation : FinPermutation 7) :
    liftD7Permutation permutation (0 : AmbientVertex) = 0 :=
  liftD7Vertex_zero permutation

@[simp] theorem liftD7Permutation_positive
    (permutation : FinPermutation 7) (vertex : Fin 7) :
    liftD7Permutation permutation (d7PositiveLabel vertex) =
      d7PositiveLabel (permutation vertex) :=
  liftD7Vertex_positive permutation vertex

@[simp] theorem liftD7Permutation_right
    (permutation : FinPermutation 7) (vertex : Fin 4) :
    liftD7Permutation permutation (d7RightLabel vertex) =
      d7RightLabel vertex :=
  liftD7Vertex_right permutation vertex

/-! ## Ambient pullback and semantic transports -/

/-- The local isomorphism maps source labels to representative labels.
Since `permuteColoring` is a pullback, the ambient action is its inverse. -/
noncomputable def d7R34RelabeledColoring
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7) : Nat -> Bool :=
  permuteColoring (liftD7Permutation sourceToRepresentative.symm)
    (rootSortedColoring coloring)

theorem avoidsCover6_permute_iff
    (permutation : FinPermutation 12) (coloring : Nat -> Bool) :
    AvoidsCover6 coloring ↔
      AvoidsCover6 (permuteColoring permutation coloring) := by
  constructor
  · intro havoid motif hmotif hoccurrence
    exact havoid motif hmotif
      ((inducedMotifOccurrence_permute_iff
        permutation coloring motif).mpr hoccurrence)
  · intro havoid motif hmotif hoccurrence
    exact havoid motif hmotif
      ((inducedMotifOccurrence_permute_iff
        permutation coloring motif).mp hoccurrence)

theorem d7R34Relabeled_isRamseyFree_iff
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7) :
    isRamseyFree 12 4 4 coloring ↔
      isRamseyFree 12 4 4
        (d7R34RelabeledColoring coloring sourceToRepresentative) := by
  exact (rootSort_isRamseyFree_iff coloring).trans
    (isRamseyFree_permute_iff
      (liftD7Permutation sourceToRepresentative.symm)
      (rootSortedColoring coloring))

theorem d7R34Relabeled_inducedMotifOccurrence_iff
    {motifOrder : Nat} (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7) (motif : Graph) :
    InducedMotifOccurrence motifOrder coloring motif ↔
      InducedMotifOccurrence motifOrder
        (d7R34RelabeledColoring coloring sourceToRepresentative) motif := by
  have hroot := inducedMotifOccurrence_permute_iff
    (motifOrder := motifOrder)
    (rootSortPermutation coloring) coloring motif
  have hroot' :
      InducedMotifOccurrence motifOrder coloring motif ↔
        InducedMotifOccurrence motifOrder
          (rootSortedColoring coloring) motif := by
    simpa [rootSortedColoring] using hroot
  exact hroot'.trans
    (inducedMotifOccurrence_permute_iff
      (motifOrder := motifOrder)
      (liftD7Permutation sourceToRepresentative.symm)
      (rootSortedColoring coloring) motif)

theorem d7R34Relabeled_avoidsCover6_iff
    (coloring : Nat -> Bool)
    (sourceToRepresentative : FinPermutation 7) :
    AvoidsCover6 coloring ↔
      AvoidsCover6
        (d7R34RelabeledColoring coloring sourceToRepresentative) := by
  exact (avoidsCover6_permute_iff
      (rootSortPermutation coloring) coloring).trans
    (avoidsCover6_permute_iff
      (liftD7Permutation sourceToRepresentative.symm)
      (rootSortedColoring coloring))

theorem d7R34Relabeled_root_positive
    (coloring : Nat -> Bool)
    (hdegree : positiveRootDegree coloring = 7)
    (sourceToRepresentative : FinPermutation 7) (vertex : Fin 7) :
    coloringEdge 12
      (d7R34RelabeledColoring coloring sourceToRepresentative)
      0 (d7PositiveLabel vertex).val = true := by
  have hedge := coloringEdge_permuteColoring
    (liftD7Permutation sourceToRepresentative.symm)
    (rootSortedColoring coloring) (0 : AmbientVertex)
    (d7PositiveLabel vertex)
  rw [liftD7Permutation_zero, liftD7Permutation_positive] at hedge
  have hroot :=
    R44Cover6DegreeSevenNormalization.d7RootSort_exact_seven
      coloring hdegree
      (show Fin 11 from ⟨(sourceToRepresentative.symm vertex).val, by omega⟩)
  have hlt : (sourceToRepresentative.symm vertex).val < 7 :=
    (sourceToRepresentative.symm vertex).isLt
  simp [hlt] at hroot
  exact (by simpa [d7R34RelabeledColoring, d7PositiveLabel] using
    hedge.trans hroot)

theorem d7R34Relabeled_root_right
    (coloring : Nat -> Bool)
    (hdegree : positiveRootDegree coloring = 7)
    (sourceToRepresentative : FinPermutation 7) (vertex : Fin 4) :
    coloringEdge 12
      (d7R34RelabeledColoring coloring sourceToRepresentative)
      0 (d7RightLabel vertex).val = false := by
  have hedge := coloringEdge_permuteColoring
    (liftD7Permutation sourceToRepresentative.symm)
    (rootSortedColoring coloring) (0 : AmbientVertex)
    (d7RightLabel vertex)
  rw [liftD7Permutation_zero, liftD7Permutation_right] at hedge
  have hroot :=
    R44Cover6DegreeSevenNormalization.d7RootSort_exact_seven
      coloring hdegree
      (show Fin 11 from ⟨vertex.val + 7, by omega⟩)
  have hnot : ¬ vertex.val + 7 < 7 := by omega
  simp [hnot] at hroot
  exact (by simpa [d7R34RelabeledColoring, d7RightLabel] using
    hedge.trans hroot)

theorem edge_degreeSevenPatternGraph
    (coloring : Nat -> Bool) (left right : Fin 7) (hne : left ≠ right) :
    edge (degreeSevenPatternGraph coloring) left.val right.val =
      coloringEdge 12 (rootSortedColoring coloring)
        (d7PositiveLabel left).val (d7PositiveLabel right).val := by
  rw [degreeSevenPatternGraph, edge_coloringGraph]
  change
    ramseyEdge 7
        (R44Cover6DegreeSevenMinCenter.sevenPatternColor
          (R44Cover6DegreeSevenMinCenter.degreeSevenPattern coloring))
        left.val right.val =
      ramseyEdge 12 (rootSortedColoring coloring)
        (left.val + 1) (right.val + 1)
  exact R44Cover6DegreeSevenMinCenter.ramseyEdge_degreeSevenPattern
    coloring left right hne

theorem d7R34Relabeled_internal_edge
    (coloring : Nat -> Bool) (catalogueIndex : Fin 9)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring catalogueIndex
      sourceToRepresentative)
    (left right : Fin 7) (hne : left ≠ right) :
    coloringEdge 12
        (d7R34RelabeledColoring coloring sourceToRepresentative)
        (d7PositiveLabel left).val (d7PositiveLabel right).val =
      edge (r34Catalogue7Representative catalogueIndex)
        left.val right.val := by
  have hinverseNe : sourceToRepresentative.symm left ≠
      sourceToRepresentative.symm right := by
    intro hequal
    apply hne
    have := congrArg sourceToRepresentative hequal
    simpa only [FinPermutation.apply_symm_apply] using this
  have hedge := coloringEdge_permuteColoring
    (liftD7Permutation sourceToRepresentative.symm)
    (rootSortedColoring coloring)
    (d7PositiveLabel left) (d7PositiveLabel right)
  rw [liftD7Permutation_positive, liftD7Permutation_positive] at hedge
  calc
    coloringEdge 12
        (d7R34RelabeledColoring coloring sourceToRepresentative)
        (d7PositiveLabel left).val (d7PositiveLabel right).val =
        coloringEdge 12 (rootSortedColoring coloring)
          (d7PositiveLabel (sourceToRepresentative.symm left)).val
          (d7PositiveLabel (sourceToRepresentative.symm right)).val := by
            simpa [d7R34RelabeledColoring] using hedge
    _ = edge (degreeSevenPatternGraph coloring)
          (sourceToRepresentative.symm left).val
          (sourceToRepresentative.symm right).val :=
        (edge_degreeSevenPatternGraph coloring _ _ hinverseNe).symm
    _ = edge (r34Catalogue7Representative catalogueIndex)
          (sourceToRepresentative
            (sourceToRepresentative.symm left)).val
          (sourceToRepresentative
            (sourceToRepresentative.symm right)).val :=
        hmap _ _
    _ = edge (r34Catalogue7Representative catalogueIndex)
          left.val right.val := by simp

/-! ## The exact 21 representative units -/

theorem sevenEdgePairs_ordered
    (pair : Fin 7 × Fin 7)
    (hpair : pair ∈ R44Cover6DegreeSevenMinCenter.sevenEdgePairs) :
    pair.1 < pair.2 := by
  native_decide +revert

def d7RepresentativeUnit (graph : Graph) (pair : Fin 7 × Fin 7) : Int :=
  if edge graph pair.1.val pair.2.val then
    positiveEdgeLiteral 12 (pair.1.val + 1) (pair.2.val + 1)
  else
    negativeEdgeLiteral 12 (pair.1.val + 1) (pair.2.val + 1)

def d7RepresentativeUnits (graph : Graph) : List Int :=
  R44Cover6DegreeSevenMinCenter.sevenEdgePairs.map
    (d7RepresentativeUnit graph)

def d7RepresentativeDimacsVariables : List Nat :=
  R44Cover6DegreeSevenMinCenter.sevenEdgePairs.map fun pair =>
    dimacsEdgeVar 12 (pair.1.val + 1) (pair.2.val + 1)

theorem d7RepresentativeDimacsVariables_exact :
    d7RepresentativeDimacsVariables =
      [12, 13, 14, 15, 16, 17, 22, 23, 24, 25, 26,
        31, 32, 33, 34, 39, 40, 41, 46, 47, 52] := by
  native_decide

theorem d7RepresentativeUnits_length (graph : Graph) :
    (d7RepresentativeUnits graph).length = 21 := by
  simp [d7RepresentativeUnits,
    R44Cover6DegreeSevenMinCenter.sevenEdgePairs]
  native_decide

theorem d7RepresentativeUnit_natAbs
    (graph : Graph) (pair : Fin 7 × Fin 7) :
    Int.natAbs (d7RepresentativeUnit graph pair) =
      dimacsEdgeVar 12 (pair.1.val + 1) (pair.2.val + 1) := by
  by_cases hedge : edge graph pair.1.val pair.2.val
  · simp [d7RepresentativeUnit, hedge, positiveEdgeLiteral]
  · simp [d7RepresentativeUnit, hedge, negativeEdgeLiteral]

theorem d7RepresentativeUnits_natAbs (graph : Graph) :
    (d7RepresentativeUnits graph).map Int.natAbs =
      d7RepresentativeDimacsVariables := by
  simp [d7RepresentativeUnits, d7RepresentativeDimacsVariables,
    d7RepresentativeUnit_natAbs]

theorem d7RepresentativeUnit_satisfied_iff
    (coloring : Nat -> Bool) (graph : Graph)
    (pair : Fin 7 × Fin 7) (hordered : pair.1 < pair.2) :
    dimacsUnitSatisfied coloring (d7RepresentativeUnit graph pair) ↔
      coloringEdge 12 coloring
          (d7PositiveLabel pair.1).val
          (d7PositiveLabel pair.2).val =
        edge graph pair.1.val pair.2.val := by
  have hambientOrdered : pair.1.val + 1 < pair.2.val + 1 := by
    omega
  cases hedge : edge graph pair.1.val pair.2.val <;>
    simp [d7RepresentativeUnit, hedge, coloringEdge,
      d7PositiveLabel, hambientOrdered]

theorem d7R34Relabeled_representativeUnitsSatisfied
    (coloring : Nat -> Bool) (catalogueIndex : Fin 9)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring catalogueIndex
      sourceToRepresentative) :
    AllUnitsSatisfied
      (d7R34RelabeledColoring coloring sourceToRepresentative)
      (d7RepresentativeUnits
        (r34Catalogue7Representative catalogueIndex)) := by
  intro literal hliteral
  simp only [d7RepresentativeUnits, List.mem_map] at hliteral
  obtain ⟨pair, hpair, rfl⟩ := hliteral
  have hordered := sevenEdgePairs_ordered pair hpair
  have hne : pair.1 ≠ pair.2 := by
    intro hequal
    have hval := congrArg Fin.val hequal
    omega
  exact (d7RepresentativeUnit_satisfied_iff
    (d7R34RelabeledColoring coloring sourceToRepresentative)
    (r34Catalogue7Representative catalogueIndex)
    pair hordered).mpr
      (d7R34Relabeled_internal_edge coloring catalogueIndex
        sourceToRepresentative hmap pair.1 pair.2 hne)

/-! ## Consolidated structural endpoint -/

theorem degreeSeven_has_r34RepresentativeRelabeling
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    ∃ catalogueIndex : Fin 9,
      ∃ sourceToRepresentative : FinPermutation 7,
        D7R34FixedIsoData coloring catalogueIndex
            sourceToRepresentative ∧
        isRamseyFree 12 4 4
          (d7R34RelabeledColoring coloring sourceToRepresentative) ∧
        (∀ vertex : Fin 7,
          coloringEdge 12
            (d7R34RelabeledColoring coloring sourceToRepresentative)
            0 (d7PositiveLabel vertex).val = true) ∧
        (∀ vertex : Fin 4,
          coloringEdge 12
            (d7R34RelabeledColoring coloring sourceToRepresentative)
            0 (d7RightLabel vertex).val = false) ∧
        (∀ left right : Fin 7, left ≠ right ->
          coloringEdge 12
              (d7R34RelabeledColoring coloring sourceToRepresentative)
              (d7PositiveLabel left).val (d7PositiveLabel right).val =
            edge (r34Catalogue7Representative catalogueIndex)
              left.val right.val) ∧
        AllUnitsSatisfied
          (d7R34RelabeledColoring coloring sourceToRepresentative)
          (d7RepresentativeUnits
            (r34Catalogue7Representative catalogueIndex)) := by
  obtain ⟨catalogueIndex, sourceToRepresentative, hmap⟩ :=
    degreeSevenPattern_has_fixedCataloguePermutation hfree hdegree
  refine ⟨catalogueIndex, sourceToRepresentative, hmap,
    (d7R34Relabeled_isRamseyFree_iff
      coloring sourceToRepresentative).mp hfree,
    d7R34Relabeled_root_positive coloring hdegree sourceToRepresentative,
    d7R34Relabeled_root_right coloring hdegree sourceToRepresentative,
    ?_, d7R34Relabeled_representativeUnitsSatisfied
      coloring catalogueIndex sourceToRepresentative hmap⟩
  intro left right hne
  exact d7R34Relabeled_internal_edge coloring catalogueIndex
    sourceToRepresentative hmap left right hne

theorem degreeSeven_cover6Avoiding_has_r34RepresentativeRelabeling
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7)
    (havoid : AvoidsCover6 coloring) :
    ∃ catalogueIndex : Fin 9,
      ∃ sourceToRepresentative : FinPermutation 7,
        D7R34FixedIsoData coloring catalogueIndex
            sourceToRepresentative ∧
        isRamseyFree 12 4 4
          (d7R34RelabeledColoring coloring sourceToRepresentative) ∧
        AvoidsCover6
          (d7R34RelabeledColoring coloring sourceToRepresentative) ∧
        AllUnitsSatisfied
          (d7R34RelabeledColoring coloring sourceToRepresentative)
          (d7RepresentativeUnits
            (r34Catalogue7Representative catalogueIndex)) := by
  obtain ⟨catalogueIndex, sourceToRepresentative, hmap, hfree',
      _hrootPositive, _hrootRight, _hedges, hunits⟩ :=
    degreeSeven_has_r34RepresentativeRelabeling hfree hdegree
  exact ⟨catalogueIndex, sourceToRepresentative, hmap, hfree',
    (d7R34Relabeled_avoidsCover6_iff
      coloring sourceToRepresentative).mp havoid, hunits⟩

#print axioms degreeSeven_lowCenterExists
#print axioms degreeSevenPattern_has_catalogueIso
#print axioms degreeSevenPattern_has_fixedCataloguePermutation
#print axioms degreeSeven_has_r34RepresentativeRelabeling
#print axioms degreeSeven_cover6Avoiding_has_r34RepresentativeRelabeling

end LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization
