import LRATCatcher.Tests.R44OrderTwelveTwoCenterCases

/-!
  # A low-degree centre in the degree-seven root neighbourhood

  This module isolates the finite graph-theoretic reduction needed by the
  degree-seven version of the cover6 search.  It does not import a SAT result
  and it does not claim a new Ramsey bound.
-/

namespace LRATCatcher.Tests.R44Cover6DegreeSevenMinCenter

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44OrderTwelveTwoCenterCases

abbrev AmbientVertex := Fin 12

/-! ## Exact degree-seven root normalization -/

theorem sortedNonRoot_exact_seven (pattern : RootPattern)
    (hdegree : (List.finRange 11).countP (patternColor pattern) = 7)
    (position : Fin 11) :
    patternColor pattern
        ((sortedNonRoot pattern).getD position.val 0) =
      decide (position.val < 7) := by
  native_decide +revert

theorem rootSort_exact_seven (coloring : Nat -> Bool)
    (hdegree : positiveRootDegree coloring = 7)
    (position : Fin 11) :
    coloringEdge 12 (rootSortedColoring coloring)
        0 (position.val + 1) = decide (position.val < 7) := by
  have hcount :
      (List.finRange 11).countP (patternColor (rootPattern coloring)) = 7 := by
    rw [rootPattern_count_eq_positiveRootDegree, hdegree]
  have hsorted := sortedNonRoot_exact_seven
    (rootPattern coloring) hcount position
  rw [patternColor_rootPattern coloring
    ((sortedNonRoot (rootPattern coloring)).getD position.val 0)] at hsorted
  have hedge := coloringEdge_permuteColoring
    (rootSortPermutation coloring) coloring (0 : AmbientVertex)
      (show AmbientVertex from Fin.mk (position.val + 1) (by omega))
  rw [rootSortPermutation_zero,
    rootSortPermutation_nonRoot_val coloring position] at hedge
  exact (by simpa [rootSortedColoring] using hedge.trans hsorted)

/-! ## The 21-bit normalized neighbourhood pattern -/

def sevenEdgePairs : List (Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun left =>
    (List.finRange 7).filterMap fun right =>
      if left < right then some (left, right) else none

def sevenEdgePair (index : Nat) : Fin 7 × Fin 7 :=
  sevenEdgePairs.getD index (0, 0)

theorem sevenEdgePair_edgeVar (left right : Fin 7)
    (hordered : left < right) :
    sevenEdgePair (edgeVar 7 left.val right.val) = (left, right) := by
  native_decide +revert

abbrev SevenPattern := BitVec 21

def sevenPatternColor (pattern : SevenPattern) (index : Nat) : Bool :=
  pattern.getLsbD index

noncomputable def degreeSevenPatternBits (coloring : Nat -> Bool) : List Bool :=
  List.ofFn fun index : Fin 21 =>
    let endpoints := sevenEdgePair index.val
    coloringEdge 12 (rootSortedColoring coloring)
      (endpoints.1.val + 1) (endpoints.2.val + 1)

noncomputable def degreeSevenPattern (coloring : Nat -> Bool) : SevenPattern :=
  BitVec.cast (by simp [degreeSevenPatternBits])
    (BitVec.ofBoolListLE (degreeSevenPatternBits coloring))

theorem sevenPatternColor_degreeSevenPattern
    (coloring : Nat -> Bool) (index : Fin 21) :
    sevenPatternColor (degreeSevenPattern coloring) index.val =
      let endpoints := sevenEdgePair index.val
      coloringEdge 12 (rootSortedColoring coloring)
        (endpoints.1.val + 1) (endpoints.2.val + 1) := by
  unfold sevenPatternColor degreeSevenPattern
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [<- List.getElem_eq_getD
    (l := degreeSevenPatternBits coloring) (i := index.val)
    (h := by simp [degreeSevenPatternBits]) false]
  change
    (List.ofFn fun index : Fin 21 =>
      let endpoints := sevenEdgePair index.val
      coloringEdge 12 (rootSortedColoring coloring)
        (endpoints.1.val + 1) (endpoints.2.val + 1))[index.val] = _
  rw [List.getElem_ofFn]

theorem degreeSevenPattern_edge_ordered
    (coloring : Nat -> Bool) (left right : Fin 7) (hordered : left < right) :
    sevenPatternColor (degreeSevenPattern coloring)
        (edgeVar 7 left.val right.val) =
      coloringEdge 12 (rootSortedColoring coloring)
        (left.val + 1) (right.val + 1) := by
  have hindex : edgeVar 7 left.val right.val < 21 := by
    native_decide +revert
  rw [sevenPatternColor_degreeSevenPattern coloring
    (show Fin 21 from Fin.mk (edgeVar 7 left.val right.val) hindex)]
  rw [sevenEdgePair_edgeVar left right hordered]

theorem ramseyEdge_degreeSevenPattern
    (coloring : Nat -> Bool) (left right : Fin 7) (hne : left ≠ right) :
    ramseyEdge 7 (sevenPatternColor (degreeSevenPattern coloring))
        left.val right.val =
      ramseyEdge 12 (rootSortedColoring coloring)
        (left.val + 1) (right.val + 1) := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · have horderedFin : left < right := hordered
    have hedge := degreeSevenPattern_edge_ordered
      coloring left right horderedFin
    simpa [ramseyEdge, coloringEdge, hordered] using hedge
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    have hedge := degreeSevenPattern_edge_ordered
      coloring right left hreverseFin
    rw [ramseyEdge_comm 7 (sevenPatternColor (degreeSevenPattern coloring))]
    rw [ramseyEdge_comm 12 (rootSortedColoring coloring)]
    simpa [ramseyEdge, coloringEdge, hreverse] using hedge

/-! ## Semantic restriction from the normalized `K_12` coloring -/

def liftSevenVertex (vertex : Nat) : Nat := vertex + 1

theorem liftSevenVertex_injective : Function.Injective liftSevenVertex := by
  intro left right hequal
  unfold liftSevenVertex at hequal
  omega

theorem liftSeven_nodup {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map liftSevenVertex).Nodup := by
  exact hnodup.map liftSevenVertex
    (fun left right hne hequal => hne (liftSevenVertex_injective hequal))

theorem liftSeven_bound {vertices : List Nat}
    (hbound : forall vertex, vertex ∈ vertices -> vertex < 7) :
    forall vertex, vertex ∈ vertices.map liftSevenVertex -> vertex < 12 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  have := hbound index hindex
  simp [liftSevenVertex]
  omega

theorem pattern_local_true_related
    (coloring : Nat -> Bool) {vertices : List Nat}
    (hall : forall left right,
      left ∈ vertices -> right ∈ vertices -> left < right ->
      sevenPatternColor (degreeSevenPattern coloring)
        (edgeVar 7 left right) = true) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (ramseyEdge 7 (sevenPatternColor (degreeSevenPattern coloring)))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem pattern_local_false_related
    (coloring : Nat -> Bool) {vertices : List Nat}
    (hall : forall left right,
      left ∈ vertices -> right ∈ vertices -> left < right ->
      sevenPatternColor (degreeSevenPattern coloring)
        (edgeVar 7 left right) = false) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 7 (sevenPatternColor (degreeSevenPattern coloring))
          left right)) vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge 7 (sevenPatternColor (degreeSevenPattern coloring))
        left right) = true
    rw [ramseyEdge_comm]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem pattern_mapped_true_related
    (coloring : Nat -> Bool) {vertices : List Nat}
    (hbound : forall vertex, vertex ∈ vertices -> vertex < 7)
    (hrelated : LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (ramseyEdge 7 (sevenPatternColor (degreeSevenPattern coloring)))
      vertices) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (ramseyEdge 12 (rootSortedColoring coloring))
      (vertices.map liftSevenVertex) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg liftSevenVertex hequal)
  have hlocal := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe
  have hedge := ramseyEdge_degreeSevenPattern coloring
    (show Fin 7 from ⟨indexLeft, hleftBound⟩)
    (show Fin 7 from ⟨indexRight, hrightBound⟩)
    (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  change ramseyEdge 12 (rootSortedColoring coloring)
    (liftSevenVertex indexLeft) (liftSevenVertex indexRight) = true
  simpa [liftSevenVertex] using hedge.symm.trans hlocal

theorem pattern_mapped_false_related
    (coloring : Nat -> Bool) {vertices : List Nat}
    (hbound : forall vertex, vertex ∈ vertices -> vertex < 7)
    (hrelated : LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 7 (sevenPatternColor (degreeSevenPattern coloring))
          left right)) vertices) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right => !(ramseyEdge 12 (rootSortedColoring coloring)
        left right))
      (vertices.map liftSevenVertex) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg liftSevenVertex hequal)
  have hlocal := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe
  have hedge := ramseyEdge_degreeSevenPattern coloring
    (show Fin 7 from ⟨indexLeft, hleftBound⟩)
    (show Fin 7 from ⟨indexRight, hrightBound⟩)
    (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  change Bool.not (ramseyEdge 12 (rootSortedColoring coloring)
    (liftSevenVertex indexLeft) (liftSevenVertex indexRight)) = true
  change Bool.not (ramseyEdge 7
    (sevenPatternColor (degreeSevenPattern coloring))
    indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  simpa [liftSevenVertex] using hlocal

theorem degreeSevenPattern_isRamseyFree
    {coloring : Nat -> Bool}
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    isRamseyFree 7 3 4
      (sevenPatternColor (degreeSevenPattern coloring)) := by
  have hnormalizedFree :
      isRamseyFree 12 4 4 (rootSortedColoring coloring) :=
    (rootSort_isRamseyFree_iff coloring).mp hfree
  have hrootNeighbor : forall index : Fin 7,
      ramseyEdge 12 (rootSortedColoring coloring)
        0 (liftSevenVertex index.val) = true := by
    intro index
    let position : Fin 11 := ⟨index.val, by omega⟩
    have hedge := rootSort_exact_seven coloring hdegree position
    have hlt : position.val < 7 := by
      dsimp [position]
      omega
    have hdecide : decide (position.val < 7) = true := by simp [hlt]
    rw [hdecide] at hedge
    simpa [liftSevenVertex, ramseyEdge, coloringEdge, position] using hedge
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map liftSevenVertex
    let forbidden := 0 :: mapped
    have hmappedNodup : mapped.Nodup := by
      exact liftSeven_nodup hnodup
    have hmappedBound : forall vertex, vertex ∈ mapped -> vertex < 12 := by
      exact liftSeven_bound hbound
    have hrootNotMapped : 0 ∉ mapped := by
      intro hmember
      obtain ⟨index, _hindex, hequal⟩ := List.mem_map.mp hmember
      simp [liftSevenVertex] at hequal
    have hforbiddenLength : forbidden.length = 4 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        forall vertex, vertex ∈ forbidden -> vertex < 12 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · omega
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := pattern_local_true_related coloring hall
    have hmappedRed :
        LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
          (ramseyEdge 12 (rootSortedColoring coloring))
          mapped := by
      exact pattern_mapped_true_related coloring hbound hlocal
    have hforbiddenRed :
        LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
          (ramseyEdge 12 (rootSortedColoring coloring))
          forbidden := by
      apply LRATCatcher.Tests.R55DegreeBounds.allDistinctRelated_cons
      · exact ramseyEdge_comm 12 (rootSortedColoring coloring)
      · exact hmappedRed
      · intro vertex hvertex
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
        have hindexBound := hbound index hindex
        exact hrootNeighbor ⟨index, hindexBound⟩
    apply hnormalizedFree.1 forbidden hforbiddenLength hforbiddenBound
      hforbiddenNodup
    intro left right hleft hright hordered
    have hedge := hforbiddenRed left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map liftSevenVertex
    have hmappedNodup : mapped.Nodup := by
      exact liftSeven_nodup hnodup
    have hmappedBound : forall vertex, vertex ∈ mapped -> vertex < 12 := by
      exact liftSeven_bound hbound
    have hlocal := pattern_local_false_related coloring hall
    have hmappedBlue : LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
        (fun left right => !(ramseyEdge 12 (rootSortedColoring coloring)
          left right)) mapped := by
      exact pattern_mapped_false_related coloring hbound hlocal
    apply hnormalizedFree.2 mapped (by simp [mapped, hlength]) hmappedBound
      hmappedNodup
    intro left right hleft hright hordered
    have hedge := hmappedBlue left hleft right hright
      (Nat.ne_of_lt hordered)
    simpa [ramseyEdge, hordered] using hedge

def sevenInternalDegree (pattern : SevenPattern) (center : Fin 7) : Nat :=
  (List.finRange 7).countP fun other =>
    decide (other != center) &&
      ramseyEdge 7 (sevenPatternColor pattern) center.val other.val

theorem checked_r34_seven_degree_window
    (pattern : SevenPattern)
    (hfree : checkRamseyFree 7 3 4 (sevenPatternColor pattern) = true) :
    (forall center : Fin 7, 1 <= sevenInternalDegree pattern center) /\
      exists center : Fin 7, sevenInternalDegree pattern center <= 2 := by
  native_decide +revert

theorem checked_r34_seven_has_degree_one_or_two
    (pattern : SevenPattern)
    (hfree : checkRamseyFree 7 3 4 (sevenPatternColor pattern) = true) :
    exists center : Fin 7,
      1 <= sevenInternalDegree pattern center /\
        sevenInternalDegree pattern center <= 2 := by
  obtain ⟨hlower, center, hupper⟩ :=
    checked_r34_seven_degree_window pattern hfree
  exact ⟨center, hlower center, hupper⟩

/-! ## Closing the finite semantic/computational round trip -/

theorem checkRamseyFree_complete
    {order redOrder blueOrder : Nat} {coloring : Nat -> Bool}
    (hfree : isRamseyFree order redOrder blueOrder coloring) :
    checkRamseyFree order redOrder blueOrder coloring = true := by
  unfold checkRamseyFree
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hlength, hbound, hnodup⟩ :=
      subsets_valid order redOrder vertices hvertices
    obtain ⟨edgeIndex, hedgeIndex, hfalse⟩ :=
      exists_false_edge order vertices coloring
        (hfree.1 vertices hlength hbound hnodup)
    rw [List.any_eq_true]
    exact ⟨edgeIndex, hedgeIndex, by simp [hfalse]⟩
  · rw [List.all_eq_true]
    intro vertices hvertices
    obtain ⟨hlength, hbound, hnodup⟩ :=
      subsets_valid order blueOrder vertices hvertices
    obtain ⟨edgeIndex, hedgeIndex, htrue⟩ :=
      exists_true_edge order vertices coloring
        (hfree.2 vertices hlength hbound hnodup)
    rw [List.any_eq_true]
    exact ⟨edgeIndex, hedgeIndex, htrue⟩

noncomputable def normalizedDegreeSevenInternalDegree
    (coloring : Nat -> Bool) (center : Fin 7) : Nat :=
  (List.finRange 7).countP fun other =>
    decide (other ≠ center) &&
      ramseyEdge 12 (rootSortedColoring coloring)
        (center.val + 1) (other.val + 1)

theorem sevenInternalDegree_eq_normalized
    (coloring : Nat -> Bool) (center : Fin 7) :
    sevenInternalDegree (degreeSevenPattern coloring) center =
      normalizedDegreeSevenInternalDegree coloring center := by
  unfold sevenInternalDegree normalizedDegreeSevenInternalDegree
  apply List.countP_congr
  intro other _hother
  by_cases hequal : other = center
  · simp [hequal]
  · have hedge := ramseyEdge_degreeSevenPattern
      coloring center other (fun h => hequal h.symm)
    simp [hequal, hedge]

/-- Main degree-seven reduction: after sorting the seven positive root
neighbours into labels `1,...,7`, one of them has one or two positive
neighbours inside that seven-vertex block. -/
theorem degreeSeven_has_internal_degree_one_or_two
    (coloring : Nat -> Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    exists center : Fin 7,
      1 <= normalizedDegreeSevenInternalDegree coloring center /\
        normalizedDegreeSevenInternalDegree coloring center <= 2 := by
  have hsemantic := degreeSevenPattern_isRamseyFree hfree hdegree
  have hcheck := checkRamseyFree_complete hsemantic
  obtain ⟨center, hlower, hupper⟩ :=
    checked_r34_seven_has_degree_one_or_two
      (degreeSevenPattern coloring) hcheck
  refine ⟨center, ?_, ?_⟩
  · rw [← sevenInternalDegree_eq_normalized]
    exact hlower
  · rw [← sevenInternalDegree_eq_normalized]
    exact hupper

/-- Every normalized positive root neighbour has at least one positive
neighbour inside the degree-seven block.  This is the formal no-isolated
endpoint; the finite checker proves it together with the low-degree centre. -/
theorem degreeSeven_has_no_isolated_positive_neighbor
    (coloring : Nat -> Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 7) :
    forall center : Fin 7,
      1 <= normalizedDegreeSevenInternalDegree coloring center := by
  have hsemantic := degreeSevenPattern_isRamseyFree hfree hdegree
  have hcheck := checkRamseyFree_complete hsemantic
  have hlower :=
    (checked_r34_seven_degree_window (degreeSevenPattern coloring) hcheck).1
  intro center
  rw [← sevenInternalDegree_eq_normalized]
  exact hlower center

#print axioms checked_r34_seven_degree_window
#print axioms checked_r34_seven_has_degree_one_or_two
#print axioms degreeSevenPattern_isRamseyFree
#print axioms degreeSeven_has_internal_degree_one_or_two
#print axioms degreeSeven_has_no_isolated_positive_neighbor

end LRATCatcher.Tests.R44Cover6DegreeSevenMinCenter
