import LRATCatcher.Tests.R44Cover6RepresentativeCubes

/-!
  # Equivariant S7 transport for the six cover6 cubes

  The generated cover is the `S_7` closure of only six partial cubes.  This
  module supplies the missing semantic transport.  Pair orientations are
  normalized explicitly, because an arbitrary vertex permutation need not
  preserve the numerical order used by the 21-bit graph6 packing.
-/

namespace LRATCatcher.Tests.R44Cover6S7Transport

open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6CubeBridge
open LRATCatcher.Tests.R44Cover6RepresentativeCubes

/-! ## Unordered local edges -/

/-- Read a local assignment on the increasing orientation of an unordered
pair.  The diagonal value is irrelevant to every predicate below. -/
def unorderedLocalEdge
    (localEdges : LocalEdgeAssignment) (left right : MotifVertex) : Bool :=
  if left < right then localEdges left right else localEdges right left

@[simp] theorem unorderedLocalEdge_of_lt
    (localEdges : LocalEdgeAssignment) {left right : MotifVertex}
    (hordered : left < right) :
    unorderedLocalEdge localEdges left right = localEdges left right := by
  simp [unorderedLocalEdge, hordered]

theorem unorderedLocalEdge_comm
    (localEdges : LocalEdgeAssignment) (left right : MotifVertex) :
    unorderedLocalEdge localEdges left right =
      unorderedLocalEdge localEdges right left := by
  unfold unorderedLocalEdge
  by_cases hordered : left < right
  · have hnotReverse : ¬ right < left := by
      intro hreverse
      have horderedVal : left.val < right.val := hordered
      have hreverseVal : right.val < left.val := hreverse
      omega
    simp [hordered, hnotReverse]
  · by_cases hequal : left = right
    · subst right
      rfl
    · have hnotOrderedVal : ¬ left.val < right.val := by
        simpa using hordered
      have hneVal : left.val ≠ right.val := fun hval => hequal (Fin.ext hval)
      have hreverseVal : right.val < left.val := by omega
      have hreverse : right < left := hreverseVal
      simp [hordered, hreverse]

private theorem fin_lt_of_not_lt_of_ne {n : Nat} {left right : Fin n}
    (hnotOrdered : ¬ left < right) (hne : left ≠ right) : right < left := by
  have hnotOrderedVal : ¬ left.val < right.val := by
    simpa using hnotOrdered
  have hneVal : left.val ≠ right.val := fun hval => hne (Fin.ext hval)
  exact (by omega : right.val < left.val)

/-- Pull a labelled local assignment back along a genuine permutation.  Thus
the edge at target labels `(u,v)` is the old edge at `(p u,p v)`. -/
def permuteLocalEdges (permutation : FinPermutation 7)
    (localEdges : LocalEdgeAssignment) : LocalEdgeAssignment :=
  fun left right =>
    unorderedLocalEdge localEdges (permutation left) (permutation right)

theorem unorderedLocalEdge_permute
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (left right : MotifVertex) :
    unorderedLocalEdge (permuteLocalEdges permutation localEdges) left right =
      unorderedLocalEdge localEdges (permutation left) (permutation right) := by
  by_cases hordered : left < right
  · simp [unorderedLocalEdge, permuteLocalEdges, hordered]
  · by_cases hequal : left = right
    · subst right
      simp [unorderedLocalEdge, permuteLocalEdges]
    · have hreverse : right < left :=
        fin_lt_of_not_lt_of_ne hordered hequal
      rw [unorderedLocalEdge_comm _ left right]
      simp [unorderedLocalEdge, permuteLocalEdges, hreverse]
      exact unorderedLocalEdge_comm _ _ _

/-! ## A four-tuple presentation of local R(4,4) admissibility -/

/-- Order-independent form of the local condition.  Quantifying four labelled
vertices is convenient for transport: their image under a bijection is again
a duplicate-free four-tuple. -/
def EveryFourTupleHasBothColors (localEdges : LocalEdgeAssignment) : Prop :=
  ∀ first second third fourth : MotifVertex,
    [first, second, third, fourth].Nodup →
    (∃ left ∈ [first, second, third, fourth],
      ∃ right ∈ [first, second, third, fourth], left ≠ right ∧
        unorderedLocalEdge localEdges left right = true) ∧
    (∃ left ∈ [first, second, third, fourth],
      ∃ right ∈ [first, second, third, fourth], left ≠ right ∧
        unorderedLocalEdge localEdges left right = false)

theorem mem_motifPairsWithin_iff
    (vertices : List MotifVertex) (left right : MotifVertex) :
    (left, right) ∈ motifPairsWithin vertices ↔
      left ∈ vertices ∧ right ∈ vertices ∧ left < right := by
  simp [motifPairsWithin]
  constructor
  · rintro ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      hordered, rfl, rfl⟩
    exact ⟨hsourceLeft, hsourceRight, hordered⟩
  · rintro ⟨hleft, hright, hordered⟩
    exact ⟨left, hleft, right, hright, hordered, rfl, rfl⟩

private theorem combinations_valid {Alpha : Type} [DecidableEq Alpha]
    (source : List Alpha) (hsource : source.Nodup) :
    ∀ size selected, selected ∈ combinations source size →
      selected.length = size ∧
      (∀ vertex ∈ selected, vertex ∈ source) ∧
      selected.Nodup := by
  induction source with
  | nil =>
      intro size selected hselected
      cases size with
      | zero =>
          simp [combinations] at hselected
          subst selected
          simp
      | succ size => simp [combinations] at hselected
  | cons head tail inductionHypothesis =>
      have hhead : head ∉ tail := (List.nodup_cons.mp hsource).1
      have htail : tail.Nodup := (List.nodup_cons.mp hsource).2
      intro size selected hselected
      cases size with
      | zero =>
          simp [combinations] at hselected
          subst selected
          simp
      | succ size =>
          simp only [combinations, List.mem_append, List.mem_map] at hselected
          rcases hselected with ⟨rest, hrest, rfl⟩ | hselected
          · obtain ⟨hlength, hmem, hnodup⟩ :=
              inductionHypothesis htail size rest hrest
            refine ⟨by simp [hlength], ?_, ?_⟩
            · intro vertex hvertex
              rcases List.mem_cons.mp hvertex with rfl | hvertex
              · simp
              · exact List.mem_cons_of_mem head (hmem vertex hvertex)
            · rw [List.nodup_cons]
              exact ⟨fun hmemHead => hhead (hmem head hmemHead), hnodup⟩
          · obtain ⟨hlength, hmem, hnodup⟩ :=
              inductionHypothesis htail (size + 1) selected hselected
            exact ⟨hlength, fun vertex hvertex =>
              List.mem_cons_of_mem head (hmem vertex hvertex), hnodup⟩

private theorem motifFourSubsets_valid
    {vertices : List MotifVertex} (hvertices : vertices ∈ motifFourSubsets) :
    vertices.length = 4 ∧ vertices.Nodup := by
  have hvalid := combinations_valid (List.finRange 7)
    (by native_decide) 4 vertices
      (by simpa [motifFourSubsets] using hvertices)
  exact ⟨hvalid.1, hvalid.2.2⟩

private theorem fourTuple_has_canonical_subset
    (first second third fourth : MotifVertex)
    (hnodup : [first, second, third, fourth].Nodup) :
    ∃ vertices, vertices ∈ motifFourSubsets ∧
      ∀ vertex, vertex ∈ vertices ↔
        vertex ∈ [first, second, third, fourth] := by
  native_decide +revert

theorem localR44Admissible_iff_fourSets
    (localEdges : LocalEdgeAssignment) :
    LocalR44Admissible localEdges ↔
      EveryFourTupleHasBothColors localEdges := by
  rw [localR44Admissible_iff]
  constructor
  · intro hall first second third fourth hnodup
    obtain ⟨vertices, hvertices, hmembership⟩ :=
      fourTuple_has_canonical_subset first second third fourth hnodup
    obtain ⟨⟨truePair, htruePair, htrue⟩,
      ⟨falsePair, hfalsePair, hfalse⟩⟩ := hall _ hvertices
    have htrueData := (mem_motifPairsWithin_iff _ _ _).1 htruePair
    have hfalseData := (mem_motifPairsWithin_iff _ _ _).1 hfalsePair
    constructor
    · exact ⟨truePair.1, (hmembership _).1 htrueData.1,
        truePair.2, (hmembership _).1 htrueData.2.1,
        (fun hequal => (Nat.ne_of_lt htrueData.2.2)
          (congrArg Fin.val hequal)),
        by simpa [unorderedLocalEdge, htrueData.2.2] using htrue⟩
    · exact ⟨falsePair.1, (hmembership _).1 hfalseData.1,
        falsePair.2, (hmembership _).1 hfalseData.2.1,
        (fun hequal => (Nat.ne_of_lt hfalseData.2.2)
          (congrArg Fin.val hequal)),
        by simpa [unorderedLocalEdge, hfalseData.2.2] using hfalse⟩
  · intro hall vertices hvertices
    have hvalid := motifFourSubsets_valid hvertices
    match vertices, hvalid.1 with
    | [first, second, third, fourth], _ =>
      have hnodup : [first, second, third, fourth].Nodup := hvalid.2
      obtain ⟨⟨trueLeft, htrueLeft, trueRight, htrueRight,
          htrueNe, htrue⟩,
        ⟨falseLeft, hfalseLeft, falseRight, hfalseRight,
          hfalseNe, hfalse⟩⟩ := hall first second third fourth hnodup
      constructor
      · by_cases hordered : trueLeft < trueRight
        · exact ⟨(trueLeft, trueRight),
            (mem_motifPairsWithin_iff _ _ _).2
              ⟨htrueLeft, htrueRight, hordered⟩,
            by simpa [unorderedLocalEdge, hordered] using htrue⟩
        · have hreverse : trueRight < trueLeft :=
            fin_lt_of_not_lt_of_ne hordered htrueNe
          exact ⟨(trueRight, trueLeft),
            (mem_motifPairsWithin_iff _ _ _).2
              ⟨htrueRight, htrueLeft, hreverse⟩,
            by simpa [unorderedLocalEdge, hordered, hreverse] using htrue⟩
      · by_cases hordered : falseLeft < falseRight
        · exact ⟨(falseLeft, falseRight),
            (mem_motifPairsWithin_iff _ _ _).2
              ⟨hfalseLeft, hfalseRight, hordered⟩,
            by simpa [unorderedLocalEdge, hordered] using hfalse⟩
        · have hreverse : falseRight < falseLeft :=
            fin_lt_of_not_lt_of_ne hordered hfalseNe
          exact ⟨(falseRight, falseLeft),
            (mem_motifPairsWithin_iff _ _ _).2
              ⟨hfalseRight, hfalseLeft, hreverse⟩,
            by simpa [unorderedLocalEdge, hordered, hreverse] using hfalse⟩

private theorem everyFourTuple_congr
    {leftEdges rightEdges : LocalEdgeAssignment}
    (hequal : ∀ left right,
      unorderedLocalEdge leftEdges left right =
        unorderedLocalEdge rightEdges left right) :
    EveryFourTupleHasBothColors leftEdges ↔
      EveryFourTupleHasBothColors rightEdges := by
  constructor
  · intro hall first second third fourth hnodup
    simpa only [hequal] using hall first second third fourth hnodup
  · intro hall first second third fourth hnodup
    simpa only [← hequal] using hall first second third fourth hnodup

private theorem everyFourTuple_permute_forward
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (hadmissible : EveryFourTupleHasBothColors localEdges) :
    EveryFourTupleHasBothColors (permuteLocalEdges permutation localEdges) := by
  intro first second third fourth hnodup
  have hmappedNodup :
      [permutation first, permutation second,
        permutation third, permutation fourth].Nodup := by
    change ([first, second, third, fourth].map permutation).Nodup
    exact hnodup.map permutation (fun left right hne hequal =>
      hne (permutation.injective hequal))
  obtain ⟨⟨trueLeft, htrueLeft, trueRight, htrueRight,
      htrueNe, htrue⟩,
    ⟨falseLeft, hfalseLeft, falseRight, hfalseRight,
      hfalseNe, hfalse⟩⟩ := hadmissible
        (permutation first) (permutation second)
        (permutation third) (permutation fourth) hmappedNodup
  change trueLeft ∈ [first, second, third, fourth].map permutation at htrueLeft
  change trueRight ∈ [first, second, third, fourth].map permutation at htrueRight
  change falseLeft ∈ [first, second, third, fourth].map permutation at hfalseLeft
  change falseRight ∈ [first, second, third, fourth].map permutation at hfalseRight
  obtain ⟨trueLeftSource, htrueLeftSource, rfl⟩ :=
    List.mem_map.mp htrueLeft
  obtain ⟨trueRightSource, htrueRightSource, rfl⟩ :=
    List.mem_map.mp htrueRight
  obtain ⟨falseLeftSource, hfalseLeftSource, rfl⟩ :=
    List.mem_map.mp hfalseLeft
  obtain ⟨falseRightSource, hfalseRightSource, rfl⟩ :=
    List.mem_map.mp hfalseRight
  constructor
  · exact ⟨trueLeftSource, htrueLeftSource,
      trueRightSource, htrueRightSource,
      (fun hequal => htrueNe (congrArg permutation hequal)),
      by simpa only [unorderedLocalEdge_permute] using htrue⟩
  · exact ⟨falseLeftSource, hfalseLeftSource,
      falseRightSource, hfalseRightSource,
      (fun hequal => hfalseNe (congrArg permutation hequal)),
      by simpa only [unorderedLocalEdge_permute] using hfalse⟩

theorem localR44Admissible_permute_forward
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (hadmissible : LocalR44Admissible localEdges) :
    LocalR44Admissible (permuteLocalEdges permutation localEdges) := by
  apply (localR44Admissible_iff_fourSets _).2
  exact everyFourTuple_permute_forward permutation localEdges
    ((localR44Admissible_iff_fourSets _).1 hadmissible)

theorem unorderedLocalEdge_permute_symm_permute
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (left right : MotifVertex) :
    unorderedLocalEdge
        (permuteLocalEdges permutation.symm
          (permuteLocalEdges permutation localEdges)) left right =
      unorderedLocalEdge localEdges left right := by
  rw [unorderedLocalEdge_permute, unorderedLocalEdge_permute]
  simp

/-- Local `R(4,4)` admissibility is exactly invariant under every genuine
permutation of the seven local vertices. -/
theorem localR44Admissible_permute_iff
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment) :
    LocalR44Admissible (permuteLocalEdges permutation localEdges) ↔
      LocalR44Admissible localEdges := by
  constructor
  · intro hadmissible
    have hdouble := localR44Admissible_permute_forward
      permutation.symm (permuteLocalEdges permutation localEdges) hadmissible
    apply (localR44Admissible_iff_fourSets _).2
    exact (everyFourTuple_congr
      (unorderedLocalEdge_permute_symm_permute permutation localEdges)).1
      ((localR44Admissible_iff_fourSets _).1 hdouble)
  · exact localR44Admissible_permute_forward permutation localEdges

/-! ## Exact transport of the 21-bit packing and partial cubes -/

theorem graph6EdgePosition_comm (left right : Nat) :
    graph6EdgePosition left right = graph6EdgePosition right left := by
  simp [graph6EdgePosition, Nat.min_comm, Nat.max_comm]

private theorem graph6EdgePosition_lt_21
    (left right : MotifVertex) (hne : left ≠ right) :
    graph6EdgePosition left.val right.val < 21 := by
  native_decide +revert

private theorem motifPairForPosition_at_ordered_pair
    (left right : MotifVertex) (hordered : left < right) :
    motifPairForPosition
        ⟨graph6EdgePosition left.val right.val,
          graph6EdgePosition_lt_21 left right (fun hequal =>
            (Nat.ne_of_lt hordered) (congrArg Fin.val hequal))⟩ =
      (left, right) := by
  native_decide +revert

/-- Target-indexed 21-bit list: the target pair at `position` reads the old
bit at the image of that pair under the permutation. -/
def permuteLocalMaskBits (permutation : FinPermutation 7) (mask : Nat) :
    List Bool :=
  List.ofFn fun position : Fin 21 =>
    let pair := motifPairForPosition position
    mask.testBit (graph6EdgePosition
      (permutation pair.1).val (permutation pair.2).val)

def permuteLocalMask (permutation : FinPermutation 7) (mask : Nat) : Nat :=
  (BitVec.ofBoolListLE (permuteLocalMaskBits permutation mask)).toNat

@[simp] theorem permuteLocalMaskBits_length
    (permutation : FinPermutation 7) (mask : Nat) :
    (permuteLocalMaskBits permutation mask).length = 21 := by
  simp [permuteLocalMaskBits]

theorem permuteLocalMask_lt
    (permutation : FinPermutation 7) (mask : Nat) :
    permuteLocalMask permutation mask < 2 ^ 21 := by
  unfold permuteLocalMask
  simpa using
    (BitVec.ofBoolListLE (permuteLocalMaskBits permutation mask)).isLt

theorem permuteLocalMask_testBit_position
    (permutation : FinPermutation 7) (mask : Nat) (position : Fin 21) :
    (permuteLocalMask permutation mask).testBit position.val =
      mask.testBit (graph6EdgePosition
        (permutation (motifPairForPosition position).1).val
        (permutation (motifPairForPosition position).2).val) := by
  unfold permuteLocalMask
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := permuteLocalMaskBits permutation mask) (i := position.val)
    (h := by simp) false]
  change
    (List.ofFn fun position : Fin 21 =>
      let pair := motifPairForPosition position
      mask.testBit (graph6EdgePosition
        (permutation pair.1).val
        (permutation pair.2).val))[position.val] = _
  rw [List.getElem_ofFn]

theorem permuteLocalMask_testBit_orderedPair
    (permutation : FinPermutation 7) (mask : Nat)
    (left right : MotifVertex) (hordered : left < right) :
    (permuteLocalMask permutation mask).testBit
        (graph6EdgePosition left.val right.val) =
      mask.testBit (graph6EdgePosition
        (permutation left).val (permutation right).val) := by
  let position : Fin 21 :=
    ⟨graph6EdgePosition left.val right.val,
      graph6EdgePosition_lt_21 left right (fun hequal =>
        (Nat.ne_of_lt hordered) (congrArg Fin.val hequal))⟩
  have hpair : motifPairForPosition position = (left, right) := by
    exact motifPairForPosition_at_ordered_pair left right hordered
  have hbit := permuteLocalMask_testBit_position permutation mask position
  simpa [position, hpair] using hbit

theorem permuteLocalMask_testBit_pair
    (permutation : FinPermutation 7) (mask : Nat)
    (left right : MotifVertex) (hne : left ≠ right) :
    (permuteLocalMask permutation mask).testBit
        (graph6EdgePosition left.val right.val) =
      mask.testBit (graph6EdgePosition
        (permutation left).val (permutation right).val) := by
  by_cases hordered : left < right
  · exact permuteLocalMask_testBit_orderedPair
      permutation mask left right hordered
  · have hreverse := fin_lt_of_not_lt_of_ne hordered hne
    rw [graph6EdgePosition_comm left.val right.val,
      permuteLocalMask_testBit_orderedPair
        permutation mask right left hreverse,
      graph6EdgePosition_comm (permutation right).val (permutation left).val]

def permuteCube (permutation : FinPermutation 7) (cube : Cover6Cube) :
    Cover6Cube :=
  { ones := permuteLocalMask permutation cube.ones
    fixed := permuteLocalMask permutation cube.fixed }

/-- Orientation-free form of `CubeMatchesLocal`. -/
def CubeMatchesUnordered
    (localEdges : LocalEdgeAssignment) (cube : Cover6Cube) : Prop :=
  ∀ left right : MotifVertex, left ≠ right →
    cube.fixed.testBit (graph6EdgePosition left.val right.val) = true →
    unorderedLocalEdge localEdges left right =
      cube.ones.testBit (graph6EdgePosition left.val right.val)

theorem cubeMatchesLocal_iff_unordered
    (localEdges : LocalEdgeAssignment) (cube : Cover6Cube) :
    CubeMatchesLocal localEdges cube ↔
      CubeMatchesUnordered localEdges cube := by
  constructor
  · intro hmatch left right hne hfixed
    by_cases hordered : left < right
    · simpa [unorderedLocalEdge, hordered] using
        hmatch left right hordered hfixed
    · have hreverse := fin_lt_of_not_lt_of_ne hordered hne
      have hfixedReverse : cube.fixed.testBit
          (graph6EdgePosition right.val left.val) = true := by
        rwa [graph6EdgePosition_comm right.val left.val]
      have hsource := hmatch right left hreverse hfixedReverse
      simpa [unorderedLocalEdge, hordered, hreverse,
        graph6EdgePosition_comm right.val left.val] using hsource
  · intro hmatch left right hordered hfixed
    have hne : left ≠ right := fun hequal =>
      (Nat.ne_of_lt hordered) (congrArg Fin.val hequal)
    simpa [unorderedLocalEdge, hordered] using
      hmatch left right hne hfixed

/-- Cube matching is equivariant when both the assignment and both packed
cube masks are transported by the same `S_7` permutation. -/
theorem cubeMatchesLocal_permute_iff
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (cube : Cover6Cube) :
    CubeMatchesLocal
        (permuteLocalEdges permutation localEdges)
        (permuteCube permutation cube) ↔
      CubeMatchesLocal localEdges cube := by
  rw [cubeMatchesLocal_iff_unordered, cubeMatchesLocal_iff_unordered]
  constructor
  · intro htarget left right hne hfixed
    let targetLeft := permutation.symm left
    let targetRight := permutation.symm right
    have htargetNe : targetLeft ≠ targetRight := by
      intro hequal
      apply hne
      have := congrArg permutation hequal
      simpa [targetLeft, targetRight] using this
    have htargetFixed : (permuteCube permutation cube).fixed.testBit
        (graph6EdgePosition targetLeft.val targetRight.val) = true := by
      unfold permuteCube
      rw [permuteLocalMask_testBit_pair permutation cube.fixed
        targetLeft targetRight htargetNe]
      simpa [targetLeft, targetRight] using hfixed
    have htransported := htarget targetLeft targetRight
      htargetNe htargetFixed
    unfold permuteCube at htransported
    rw [unorderedLocalEdge_permute,
      permuteLocalMask_testBit_pair permutation cube.ones
        targetLeft targetRight htargetNe] at htransported
    simpa [targetLeft, targetRight] using htransported
  · intro hsource left right hne hfixed
    have himageNe : permutation left ≠ permutation right :=
      fun hequal => hne (permutation.injective hequal)
    have hsourceFixed : cube.fixed.testBit
        (graph6EdgePosition (permutation left).val
          (permutation right).val) = true := by
      unfold permuteCube at hfixed
      rwa [permuteLocalMask_testBit_pair permutation cube.fixed
        left right hne] at hfixed
    have hmatch := hsource (permutation left) (permutation right)
      himageNe hsourceFixed
    unfold permuteCube
    rw [unorderedLocalEdge_permute,
      permuteLocalMask_testBit_pair permutation cube.ones left right hne]
    exact hmatch

/-! ## Packing an arbitrary semantic local assignment -/

def localAssignmentMaskBits (localEdges : LocalEdgeAssignment) : List Bool :=
  List.ofFn fun position : Fin 21 =>
    let pair := motifPairForPosition position
    localEdges pair.1 pair.2

def localAssignmentMask (localEdges : LocalEdgeAssignment) : Nat :=
  (BitVec.ofBoolListLE (localAssignmentMaskBits localEdges)).toNat

@[simp] theorem localAssignmentMaskBits_length
    (localEdges : LocalEdgeAssignment) :
    (localAssignmentMaskBits localEdges).length = 21 := by
  simp [localAssignmentMaskBits]

theorem localAssignmentMask_lt (localEdges : LocalEdgeAssignment) :
    localAssignmentMask localEdges < 2 ^ 21 := by
  unfold localAssignmentMask
  simpa using (BitVec.ofBoolListLE
    (localAssignmentMaskBits localEdges)).isLt

theorem localAssignmentMask_testBit_position
    (localEdges : LocalEdgeAssignment) (position : Fin 21) :
    (localAssignmentMask localEdges).testBit position.val =
      localEdges (motifPairForPosition position).1
        (motifPairForPosition position).2 := by
  unfold localAssignmentMask
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD
    (l := localAssignmentMaskBits localEdges) (i := position.val)
    (h := by simp) false]
  change
    (List.ofFn fun position : Fin 21 =>
      let pair := motifPairForPosition position
      localEdges pair.1 pair.2)[position.val] = _
  rw [List.getElem_ofFn]

theorem maskLocalEdges_localAssignmentMask
    (localEdges : LocalEdgeAssignment)
    (left right : MotifVertex) (hordered : left < right) :
    maskLocalEdges (localAssignmentMask localEdges) left right =
      localEdges left right := by
  let position : Fin 21 :=
    ⟨graph6EdgePosition left.val right.val,
      graph6EdgePosition_lt_21 left right (fun hequal =>
        (Nat.ne_of_lt hordered) (congrArg Fin.val hequal))⟩
  have hpair : motifPairForPosition position = (left, right) :=
    motifPairForPosition_at_ordered_pair left right hordered
  have hbit := localAssignmentMask_testBit_position localEdges position
  simpa [maskLocalEdges, position, hpair] using hbit

theorem localR44Admissible_congr_ordered
    {leftEdges rightEdges : LocalEdgeAssignment}
    (hequal : ∀ left right : MotifVertex, left < right →
      leftEdges left right = rightEdges left right) :
    LocalR44Admissible leftEdges ↔ LocalR44Admissible rightEdges := by
  simp only [localR44Admissible_iff, EveryFourHasBothColors]
  constructor
  · intro hall vertices hvertices
    obtain ⟨⟨truePair, htruePair, htrue⟩,
      ⟨falsePair, hfalsePair, hfalse⟩⟩ := hall vertices hvertices
    have htrueOrdered :=
      (mem_motifPairsWithin_iff _ _ _).1 htruePair |>.2.2
    have hfalseOrdered :=
      (mem_motifPairsWithin_iff _ _ _).1 hfalsePair |>.2.2
    exact ⟨⟨truePair, htruePair,
        (hequal _ _ htrueOrdered).symm.trans htrue⟩,
      ⟨falsePair, hfalsePair,
        (hequal _ _ hfalseOrdered).symm.trans hfalse⟩⟩
  · intro hall vertices hvertices
    obtain ⟨⟨truePair, htruePair, htrue⟩,
      ⟨falsePair, hfalsePair, hfalse⟩⟩ := hall vertices hvertices
    have htrueOrdered :=
      (mem_motifPairsWithin_iff _ _ _).1 htruePair |>.2.2
    have hfalseOrdered :=
      (mem_motifPairsWithin_iff _ _ _).1 hfalsePair |>.2.2
    exact ⟨⟨truePair, htruePair,
        (hequal _ _ htrueOrdered).trans htrue⟩,
      ⟨falsePair, hfalsePair,
        (hequal _ _ hfalseOrdered).trans hfalse⟩⟩

theorem cubeMatchesLocal_congr_ordered
    {leftEdges rightEdges : LocalEdgeAssignment} (cube : Cover6Cube)
    (hequal : ∀ left right : MotifVertex, left < right →
      leftEdges left right = rightEdges left right) :
    CubeMatchesLocal leftEdges cube ↔
      CubeMatchesLocal rightEdges cube := by
  constructor <;> intro hmatch left right hordered hfixed
  · exact (hequal left right hordered).symm.trans
      (hmatch left right hordered hfixed)
  · exact (hequal left right hordered).trans
      (hmatch left right hordered hfixed)

/-- Any finite uniqueness theorem stated for packed masks automatically
extends to the semantic `LocalEdgeAssignment` interface. -/
theorem ordered_match_of_packed_unique
    (cube : Cover6Cube) (target : Nat)
    (hunique : ∀ mask, mask < 2 ^ 21 →
      CubeMatchesLocal (maskLocalEdges mask) cube →
      LocalR44Admissible (maskLocalEdges mask) → mask = target)
    (localEdges : LocalEdgeAssignment)
    (hadmissible : LocalR44Admissible localEdges)
    (hmatch : CubeMatchesLocal localEdges cube) :
    ∀ left right : MotifVertex, left < right →
      localEdges left right = maskLocalEdges target left right := by
  let mask := localAssignmentMask localEdges
  have hpointwise : ∀ left right : MotifVertex, left < right →
      maskLocalEdges mask left right = localEdges left right := by
    exact maskLocalEdges_localAssignmentMask localEdges
  have hpackedMatch : CubeMatchesLocal (maskLocalEdges mask) cube :=
    (cubeMatchesLocal_congr_ordered cube hpointwise).2 hmatch
  have hpackedAdmissible : LocalR44Admissible (maskLocalEdges mask) :=
    (localR44Admissible_congr_ordered hpointwise).2 hadmissible
  have htarget := hunique mask (localAssignmentMask_lt localEdges)
    hpackedMatch hpackedAdmissible
  intro left right hordered
  calc
    localEdges left right = maskLocalEdges mask left right :=
      (hpointwise left right hordered).symm
    _ = maskLocalEdges target left right := by rw [htarget]

/-! ## Relabelled motifs and the six finite representatives -/

/-- A local assignment is a copy of `motif` with target label `v` sent to
source motif label `permutation v`.  The relation is deliberately unordered,
so its transport law does not need case splits on label order. -/
def LocalEdgesMatchRelabeledMotif
    (localEdges : LocalEdgeAssignment) (permutation : FinPermutation 7)
    (motif : Graph) : Prop :=
  ∀ left right : MotifVertex, left ≠ right →
    unorderedLocalEdge localEdges left right =
      edge motif (permutation left).val (permutation right).val

theorem localEdgesMatchRelabeledMotif_permute
    (outer inner : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (motif : Graph)
    (hmatch : LocalEdgesMatchRelabeledMotif localEdges inner motif) :
    LocalEdgesMatchRelabeledMotif
      (permuteLocalEdges outer localEdges) (outer.trans inner) motif := by
  intro left right hne
  rw [unorderedLocalEdge_permute]
  exact hmatch (outer left) (outer right)
    (fun hequal => hne (outer.injective hequal))

private theorem unorderedLocalEdge_congr_ordered
    {leftEdges rightEdges : LocalEdgeAssignment}
    (hequal : ∀ left right : MotifVertex, left < right →
      leftEdges left right = rightEdges left right)
    (left right : MotifVertex) (hne : left ≠ right) :
    unorderedLocalEdge leftEdges left right =
      unorderedLocalEdge rightEdges left right := by
  by_cases hordered : left < right
  · simpa [unorderedLocalEdge, hordered] using hequal left right hordered
  · have hreverse := fin_lt_of_not_lt_of_ne hordered hne
    simpa [unorderedLocalEdge, hordered, hreverse] using
      hequal right left hreverse

theorem relabeledMotifMatch_of_ordered_eq
    {leftEdges rightEdges : LocalEdgeAssignment}
    (permutation : FinPermutation 7) (motif : Graph)
    (hequal : ∀ left right : MotifVertex, left < right →
      leftEdges left right = rightEdges left right)
    (hmatch : LocalEdgesMatchRelabeledMotif rightEdges permutation motif) :
    LocalEdgesMatchRelabeledMotif leftEdges permutation motif := by
  intro left right hne
  exact (unorderedLocalEdge_congr_ordered hequal left right hne).trans
    (hmatch left right hne)

private theorem representativeMotifPermutation0_valid :
    isPermutation [4, 5, 6, 0, 3, 1, 2] 7 = true := by native_decide
private theorem representativeMotifPermutation1_valid :
    isPermutation [3, 4, 5, 6, 1, 0, 2] 7 = true := by native_decide
private theorem representativeMotifPermutation2_valid :
    isPermutation [5, 2, 6, 3, 1, 0, 4] 7 = true := by native_decide
private theorem representativeMotifPermutation3_valid :
    isPermutation [5, 6, 3, 2, 0, 4, 1] 7 = true := by native_decide
private theorem representativeMotifPermutation4_valid :
    isPermutation [5, 3, 6, 4, 2, 0, 1] 7 = true := by native_decide
private theorem representativeMotifPermutation5_valid :
    isPermutation [6, 5, 4, 2, 3, 1, 0] 7 = true := by native_decide

noncomputable def representativeMotifPermutation0 : FinPermutation 7 :=
  listPermutationToFin [4, 5, 6, 0, 3, 1, 2] 7
    representativeMotifPermutation0_valid
noncomputable def representativeMotifPermutation1 : FinPermutation 7 :=
  listPermutationToFin [3, 4, 5, 6, 1, 0, 2] 7
    representativeMotifPermutation1_valid
noncomputable def representativeMotifPermutation2 : FinPermutation 7 :=
  listPermutationToFin [5, 2, 6, 3, 1, 0, 4] 7
    representativeMotifPermutation2_valid
noncomputable def representativeMotifPermutation3 : FinPermutation 7 :=
  listPermutationToFin [5, 6, 3, 2, 0, 4, 1] 7
    representativeMotifPermutation3_valid
noncomputable def representativeMotifPermutation4 : FinPermutation 7 :=
  listPermutationToFin [5, 3, 6, 4, 2, 0, 1] 7
    representativeMotifPermutation4_valid
noncomputable def representativeMotifPermutation5 : FinPermutation 7 :=
  listPermutationToFin [6, 5, 4, 2, 3, 1, 0] 7
    representativeMotifPermutation5_valid

theorem representativeTarget0_matches_motif :
    LocalEdgesMatchRelabeledMotif (maskLocalEdges 0x12098B)
      representativeMotifPermutation0 motifFGBacktickXo := by
  intro left right hne
  unfold representativeMotifPermutation0
  simp only [listPermutationToFin_apply_val]
  native_decide +revert

theorem representativeTarget1_matches_motif :
    LocalEdgesMatchRelabeledMotif (maskLocalEdges 0x3E6BE)
      representativeMotifPermutation1 motifFdWBraceW := by
  intro left right hne
  unfold representativeMotifPermutation1
  simp only [listPermutationToFin_apply_val]
  native_decide +revert

theorem representativeTarget2_matches_motif :
    LocalEdgesMatchRelabeledMotif (maskLocalEdges 0x386AE)
      representativeMotifPermutation2 motifFIIXw := by
  intro left right hne
  unfold representativeMotifPermutation2
  simp only [listPermutationToFin_apply_val]
  native_decide +revert

theorem representativeTarget3_matches_motif :
    LocalEdgesMatchRelabeledMotif (maskLocalEdges 0x49CF5)
      representativeMotifPermutation3 motifFHFLw := by
  intro left right hne
  unfold representativeMotifPermutation3
  simp only [listPermutationToFin_apply_val]
  native_decide +revert

theorem representativeTarget4_matches_motif :
    LocalEdgesMatchRelabeledMotif (maskLocalEdges 0x8897E)
      representativeMotifPermutation4 motifFKDhw := by
  intro left right hne
  unfold representativeMotifPermutation4
  simp only [listPermutationToFin_apply_val]
  native_decide +revert

theorem representativeTarget5_matches_motif :
    LocalEdgesMatchRelabeledMotif (maskLocalEdges 0x28EED)
      representativeMotifPermutation5 motifFAtHCaretG := by
  intro left right hne
  unfold representativeMotifPermutation5
  simp only [listPermutationToFin_apply_val]
  native_decide +revert

def CubeForcesRelabeledMotif
    (cube : Cover6Cube) (permutation : FinPermutation 7)
    (motif : Graph) : Prop :=
  ∀ localEdges, LocalR44Admissible localEdges →
    CubeMatchesLocal localEdges cube →
    LocalEdgesMatchRelabeledMotif localEdges permutation motif

theorem representativeCube0_forces_motif :
    CubeForcesRelabeledMotif representativeCube0
      representativeMotifPermutation0 motifFGBacktickXo := by
  intro localEdges hadmissible hmatch
  apply relabeledMotifMatch_of_ordered_eq
    representativeMotifPermutation0 motifFGBacktickXo
  · exact ordered_match_of_packed_unique representativeCube0 0x12098B
      (fun mask hmask hcube hr44 =>
        representativeCube0_match_r44_unique mask hmask hcube hr44)
      localEdges hadmissible hmatch
  · exact representativeTarget0_matches_motif

theorem representativeCube1_forces_motif :
    CubeForcesRelabeledMotif representativeCube1
      representativeMotifPermutation1 motifFdWBraceW := by
  intro localEdges hadmissible hmatch
  apply relabeledMotifMatch_of_ordered_eq
    representativeMotifPermutation1 motifFdWBraceW
  · exact ordered_match_of_packed_unique representativeCube1 0x3E6BE
      (fun mask hmask hcube hr44 =>
        representativeCube1_match_r44_unique mask hmask hcube hr44)
      localEdges hadmissible hmatch
  · exact representativeTarget1_matches_motif

theorem representativeCube2_forces_motif :
    CubeForcesRelabeledMotif representativeCube2
      representativeMotifPermutation2 motifFIIXw := by
  intro localEdges hadmissible hmatch
  apply relabeledMotifMatch_of_ordered_eq
    representativeMotifPermutation2 motifFIIXw
  · exact ordered_match_of_packed_unique representativeCube2 0x386AE
      (fun mask hmask hcube hr44 =>
        representativeCube2_match_r44_unique mask hmask hcube hr44)
      localEdges hadmissible hmatch
  · exact representativeTarget2_matches_motif

theorem representativeCube3_forces_motif :
    CubeForcesRelabeledMotif representativeCube3
      representativeMotifPermutation3 motifFHFLw := by
  intro localEdges hadmissible hmatch
  apply relabeledMotifMatch_of_ordered_eq
    representativeMotifPermutation3 motifFHFLw
  · exact ordered_match_of_packed_unique representativeCube3 0x49CF5
      (fun mask hmask hcube hr44 =>
        representativeCube3_match_r44_unique mask hmask hcube hr44)
      localEdges hadmissible hmatch
  · exact representativeTarget3_matches_motif

theorem representativeCube4_forces_motif :
    CubeForcesRelabeledMotif representativeCube4
      representativeMotifPermutation4 motifFKDhw := by
  intro localEdges hadmissible hmatch
  apply relabeledMotifMatch_of_ordered_eq
    representativeMotifPermutation4 motifFKDhw
  · exact ordered_match_of_packed_unique representativeCube4 0x8897E
      (fun mask hmask hcube hr44 =>
        representativeCube4_match_r44_unique mask hmask hcube hr44)
      localEdges hadmissible hmatch
  · exact representativeTarget4_matches_motif

theorem representativeCube5_forces_motif :
    CubeForcesRelabeledMotif representativeCube5
      representativeMotifPermutation5 motifFAtHCaretG := by
  intro localEdges hadmissible hmatch
  apply relabeledMotifMatch_of_ordered_eq
    representativeMotifPermutation5 motifFAtHCaretG
  · exact ordered_match_of_packed_unique representativeCube5 0x28EED
      (fun mask hmask hcube hr44 =>
        representativeCube5_match_r44_unique mask hmask hcube hr44)
      localEdges hadmissible hmatch
  · exact representativeTarget5_matches_motif

/-! ## From six representatives to every cube in their S7 orbits -/

theorem cubeMatchesLocal_unpermute
    (permutation : FinPermutation 7) (localEdges : LocalEdgeAssignment)
    (cube : Cover6Cube)
    (hmatch : CubeMatchesLocal localEdges (permuteCube permutation cube)) :
    CubeMatchesLocal (permuteLocalEdges permutation.symm localEdges) cube := by
  apply (cubeMatchesLocal_iff_unordered _ _).2
  have htarget := (cubeMatchesLocal_iff_unordered _ _).1 hmatch
  intro left right hne hfixed
  let targetLeft := permutation.symm left
  let targetRight := permutation.symm right
  have htargetNe : targetLeft ≠ targetRight := by
    intro hequal
    apply hne
    have := congrArg permutation hequal
    simpa [targetLeft, targetRight] using this
  have htargetFixed : (permuteCube permutation cube).fixed.testBit
      (graph6EdgePosition targetLeft.val targetRight.val) = true := by
    unfold permuteCube
    rw [permuteLocalMask_testBit_pair permutation cube.fixed
      targetLeft targetRight htargetNe]
    simpa [targetLeft, targetRight] using hfixed
  have htransported := htarget targetLeft targetRight
    htargetNe htargetFixed
  unfold permuteCube at htransported
  rw [permuteLocalMask_testBit_pair permutation cube.ones
    targetLeft targetRight htargetNe] at htransported
  rw [unorderedLocalEdge_permute]
  simpa [targetLeft, targetRight] using htransported

/-- The orbit permutation and the representative-to-motif permutation compose
in the target-to-source direction used by the generator. -/
theorem permutedCube_forces_motif
    (outer inner : FinPermutation 7) (cube : Cover6Cube) (motif : Graph)
    (hforces : CubeForcesRelabeledMotif cube inner motif) :
    CubeForcesRelabeledMotif (permuteCube outer cube)
      (outer.trans inner) motif := by
  intro localEdges hadmissible hmatch
  let sourceEdges := permuteLocalEdges outer.symm localEdges
  have hsourceAdmissible : LocalR44Admissible sourceEdges := by
    exact (localR44Admissible_permute_iff outer.symm localEdges).2
      hadmissible
  have hsourceCube : CubeMatchesLocal sourceEdges cube := by
    exact cubeMatchesLocal_unpermute outer localEdges cube hmatch
  have hsourceMotif := hforces sourceEdges hsourceAdmissible hsourceCube
  intro left right hne
  have himageNe : outer left ≠ outer right :=
    fun hequal => hne (outer.injective hequal)
  have htransported := hsourceMotif (outer left) (outer right) himageNe
  unfold sourceEdges at htransported
  rw [unorderedLocalEdge_permute] at htransported
  simpa using htransported

def CubeInOrbitOf (cube representative : Cover6Cube) : Prop :=
  ∃ permutation : FinPermutation 7,
    cube = permuteCube permutation representative

/-- Semantic endpoint independent of an enumerated 25,200-row table: an
arbitrary cube carrying an orbit witness inherits the representative's motif
forcing theorem. -/
theorem orbitCube_forces_motif
    (cube representative : Cover6Cube)
    (inner : FinPermutation 7) (motif : Graph)
    (horbit : CubeInOrbitOf cube representative)
    (hforces : CubeForcesRelabeledMotif representative inner motif) :
    ∃ permutation : FinPermutation 7,
      CubeForcesRelabeledMotif cube permutation motif := by
  obtain ⟨outer, rfl⟩ := horbit
  exact ⟨outer.trans inner,
    permutedCube_forces_motif outer inner representative motif hforces⟩

#print axioms localR44Admissible_permute_iff
#print axioms permuteLocalMask_testBit_pair
#print axioms cubeMatchesLocal_permute_iff
#print axioms representativeCube0_forces_motif
#print axioms representativeCube5_forces_motif
#print axioms orbitCube_forces_motif

end LRATCatcher.Tests.R44Cover6S7Transport
