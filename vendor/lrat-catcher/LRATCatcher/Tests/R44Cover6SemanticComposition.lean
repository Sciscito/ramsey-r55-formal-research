import LRATCatcher.Tests.R44Cover6S7Transport
import LRATCatcher.Tests.R44Cover6Master8IndexedSource

/-!
  # Semantic composition for the cover6 degree-eight source

  This module joins the local cube semantics to the ambient induced-motif
  predicate and isolates the two finite payload obligations needed by the
  indexed Master8 source.  It also proves, propositionally, that a normalized
  degree-eight counterexample satisfies every base clause and every one of the
  eight normalized extra clauses.  No generated cube table is trusted here.
-/

namespace LRATCatcher.Tests.R44Cover6SemanticComposition

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44OrderTwelveTwoCenterSymmetry
open LRATCatcher.Tests.R44OrderTwelveTwoCenterCases
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6CubeBridge
open LRATCatcher.Tests.R44Cover6RepresentativeCubes
open LRATCatcher.Tests.R44Cover6S7Transport
open LRATCatcher.Tests.R44Cover6Master8IndexedSource

/-! ## From a relabelled local motif to an ambient occurrence -/

theorem symmetricEdgeVarTwelve_comm
    (left right : AmbientVertex) :
    symmetricEdgeVarTwelve left right =
      symmetricEdgeVarTwelve right left := by
  unfold symmetricEdgeVarTwelve
  by_cases hleft : left < right
  · have hright : ¬ right < left := fun hright =>
      (Nat.lt_asymm hleft hright)
    simp [hleft, hright]
  · by_cases hright : right < left
    · simp [hleft, hright]
    · have hleftVal : ¬ left.val < right.val := by simpa using hleft
      have hrightVal : ¬ right.val < left.val := by simpa using hright
      have hequal : left = right := Fin.ext (by omega)
      subst right
      simp

theorem unordered_embeddedLocalEdges
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (left right : MotifVertex) :
    unorderedLocalEdge (embeddedLocalEdges coloring embedding) left right =
      coloring (symmetricEdgeVarTwelve (embedding left) (embedding right)) := by
  unfold unorderedLocalEdge embeddedLocalEdges
  by_cases hordered : left < right
  · simp [hordered]
  · simp only [hordered, if_false]
    rw [symmetricEdgeVarTwelve_comm]

/-- Restricting an ambient `R(4,4)`-free coloring along any injective
seven-vertex embedding satisfies the executable local admissibility
predicate consumed by the six representative-cube theorems. -/
theorem embeddedLocalEdges_admissible
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hinjective : Function.Injective embedding) :
    LocalR44Admissible (embeddedLocalEdges coloring embedding) := by
  apply (localR44Admissible_iff_fourSets _).2
  intro first second third fourth hnodup
  let localVertices : List MotifVertex := [first, second, third, fourth]
  let ambientVertices : List Nat :=
    localVertices.map fun vertex => (embedding vertex).val
  have hambientLength : ambientVertices.length = 4 := by
    simp [ambientVertices, localVertices]
  have hambientBound : ∀ vertex ∈ ambientVertices, vertex < 12 := by
    intro vertex hvertex
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hvertex
    exact (embedding source).isLt
  have hambientNodup : ambientVertices.Nodup := by
    change (localVertices.map fun vertex => (embedding vertex).val).Nodup
    have hlocalNodup : localVertices.Nodup := by
      simpa [localVertices] using hnodup
    exact hlocalNodup.map (fun vertex => (embedding vertex).val)
      (fun left right hne hequal =>
        hne (hinjective (Fin.ext hequal)))
  have hnotRed := hfree.1 ambientVertices hambientLength hambientBound
    hambientNodup
  have hnotBlue := hfree.2 ambientVertices hambientLength hambientBound
    hambientNodup
  obtain ⟨falseVariable, hfalseVariable, hfalse⟩ :=
    exists_false_edge 12 ambientVertices coloring hnotRed
  obtain ⟨falseLeftValue, falseRightValue, hfalseLeftValue,
      hfalseRightValue, hfalseOrdered, rfl⟩ :=
    cliqueEdgeVars_mem 12 ambientVertices falseVariable hfalseVariable
  obtain ⟨falseLeft, hfalseLeft, hfalseLeftEq⟩ :=
    List.mem_map.mp hfalseLeftValue
  obtain ⟨falseRight, hfalseRight, hfalseRightEq⟩ :=
    List.mem_map.mp hfalseRightValue
  have hfalseImageOrdered :
      (embedding falseLeft).val < (embedding falseRight).val := by
    simpa [← hfalseLeftEq, ← hfalseRightEq] using hfalseOrdered
  have hfalseNe : falseLeft ≠ falseRight := by
    intro hequal
    subst falseRight
    exact (Nat.lt_irrefl _ hfalseImageOrdered)
  have hfalseLocal : unorderedLocalEdge
      (embeddedLocalEdges coloring embedding) falseLeft falseRight = false := by
    calc
      unorderedLocalEdge (embeddedLocalEdges coloring embedding)
          falseLeft falseRight =
          coloring (symmetricEdgeVarTwelve
            (embedding falseLeft) (embedding falseRight)) :=
        unordered_embeddedLocalEdges coloring embedding falseLeft falseRight
      _ = coloringEdge 12 coloring
          (embedding falseLeft).val (embedding falseRight).val :=
        coloring_symmetricEdgeVarTwelve coloring _ _
          (fun hequal => hfalseNe (hinjective hequal))
      _ = false := by
        simpa [coloringEdge, hfalseImageOrdered,
          ← hfalseLeftEq, ← hfalseRightEq] using hfalse
  obtain ⟨trueVariable, htrueVariable, htrue⟩ :=
    exists_true_edge 12 ambientVertices coloring hnotBlue
  obtain ⟨trueLeftValue, trueRightValue, htrueLeftValue,
      htrueRightValue, htrueOrdered, rfl⟩ :=
    cliqueEdgeVars_mem 12 ambientVertices trueVariable htrueVariable
  obtain ⟨trueLeft, htrueLeft, htrueLeftEq⟩ :=
    List.mem_map.mp htrueLeftValue
  obtain ⟨trueRight, htrueRight, htrueRightEq⟩ :=
    List.mem_map.mp htrueRightValue
  have htrueImageOrdered :
      (embedding trueLeft).val < (embedding trueRight).val := by
    simpa [← htrueLeftEq, ← htrueRightEq] using htrueOrdered
  have htrueNe : trueLeft ≠ trueRight := by
    intro hequal
    subst trueRight
    exact (Nat.lt_irrefl _ htrueImageOrdered)
  have htrueLocal : unorderedLocalEdge
      (embeddedLocalEdges coloring embedding) trueLeft trueRight = true := by
    calc
      unorderedLocalEdge (embeddedLocalEdges coloring embedding)
          trueLeft trueRight =
          coloring (symmetricEdgeVarTwelve
            (embedding trueLeft) (embedding trueRight)) :=
        unordered_embeddedLocalEdges coloring embedding trueLeft trueRight
      _ = coloringEdge 12 coloring
          (embedding trueLeft).val (embedding trueRight).val :=
        coloring_symmetricEdgeVarTwelve coloring _ _
          (fun hequal => htrueNe (hinjective hequal))
      _ = true := by
        simpa [coloringEdge, htrueImageOrdered,
          ← htrueLeftEq, ← htrueRightEq] using htrue
  exact ⟨⟨trueLeft, by simpa [localVertices] using htrueLeft,
      trueRight, by simpa [localVertices] using htrueRight,
      htrueNe, htrueLocal⟩,
    ⟨falseLeft, by simpa [localVertices] using hfalseLeft,
      falseRight, by simpa [localVertices] using hfalseRight,
      hfalseNe, hfalseLocal⟩⟩

def relabeledEmbedding
    (embedding : MotifEmbedding) (permutation : FinPermutation 7) :
    MotifEmbedding := fun vertex => embedding (permutation.symm vertex)

theorem relabeledEmbedding_injective
    (embedding : MotifEmbedding) (permutation : FinPermutation 7)
    (hinjective : Function.Injective embedding) :
    Function.Injective (relabeledEmbedding embedding permutation) := by
  intro left right hequal
  apply permutation.symm.injective
  exact hinjective hequal

theorem relabeledLocalMatch_gives_embeddingMatch
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (permutation : FinPermutation 7) (motif : Graph)
    (hmatch : LocalEdgesMatchRelabeledMotif
      (embeddedLocalEdges coloring embedding) permutation motif) :
    EmbeddingMatchesMotif coloring
      (relabeledEmbedding embedding permutation) motif := by
  intro left right hordered
  let sourceLeft := permutation.symm left
  let sourceRight := permutation.symm right
  have hne : sourceLeft ≠ sourceRight := by
    intro hequal
    have := congrArg permutation hequal
    have hleftRight : left ≠ right := fun hequal' =>
      (Nat.ne_of_lt hordered) (congrArg Fin.val hequal')
    exact hleftRight (by simpa [sourceLeft, sourceRight] using this)
  have hsource := hmatch sourceLeft sourceRight hne
  rw [unordered_embeddedLocalEdges] at hsource
  simpa [relabeledEmbedding, sourceLeft, sourceRight] using hsource

/-- A false partial blocker carrying a relabelled-motif forcing theorem is
already a declarative induced occurrence in the ambient coloring. -/
theorem relabeledCubeBlocker_false_gives_occurrence
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (cube : Cover6Cube) (permutation : FinPermutation 7) (motif : Graph)
    (hmotif : motif ∈ cover6Motifs)
    (hinjective : Function.Injective embedding)
    (hadmissible : LocalR44Admissible
      (embeddedLocalEdges coloring embedding))
    (hforces : CubeForcesRelabeledMotif cube permutation motif)
    (hfalse : CNF.Clause.eval coloring
      (cubeDimacsBlocker embedding cube) = false) :
    InducedMotifOccurrence 7 coloring motif := by
  have hcube :=
    (cubeDimacsBlocker_eval_false_iff coloring embedding cube).1 hfalse
  have hlocal := hforces _ hadmissible hcube
  have hfull := relabeledLocalMatch_gives_embeddingMatch
    coloring embedding permutation motif hlocal
  have hfullFalse := (motifDimacsBlocker_eval_false_iff coloring
    (relabeledEmbedding embedding permutation) motif).2 hfull
  exact false_motifDimacsBlocker_gives_occurrence coloring
    (relabeledEmbedding embedding permutation) motif hmotif
    (relabeledEmbedding_injective embedding permutation hinjective) hfullFalse

def AvoidsCover6 (coloring : Nat → Bool) : Prop :=
  ∀ motif, motif ∈ cover6Motifs →
    ¬ InducedMotifOccurrence 7 coloring motif

theorem orbitCubeBlocker_eval_true
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (cube representative : Cover6Cube)
    (inner : FinPermutation 7) (motif : Graph)
    (havoid : AvoidsCover6 coloring)
    (hmotif : motif ∈ cover6Motifs)
    (hinjective : Function.Injective embedding)
    (hadmissible : LocalR44Admissible
      (embeddedLocalEdges coloring embedding))
    (horbit : CubeInOrbitOf cube representative)
    (hforces : CubeForcesRelabeledMotif representative inner motif) :
    CNF.Clause.eval coloring (cubeDimacsBlocker embedding cube) = true := by
  obtain ⟨permutation, hcubeForces⟩ :=
    orbitCube_forces_motif cube representative inner motif horbit hforces
  cases hvalue : CNF.Clause.eval coloring
      (cubeDimacsBlocker embedding cube) with
  | true => rfl
  | false =>
      exact False.elim <| (havoid motif hmotif) <|
        relabeledCubeBlocker_false_gives_occurrence coloring embedding cube
          permutation motif hmotif hinjective hadmissible hcubeForces hvalue

/-! ## Exact interfaces for the two generated blocker families -/

/-- Root-free K7 clauses require only an equality with a full cube blocker,
plus the finite orbit witness supplied by the generated payload. -/
structure RootFreeBlockerWitness (clause : CNF.Clause Nat) where
  embedding : MotifEmbedding
  cube : Cover6Cube
  representative : Cover6Cube
  inner : FinPermutation 7
  motif : Graph
  motif_mem : motif ∈ cover6Motifs
  embedding_injective : Function.Injective embedding
  orbit : CubeInOrbitOf cube representative
  representative_forces :
    CubeForcesRelabeledMotif representative inner motif
  clause_eq : clause = cubeDimacsBlocker embedding cube

/-- Root-containing K6 clauses are projections of a full seven-vertex cube.
The lift payload must prove precisely that falsifying the projected clause
forces the full cube on the embedding containing the root. -/
structure RootContainingBlockerWitness
    (coloring : Nat → Bool) (clause : CNF.Clause Nat) where
  embedding : MotifEmbedding
  cube : Cover6Cube
  representative : Cover6Cube
  inner : FinPermutation 7
  motif : Graph
  motif_mem : motif ∈ cover6Motifs
  embedding_injective : Function.Injective embedding
  orbit : CubeInOrbitOf cube representative
  representative_forces :
    CubeForcesRelabeledMotif representative inner motif
  projected_false_gives_full_match :
    CNF.Clause.eval coloring clause = false →
      CubeMatchesLocal (embeddedLocalEdges coloring embedding) cube

theorem rootFreeBlockerWitness_eval_true
    {coloring : Nat → Bool} {clause : CNF.Clause Nat}
    (hfree : isRamseyFree 12 4 4 coloring)
    (havoid : AvoidsCover6 coloring)
    (witness : RootFreeBlockerWitness clause) :
    CNF.Clause.eval coloring clause = true := by
  have hadmissible := embeddedLocalEdges_admissible coloring witness.embedding
    hfree witness.embedding_injective
  rw [witness.clause_eq]
  exact orbitCubeBlocker_eval_true coloring witness.embedding witness.cube
    witness.representative witness.inner witness.motif havoid
    witness.motif_mem witness.embedding_injective hadmissible witness.orbit
    witness.representative_forces

theorem rootContainingBlockerWitness_eval_true
    {coloring : Nat → Bool} {clause : CNF.Clause Nat}
    (hfree : isRamseyFree 12 4 4 coloring)
    (havoid : AvoidsCover6 coloring)
    (witness : RootContainingBlockerWitness coloring clause) :
    CNF.Clause.eval coloring clause = true := by
  have hadmissible := embeddedLocalEdges_admissible coloring witness.embedding
    hfree witness.embedding_injective
  cases hvalue : CNF.Clause.eval coloring clause with
  | true => rfl
  | false =>
      obtain ⟨permutation, hforces⟩ := orbitCube_forces_motif
        witness.cube witness.representative witness.inner witness.motif
        witness.orbit witness.representative_forces
      have hlocal := hforces _ hadmissible
        (witness.projected_false_gives_full_match hvalue)
      have hfull := relabeledLocalMatch_gives_embeddingMatch coloring
        witness.embedding permutation witness.motif hlocal
      have hfullFalse := (motifDimacsBlocker_eval_false_iff coloring
        (relabeledEmbedding witness.embedding permutation)
        witness.motif).2 hfull
      exact False.elim <| (havoid witness.motif witness.motif_mem) <|
        false_motifDimacsBlocker_gives_occurrence coloring
          (relabeledEmbedding witness.embedding permutation) witness.motif
          witness.motif_mem
          (relabeledEmbedding_injective witness.embedding permutation
            witness.embedding_injective)
          hfullFalse

/-! ## DIMACS indexing lemmas for the base formula -/

private theorem pythonCombinations_valid {Alpha : Type} [DecidableEq Alpha]
    (source : List Alpha) (hsource : source.Nodup) :
    ∀ size selected, selected ∈ pythonCombinations source size →
      selected.length = size ∧
      (∀ value ∈ selected, value ∈ source) ∧ selected.Nodup := by
  induction source with
  | nil =>
      intro size selected hselected
      cases size with
      | zero =>
          simp [pythonCombinations] at hselected
          subst selected
          simp
      | succ size => simp [pythonCombinations] at hselected
  | cons head tail inductionHypothesis =>
      have hhead : head ∉ tail := (List.nodup_cons.mp hsource).1
      have htail : tail.Nodup := (List.nodup_cons.mp hsource).2
      intro size selected hselected
      cases size with
      | zero =>
          simp [pythonCombinations] at hselected
          subst selected
          simp
      | succ size =>
          simp only [pythonCombinations, List.mem_append, List.mem_map] at hselected
          rcases hselected with ⟨rest, hrest, rfl⟩ | hselected
          · obtain ⟨hlength, hmem, hnodup⟩ :=
              inductionHypothesis htail size rest hrest
            refine ⟨by simp [hlength], ?_, ?_⟩
            · intro value hvalue
              rcases List.mem_cons.mp hvalue with rfl | hvalue
              · simp
              · exact List.mem_cons_of_mem head (hmem value hvalue)
            · rw [List.nodup_cons]
              exact ⟨fun hmemHead => hhead (hmem head hmemHead), hnodup⟩
          · obtain ⟨hlength, hmem, hnodup⟩ :=
              inductionHypothesis htail (size + 1) selected hselected
            exact ⟨hlength, fun value hvalue =>
              List.mem_cons_of_mem head (hmem value hvalue), hnodup⟩

private theorem singleton_mem_pythonCombinations_one
    {Alpha : Type} [DecidableEq Alpha] {source : List Alpha} {value : Alpha}
    (hvalue : value ∈ source) :
    [value] ∈ pythonCombinations source 1 := by
  induction source with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · simp [pythonCombinations]
      · simp only [pythonCombinations, List.mem_append, List.mem_map]
        exact Or.inr (inductionHypothesis hvalue)

private theorem pair_mem_pythonCombinations_two
    {Alpha : Type} [DecidableEq Alpha] {source : List Alpha}
    {left right : Alpha}
    (hleft : left ∈ source) (hright : right ∈ source)
    (hne : left ≠ right) :
    [left, right] ∈ pythonCombinations source 2 ∨
      [right, left] ∈ pythonCombinations source 2 := by
  induction source with
  | nil => simp at hleft
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hleft with rfl | hleft
      · have hrightTail : right ∈ tail := by
          rcases List.mem_cons.mp hright with hrightHead | hrightTail
          · exact False.elim (hne hrightHead.symm)
          · exact hrightTail
        exact Or.inl <| by
          simp only [pythonCombinations, List.mem_append, List.mem_map]
          exact Or.inl ⟨[right],
            singleton_mem_pythonCombinations_one hrightTail, rfl⟩
      · rcases List.mem_cons.mp hright with hrightHead | hright
        · have hheadPair : [head, left] ∈
              pythonCombinations (head :: tail) 2 := by
            simp only [pythonCombinations, List.mem_append, List.mem_map]
            exact Or.inl ⟨[left],
              singleton_mem_pythonCombinations_one hleft, rfl⟩
          exact Or.inr (by simpa [hrightHead] using hheadPair)
        · obtain hpair | hpair := inductionHypothesis hleft hright
          · exact Or.inl <| by
              simp only [pythonCombinations, List.mem_append, List.mem_map]
              exact Or.inr hpair
          · exact Or.inr <| by
              simp only [pythonCombinations, List.mem_append, List.mem_map]
              exact Or.inr hpair

theorem globalEdge_comm (left right : Nat) :
    globalEdge left right = globalEdge right left := by
  simp [globalEdge, Nat.min_comm, Nat.max_comm]

theorem globalEdge_mem_pythonPairVariables
    (items : List Nat) {left right : Nat}
    (hleft : left ∈ items) (hright : right ∈ items)
    (hne : left ≠ right) :
    globalEdge left right ∈ pythonPairVariables items := by
  obtain hpair | hpair :=
    pair_mem_pythonCombinations_two hleft hright hne
  · unfold pythonPairVariables
    rw [List.mem_filterMap]
    exact ⟨[left, right], hpair, by simp⟩
  · unfold pythonPairVariables
    rw [List.mem_filterMap]
    exact ⟨[right, left], hpair, by simp [globalEdge_comm]⟩

theorem globalEdge_eq_edgeVar_add_one
    {left right : Nat} (hleftRight : left < right) (hright : right < 12) :
    globalEdge left right = edgeVar 12 left right + 1 := by
  have hle : left ≤ right := Nat.le_of_lt hleftRight
  unfold globalEdge edgeVar
  rw [Nat.min_eq_left hle, Nat.max_eq_right hle]
  have hcoefficient : 24 - left - 1 = 23 - left := by omega
  rw [hcoefficient]
  rw [Nat.add_sub_assoc hle]
  omega

theorem dimacsLit_signed_globalEdge
    (isPositive : Bool) {left right : Nat}
    (hleftRight : left < right) (hright : right < 12) :
    LRATCatcher.dimacsLit
        (if isPositive then positive (globalEdge left right)
          else negative (globalEdge left right)) =
      (edgeVar 12 left right, isPositive) := by
  rw [globalEdge_eq_edgeVar_add_one hleftRight hright]
  cases isPositive with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      unfold negative LRATCatcher.dimacsLit
      have habs :
          (Int.ofNat (edgeVar 12 left right + 1)).natAbs =
            edgeVar 12 left right + 1 := rfl
      have hpositive :
          (0 : Int) < Int.ofNat (edgeVar 12 left right + 1) :=
        Int.natCast_pos.mpr (by omega)
      rw [Int.natAbs_neg, habs]
      apply Prod.ext
      · simp
      · change decide ((0 : Int) <
            -Int.ofNat (edgeVar 12 left right + 1)) = false
        simp
        exact Int.add_nonneg (Int.natCast_nonneg _)
          (show (0 : Int) ≤ 1 by decide)
  | true =>
      simp only [if_true]
      unfold positive LRATCatcher.dimacsLit
      have habs :
          (Int.ofNat (edgeVar 12 left right + 1)).natAbs =
            edgeVar 12 left right + 1 := rfl
      rw [habs]
      simp

theorem signedPairClause_eval_true
    (coloring : Nat → Bool) (items : List Nat) (isPositive : Bool)
    {left right : Nat}
    (hleft : left ∈ items) (hright : right ∈ items)
    (hleftRight : left < right) (hrightBound : right < 12)
    (hcolor : coloring (edgeVar 12 left right) = isPositive) :
    CNF.Clause.eval coloring
      (dimacsClause (signedVariables isPositive
        (pythonPairVariables items))) = true := by
  have hglobal : globalEdge left right ∈ pythonPairVariables items :=
    globalEdge_mem_pythonPairVariables items hleft hright
      (Nat.ne_of_lt hleftRight)
  let rawLiteral : Int :=
    if isPositive then positive (globalEdge left right)
    else negative (globalEdge left right)
  have hraw : rawLiteral ∈
      signedVariables isPositive (pythonPairVariables items) := by
    unfold rawLiteral signedVariables
    exact List.mem_map.mpr ⟨globalEdge left right, hglobal, rfl⟩
  have hparsed : LRATCatcher.dimacsLit rawLiteral ∈
      dimacsClause (signedVariables isPositive
        (pythonPairVariables items)) := by
    exact List.mem_map.mpr ⟨rawLiteral, hraw, rfl⟩
  rw [CNF.Clause.eval, List.any_eq_true]
  refine ⟨LRATCatcher.dimacsLit rawLiteral, hparsed, ?_⟩
  have hliteral := dimacsLit_signed_globalEdge isPositive
    hleftRight hrightBound
  change LRATCatcher.dimacsLit rawLiteral =
      (edgeVar 12 left right, isPositive) at hliteral
  rw [hliteral]
  simp [hcolor]

theorem mem_vertices_bounds
    {first count value : Nat} (hvalue : value ∈ vertices first count) :
    first ≤ value ∧ value < first + count := by
  unfold vertices at hvalue
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hvalue
  have hlt := List.mem_range.mp hoffset
  omega

theorem fourBlockItem_valid
    {index : Nat} (hindex : index < 330) :
    let item := (R44Cover6Master8IndexedSource.combinations 1 11 4).getD index []
    item.length = 4 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 12) ∧
      item.Nodup := by
  have hlength :
      (R44Cover6Master8IndexedSource.combinations 1 11 4).length = 330 := by
    native_decide
  have hbound : index <
      (R44Cover6Master8IndexedSource.combinations 1 11 4).length := by omega
  let item :=
    (R44Cover6Master8IndexedSource.combinations 1 11 4).getD index []
  have hmember : item ∈
      R44Cover6Master8IndexedSource.combinations 1 11 4 := by
    unfold item
    rw [← List.getElem_eq_getD
      (l := R44Cover6Master8IndexedSource.combinations 1 11 4)
      (i := index) (h := hbound) []]
    exact List.getElem_mem hbound
  have hvalid := pythonCombinations_valid (vertices 1 11)
    (by native_decide) 4 item
      (by simpa [R44Cover6Master8IndexedSource.combinations] using hmember)
  exact ⟨hvalid.1, fun value hvalue =>
    mem_vertices_bounds (hvalid.2.1 value hvalue), hvalid.2.2⟩

theorem positiveTriangleItem_valid
    {index : Nat} (hindex : index < 56) :
    let item := (R44Cover6Master8IndexedSource.combinations 1 8 3).getD index []
    item.length = 3 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 9) ∧
      item.Nodup := by
  have hlength :
      (R44Cover6Master8IndexedSource.combinations 1 8 3).length = 56 := by
    native_decide
  have hbound : index <
      (R44Cover6Master8IndexedSource.combinations 1 8 3).length := by omega
  let item :=
    (R44Cover6Master8IndexedSource.combinations 1 8 3).getD index []
  have hmember : item ∈
      R44Cover6Master8IndexedSource.combinations 1 8 3 := by
    unfold item
    rw [← List.getElem_eq_getD
      (l := R44Cover6Master8IndexedSource.combinations 1 8 3)
      (i := index) (h := hbound) []]
    exact List.getElem_mem hbound
  have hvalid := pythonCombinations_valid (vertices 1 8)
    (by native_decide) 3 item
      (by simpa [R44Cover6Master8IndexedSource.combinations] using hmember)
  exact ⟨hvalid.1, fun value hvalue =>
    mem_vertices_bounds (hvalid.2.1 value hvalue), hvalid.2.2⟩

theorem twoCenterBranch_root_true
    {coloring : Nat → Bool} {p q vertex : Nat}
    (hbranch : TwoCenterBranch coloring p q)
    (hlower : 1 ≤ vertex) (hupper : vertex < 9) :
    coloringEdge 12 coloring 0 vertex = true := by
  by_cases hone : vertex = 1
  · subst vertex
    exact hbranch.1
  · let position : Fin 7 := ⟨vertex - 2, by omega⟩
    have hedge := hbranch.2.1 position
    have hvertex : position.val + 2 = vertex := by
      dsimp [position]
      omega
    simpa [hvertex] using hedge

theorem twoCenterBranch_root_false
    {coloring : Nat → Bool} {p q vertex : Nat}
    (hbranch : TwoCenterBranch coloring p q)
    (hlower : 9 ≤ vertex) (hupper : vertex < 12) :
    coloringEdge 12 coloring 0 vertex = false := by
  let position : Fin 3 := ⟨vertex - 9, by omega⟩
  have hedge := hbranch.2.2.1 position
  have hvertex : position.val + 9 = vertex := by
    dsimp [position]
    omega
  simpa [hvertex] using hedge

/-- Every one of the 717 non-cube clauses follows propositionally from
ambient `R(4,4)` freeness and the normalized degree-eight root block. -/
theorem baseClause_eval_true
    (coloring : Nat → Bool) (p q index : Nat)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hbranch : TwoCenterBranch coloring p q)
    (hindex : index < 717) :
    CNF.Clause.eval coloring (dimacsClause (baseClause index)) = true := by
  by_cases hfour : index < 660
  · let item :=
      (R44Cover6Master8IndexedSource.combinations 1 11 4).getD (index / 2) []
    have hitemIndex : index / 2 < 330 := by omega
    have hvalid := fourBlockItem_valid hitemIndex
    change item.length = 4 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 12) ∧
      item.Nodup at hvalid
    by_cases hpositive : index % 2 = 1
    · have hnotBlue := hfree.2 item hvalid.1
          (fun value hvalue => (hvalid.2.1 value hvalue).2)
          hvalid.2.2
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_true_edge 12 item coloring hnotBlue
      obtain ⟨left, right, hleft, hright, hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 item dimacsVariable hvariable
      have hsatisfied := signedPairClause_eval_true coloring item true
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [baseClause, hfour, hpositive, item] using hsatisfied
    · have hnotRed := hfree.1 item hvalid.1
          (fun value hvalue => (hvalid.2.1 value hvalue).2)
          hvalid.2.2
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_false_edge 12 item coloring hnotRed
      obtain ⟨left, right, hleft, hright, hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 item dimacsVariable hvariable
      have hsatisfied := signedPairClause_eval_true coloring item false
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [baseClause, hfour, hpositive, item] using hsatisfied
  · by_cases hpositiveBlock : index < 716
    · let item :=
        (R44Cover6Master8IndexedSource.combinations 1 8 3).getD
          (index - 660) []
      have hitemIndex : index - 660 < 56 := by omega
      have hvalid := positiveTriangleItem_valid hitemIndex
      change item.length = 3 ∧
        (∀ value ∈ item, 1 ≤ value ∧ value < 9) ∧
        item.Nodup at hvalid
      let ambient := 0 :: item
      have hambientLength : ambient.length = 4 := by
        simp [ambient, hvalid.1]
      have hambientBound : ∀ value ∈ ambient, value < 12 := by
        intro value hvalue
        rcases List.mem_cons.mp hvalue with rfl | hvalue
        · omega
        · have hbounds := hvalid.2.1 value hvalue
          omega
      have hambientNodup : ambient.Nodup := by
        change (0 :: item).Nodup
        rw [List.nodup_cons]
        exact ⟨by
          intro hzero
          have hzeroBounds := hvalid.2.1 0 hzero
          omega, hvalid.2.2⟩
      have hnotRed := hfree.1 ambient hambientLength hambientBound
        hambientNodup
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_false_edge 12 ambient coloring hnotRed
      obtain ⟨left, right, hleftAmbient, hrightAmbient,
          hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 ambient dimacsVariable hvariable
      have hright : right ∈ item := by
        rcases List.mem_cons.mp hrightAmbient with hzero | hright
        · subst right
          omega
        · exact hright
      have hleft : left ∈ item := by
        rcases List.mem_cons.mp hleftAmbient with hzero | hleft
        · subst left
          have hroot := twoCenterBranch_root_true hbranch
            (hvalid.2.1 right hright).1 (hvalid.2.1 right hright).2
          have hrootRaw : coloring (edgeVar 12 0 right) = true := by
            simpa [coloringEdge, hleftRight] using hroot
          simp [hrootRaw] at hcolor
        · exact hleft
      have hsatisfied := signedPairClause_eval_true coloring item false
        hleft hright hleftRight
        (by have hbounds := hvalid.2.1 right hright; omega) hcolor
      simpa [baseClause, hfour, hpositiveBlock, item] using hsatisfied
    · have hindexEq : index = 716 := by omega
      subst index
      let item : List Nat := [9, 10, 11]
      let ambient : List Nat := 0 :: item
      have hnotBlue := hfree.2 ambient (by native_decide)
        (by native_decide) (by native_decide)
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_true_edge 12 ambient coloring hnotBlue
      obtain ⟨left, right, hleftAmbient, hrightAmbient,
          hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 ambient dimacsVariable hvariable
      have hright : right ∈ item := by
        rcases List.mem_cons.mp hrightAmbient with hzero | hright
        · subst right
          omega
        · exact hright
      have hrightBounds : 9 ≤ right ∧ right < 12 := by
        simp [item] at hright
        rcases hright with rfl | rfl | rfl <;> omega
      have hleft : left ∈ item := by
        rcases List.mem_cons.mp hleftAmbient with hzero | hleft
        · subst left
          have hroot := twoCenterBranch_root_false hbranch
            hrightBounds.1 hrightBounds.2
          have hrootRaw : coloring (edgeVar 12 0 right) = false := by
            simpa [coloringEdge, hleftRight] using hroot
          simp [hrootRaw] at hcolor
        · exact hleft
      have hsatisfied := signedPairClause_eval_true coloring item true
        hleft hright hleftRight hrightBounds.2 hcolor
      simpa [baseClause, item] using hsatisfied

/-! ## The seven retained sorting clauses and the bound `¬15` -/

theorem twoCenterBranch_second_left_raw
    {coloring : Nat → Bool} {p q : Nat}
    (hbranch : TwoCenterBranch coloring p q) (position : Fin 7) :
    coloring (edgeVar 12 1 (position.val + 2)) =
      decide (position.val < p) := by
  have hedge := hbranch.2.2.2.1 position
  have hordered : 1 < position.val + 2 := by omega
  simpa [coloringEdge, hordered] using hedge

theorem twoCenterBranch_second_right_raw
    {coloring : Nat → Bool} {p q : Nat}
    (hbranch : TwoCenterBranch coloring p q) (position : Fin 3) :
    coloring (edgeVar 12 1 (position.val + 9)) =
      decide (position.val < q) := by
  have hedge := hbranch.2.2.2.2 position
  have hordered : 1 < position.val + 9 := by omega
  simpa [coloringEdge, hordered] using hedge

theorem prefixImplicationClause_eval_true
    (coloring : Nat → Bool) (threshold : Nat)
    {leftVertex rightVertex leftRank rightRank : Nat}
    (hleftVertex : 1 < leftVertex) (hleftBound : leftVertex < 12)
    (hrightVertexLower : 1 < rightVertex)
    (hrightVertex : rightVertex < 12)
    (hranks : leftRank < rightRank)
    (hleft : coloring (edgeVar 12 1 leftVertex) =
      decide (leftRank < threshold))
    (hright : coloring (edgeVar 12 1 rightVertex) =
      decide (rightRank < threshold)) :
    CNF.Clause.eval coloring (dimacsClause
      [positive (globalEdge 1 leftVertex),
        negative (globalEdge 1 rightVertex)]) = true := by
  simp only [dimacsClause, List.map_cons, List.map_nil, CNF.Clause.eval,
    List.any_cons, List.any_nil, Bool.or_false]
  have hpositiveParsed : LRATCatcher.dimacsLit
      (positive (globalEdge 1 leftVertex)) =
        (edgeVar 12 1 leftVertex, true) := by
    simpa using dimacsLit_signed_globalEdge true hleftVertex hleftBound
  have hnegativeParsed : LRATCatcher.dimacsLit
      (negative (globalEdge 1 rightVertex)) =
        (edgeVar 12 1 rightVertex, false) := by
    simpa using dimacsLit_signed_globalEdge false
      hrightVertexLower hrightVertex
  rw [hpositiveParsed, hnegativeParsed]
  by_cases hbelow : leftRank < threshold
  · simp [hleft, hbelow]
  · have hrightNotBelow : ¬ rightRank < threshold := by omega
    simp [hright, hrightNotBelow]

theorem negativeUnitClause_eval_true
    (coloring : Nat → Bool) {vertex : Nat}
    (hvertex : 1 < vertex) (hbound : vertex < 12)
    (hcolor : coloring (edgeVar 12 1 vertex) = false) :
    CNF.Clause.eval coloring
      (dimacsClause [negative (globalEdge 1 vertex)]) = true := by
  simp only [dimacsClause, List.map_cons, List.map_nil, CNF.Clause.eval,
    List.any_cons, List.any_nil, Bool.or_false]
  have hnegativeParsed : LRATCatcher.dimacsLit
      (negative (globalEdge 1 vertex)) =
        (edgeVar 12 1 vertex, false) := by
    simpa using dimacsLit_signed_globalEdge false hvertex hbound
  rw [hnegativeParsed]
  simp [hcolor]

theorem normalizedExtraClause_eval_true
    (coloring : Nat → Bool) (p q index : Nat)
    (hbranch : TwoCenterBranch coloring p q)
    (hp : p ≤ 3) (hindex : index < 8) :
    CNF.Clause.eval coloring
      (dimacsClause (normalizedExtraClauses.getD index [])) = true := by
  have hcases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hsatisfied := prefixImplicationClause_eval_true coloring p
      (leftVertex := 2) (rightVertex := 3)
      (leftRank := 0) (rightRank := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_left_raw hbranch (0 : Fin 7))
      (twoCenterBranch_second_left_raw hbranch (1 : Fin 7))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hsatisfied := prefixImplicationClause_eval_true coloring p
      (leftVertex := 3) (rightVertex := 4)
      (leftRank := 1) (rightRank := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_left_raw hbranch (1 : Fin 7))
      (twoCenterBranch_second_left_raw hbranch (2 : Fin 7))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hsatisfied := prefixImplicationClause_eval_true coloring p
      (leftVertex := 5) (rightVertex := 6)
      (leftRank := 3) (rightRank := 4)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_left_raw hbranch (3 : Fin 7))
      (twoCenterBranch_second_left_raw hbranch (4 : Fin 7))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hsatisfied := prefixImplicationClause_eval_true coloring p
      (leftVertex := 6) (rightVertex := 7)
      (leftRank := 4) (rightRank := 5)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_left_raw hbranch (4 : Fin 7))
      (twoCenterBranch_second_left_raw hbranch (5 : Fin 7))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hsatisfied := prefixImplicationClause_eval_true coloring p
      (leftVertex := 7) (rightVertex := 8)
      (leftRank := 5) (rightRank := 6)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_left_raw hbranch (5 : Fin 7))
      (twoCenterBranch_second_left_raw hbranch (6 : Fin 7))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hsatisfied := prefixImplicationClause_eval_true coloring q
      (leftVertex := 9) (rightVertex := 10)
      (leftRank := 0) (rightRank := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_right_raw hbranch (0 : Fin 3))
      (twoCenterBranch_second_right_raw hbranch (1 : Fin 3))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hsatisfied := prefixImplicationClause_eval_true coloring q
      (leftVertex := 10) (rightVertex := 11)
      (leftRank := 1) (rightRank := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (twoCenterBranch_second_right_raw hbranch (1 : Fin 3))
      (twoCenterBranch_second_right_raw hbranch (2 : Fin 3))
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied
  · have hcenterFive := twoCenterBranch_second_left_raw hbranch (3 : Fin 7)
    change coloring (edgeVar 12 1 5) = decide (3 < p) at hcenterFive
    have hnotBelow : ¬ 3 < p := by omega
    have hfalse : coloring (edgeVar 12 1 5) = false := by
      simpa [hnotBelow] using hcenterFive
    have hsatisfied := negativeUnitClause_eval_true coloring
      (vertex := 5) (by omega) (by omega) hfalse
    simpa [normalizedExtraClauses, positive, negative, globalEdge] using hsatisfied

/-! ## Ordered 6,152-clause core view -/

def coreArrayPosition (position : Fin 6152) :
    Fin coreNormalizedFinIndices.size :=
  ⟨position.val, by rw [coreNormalizedIndexCount]; exact position.isLt⟩

def coreSourceIndex (position : Fin 6152) : Fin normalizedClauseCount :=
  coreNormalizedFinIndices[coreArrayPosition position]

def selectedCoreClause (position : Fin 6152) : CNF.Clause Nat :=
  normalizedSource.clauseAt (coreSourceIndex position)

def baseCorePosition (position : Fin 221) : Fin 6152 :=
  ⟨position.val, by omega⟩

def rootFreeCorePosition (position : Fin 3514) : Fin 6152 :=
  ⟨221 + position.val, by omega⟩

def rootContainingCorePosition (position : Fin 2409) : Fin 6152 :=
  ⟨3735 + position.val, by omega⟩

def extraCorePosition (position : Fin 8) : Fin 6152 :=
  ⟨6144 + position.val, by omega⟩

/- These four finite theorems certify that the provider split is the exact
ordered taxonomy of the tracked core selection, rather than a convention
assumed by the semantic theorem. -/
theorem baseCoreSourceIndex_lt (position : Fin 221) :
    (coreSourceIndex (baseCorePosition position)).val < 717 := by
  native_decide +revert

theorem rootFreeCoreSourceIndex_range (position : Fin 3514) :
    717 ≤ (coreSourceIndex (rootFreeCorePosition position)).val ∧
      (coreSourceIndex (rootFreeCorePosition position)).val < 3211197 := by
  native_decide +revert

theorem rootContainingCoreSourceIndex_range (position : Fin 2409) :
    3211197 ≤
        (coreSourceIndex (rootContainingCorePosition position)).val ∧
      (coreSourceIndex (rootContainingCorePosition position)).val <
        sourceClauseCount := by
  native_decide +revert

theorem extraCoreSourceIndex_eq (position : Fin 8) :
    (coreSourceIndex (extraCorePosition position)).val =
      sourceClauseCount + position.val := by
  native_decide +revert

theorem normalizedSource_baseClause
    (index : Fin normalizedClauseCount) (hindex : index.val < 717) :
    normalizedSource.clauseAt index =
      dimacsClause (baseClause index.val) := by
  have hsource : index.val < sourceClauseCount := by
    unfold sourceClauseCount
    omega
  have hsourceLiteral : index.val < 3367437 := by
    simpa [sourceClauseCount] using hsource
  simp [normalizedSource, normalizedClauseDimacs, master8ClauseDimacs,
    sourceClauseCount, hindex, hsourceLiteral]

theorem normalizedSource_extraClause (position : Fin 8) :
    normalizedSource.clauseAt
        (coreSourceIndex (extraCorePosition position)) =
      dimacsClause (normalizedExtraClauses.getD position.val []) := by
  have hindex := extraCoreSourceIndex_eq position
  have hnotSource : ¬ sourceClauseCount + position.val < sourceClauseCount := by
    omega
  have hnotSourceLiteral :
      ¬ 3367437 + position.val < 3367437 := by
    change ¬ 3367437 + position.val < 3367437 at hnotSource
    exact hnotSource
  simp [normalizedSource, normalizedClauseDimacs, hindex,
    sourceClauseCount, normalizedClauseCount, hnotSourceLiteral]

/-- Exactly the two payload-dependent regions of the compact core.  A future
generated data module supplies these witnesses in core order; base and extra
clauses are discharged independently above. -/
structure CoreBlockerWitnessProvider (coloring : Nat → Bool) where
  rootFree : ∀ position : Fin 3514,
    RootFreeBlockerWitness
      (selectedCoreClause (rootFreeCorePosition position))
  rootContaining : ∀ position : Fin 2409,
    RootContainingBlockerWitness coloring
      (selectedCoreClause (rootContainingCorePosition position))

/- IMPORTANT TRUST BOUNDARY: this module does not construct the provider.
Consequently the endpoint below is conditional and is not, by itself, a
proof of the cover6 degree-eight theorem.  The remaining generated module
must check every one of the 3,514 K7 orbit witnesses and 2,409 K6 full lifts. -/

theorem selectedCoreClause_eval_true
    (coloring : Nat → Bool) (p q : Nat)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hbranch : TwoCenterBranch coloring p q)
    (hp : p ≤ 3) (havoid : AvoidsCover6 coloring)
    (provider : CoreBlockerWitnessProvider coloring)
    (position : Fin 6152) :
    CNF.Clause.eval coloring (selectedCoreClause position) = true := by
  by_cases hbase : position.val < 221
  · let basePosition : Fin 221 := ⟨position.val, hbase⟩
    have hposition : baseCorePosition basePosition = position := by
      apply Fin.ext
      simp [baseCorePosition, basePosition]
    rw [← hposition]
    have hsourceBound := baseCoreSourceIndex_lt basePosition
    rw [selectedCoreClause, normalizedSource_baseClause _ hsourceBound]
    exact baseClause_eval_true coloring p q
      (coreSourceIndex (baseCorePosition basePosition)).val
      hfree hbranch hsourceBound
  · by_cases hrootFree : position.val < 3735
    · let payloadPosition : Fin 3514 :=
        ⟨position.val - 221, by omega⟩
      have hposition : rootFreeCorePosition payloadPosition = position := by
        apply Fin.ext
        simp [rootFreeCorePosition, payloadPosition]
        omega
      rw [← hposition]
      exact rootFreeBlockerWitness_eval_true hfree havoid
        (provider.rootFree payloadPosition)
    · by_cases hrootContaining : position.val < 6144
      · let payloadPosition : Fin 2409 :=
          ⟨position.val - 3735, by omega⟩
        have hposition :
            rootContainingCorePosition payloadPosition = position := by
          apply Fin.ext
          simp [rootContainingCorePosition, payloadPosition]
          omega
        rw [← hposition]
        exact rootContainingBlockerWitness_eval_true hfree havoid
          (provider.rootContaining payloadPosition)
      · let extraPosition : Fin 8 :=
          ⟨position.val - 6144, by omega⟩
        have hposition : extraCorePosition extraPosition = position := by
          apply Fin.ext
          simp [extraCorePosition, extraPosition]
          omega
        rw [← hposition, selectedCoreClause,
          normalizedSource_extraClause extraPosition]
        exact normalizedExtraClause_eval_true coloring p q extraPosition.val
          hbranch hp extraPosition.isLt

theorem normalizedCoreSelection_eval_true
    (coloring : Nat → Bool) (p q : Nat)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hbranch : TwoCenterBranch coloring p q)
    (hp : p ≤ 3) (havoid : AvoidsCover6 coloring)
    (provider : CoreBlockerWitnessProvider coloring) :
    CNF.eval coloring
      (normalizedSource.selectCNF coreNormalizedFinIndices) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hsize :
      (normalizedSource.selectCNF coreNormalizedFinIndices).clauses.size =
        6152 := by
    unfold R44Cover6Master8CoreBridge.IndexedCNFSource.selectCNF
    simpa using coreNormalizedIndexCount
  let position : Fin 6152 := ⟨index, by omega⟩
  have hsatisfied := selectedCoreClause_eval_true coloring p q hfree
    hbranch hp havoid provider position
  simpa [R44Cover6Master8CoreBridge.IndexedCNFSource.selectCNF,
    selectedCoreClause, coreSourceIndex, coreArrayPosition, position]
    using hsatisfied

theorem avoidsCover6_twoCenter_iff (coloring : Nat → Bool) :
    AvoidsCover6 coloring ↔ AvoidsCover6 (twoCenterColoring coloring) := by
  constructor
  · intro havoid motif hmotif hoccurrence
    exact havoid motif hmotif
      ((twoCenter_inducedMotifOccurrence_iff coloring motif).mpr hoccurrence)
  · intro havoid motif hmotif hoccurrence
    exact havoid motif hmotif
      ((twoCenter_inducedMotifOccurrence_iff coloring motif).mp hoccurrence)

/-- Final semantic composition endpoint.  Once the two finite witness
providers are generated and checked, a degree-eight cover6-avoiding
counterexample would satisfy the exact tracked core, contradicting its
already replayed LRAT refutation. -/
theorem no_degreeEight_cover6_avoiding_of_coreProvider
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 8)
    (havoid : AvoidsCover6 coloring)
    (provider : CoreBlockerWitnessProvider (twoCenterColoring coloring)) :
    False := by
  let normalized := twoCenterColoring coloring
  have hnormalizedFree : isRamseyFree 12 4 4 normalized :=
    (twoCenter_isRamseyFree_iff coloring).mp hfree
  have hbranch : TwoCenterBranch normalized
      (pValue coloring) (qValue coloring) :=
    twoCenter_branch coloring hdegree
  have hp : pValue coloring ≤ 3 := pValue_le_three hfree hdegree
  have hnormalizedAvoid : AvoidsCover6 normalized :=
    (avoidsCover6_twoCenter_iff coloring).mp havoid
  have htrue := normalizedCoreSelection_eval_true normalized
    (pValue coloring) (qValue coloring) hnormalizedFree hbranch hp
    hnormalizedAvoid provider
  have hfalse := normalizedCoreSelection_unsat normalized
  exact Bool.noConfusion (htrue.symm.trans hfalse)

#print axioms relabeledCubeBlocker_false_gives_occurrence
#print axioms embeddedLocalEdges_admissible
#print axioms baseClause_eval_true
#print axioms normalizedExtraClause_eval_true
#print axioms normalizedCoreSelection_eval_true
#print axioms no_degreeEight_cover6_avoiding_of_coreProvider

end LRATCatcher.Tests.R44Cover6SemanticComposition
