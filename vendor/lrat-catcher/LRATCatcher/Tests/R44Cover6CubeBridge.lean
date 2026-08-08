import LRATCatcher.Tests.R44Cover6MotifBridge

/-!
  # Partial-cube semantics for the order-seven cover6 blockers

  A cover6 cube is a pair `(ones, fixed)` of 21-bit masks.  A fixed bit set
  in `ones` requires an edge; a fixed bit clear in `ones` requires a non-edge.
  The emitted clause uses the opposite polarity, so it is false exactly when
  every fixed requirement holds.  This module proves that statement without
  importing the 25,200 generated cubes or any SAT/LRAT artifact.
-/

namespace LRATCatcher.Tests.R44Cover6CubeBridge

open Std.Sat
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44Cover6MotifBridge

/-! ## Cube data and local semantics -/

structure Cover6Cube where
  ones : Nat
  fixed : Nat
deriving DecidableEq, Repr

namespace Cover6Cube

/-- The generator invariant: both masks have width at most 21 and every one
bit is fixed.  The blocker theorem itself is total and does not need this
hypothesis; generated-cube audits should establish it separately. -/
def WellFormed (cube : Cover6Cube) : Prop :=
  cube.ones < 2 ^ 21 ∧
    cube.fixed < 2 ^ 21 ∧
    ∀ position, position < 21 →
      cube.ones.testBit position = true →
      cube.fixed.testBit position = true

end Cover6Cube

abbrev LocalEdgeAssignment := MotifVertex → MotifVertex → Bool

/-- Graph6/local-mask bit position of an ordered local pair. -/
def motifPairPosition (pair : MotifVertex × MotifVertex) : Nat :=
  graph6EdgePosition pair.1.val pair.2.val

/-- The fixed upper-triangle positions, retaining graph6 column order. -/
def cubeFixedPairs (cube : Cover6Cube) :
    List (MotifVertex × MotifVertex) :=
  motifUpperPairs.filter fun pair =>
    cube.fixed.testBit (motifPairPosition pair)

theorem mem_cubeFixedPairs_iff
    (cube : Cover6Cube) (left right : MotifVertex) :
    (left, right) ∈ cubeFixedPairs cube ↔
      left < right ∧
        cube.fixed.testBit
          (graph6EdgePosition left.val right.val) = true := by
  simp [cubeFixedPairs, motifPairPosition, mem_motifUpperPairs_iff]

/-- A local edge assignment satisfies every requirement encoded by a cube. -/
def CubeMatchesLocal
    (localEdges : LocalEdgeAssignment) (cube : Cover6Cube) : Prop :=
  ∀ left right : MotifVertex, left < right →
    cube.fixed.testBit (graph6EdgePosition left.val right.val) = true →
    localEdges left right =
      cube.ones.testBit (graph6EdgePosition left.val right.val)

/-- Restrict an ambient `K_12` assignment along one labelled embedding. -/
def embeddedLocalEdges
    (coloring : Nat → Bool) (embedding : MotifEmbedding) :
    LocalEdgeAssignment := fun left right =>
  coloring (symmetricEdgeVarTwelve (embedding left) (embedding right))

/-! ## Exact partial blocker -/

/-- Raw one-based DIMACS clause emitted for a partial cube. -/
def cubeDimacsClause
    (embedding : MotifEmbedding) (cube : Cover6Cube) : List Int :=
  (cubeFixedPairs cube).map fun pair =>
    blockingDimacsLiteral
      (symmetricEdgeVarTwelve (embedding pair.1) (embedding pair.2))
      (cube.ones.testBit (motifPairPosition pair))

/-- Parsed `Std.Sat` form of the same partial blocker. -/
def cubeDimacsBlocker
    (embedding : MotifEmbedding) (cube : Cover6Cube) : CNF.Clause Nat :=
  (cubeDimacsClause embedding cube).map LRATCatcher.dimacsLit

theorem cubeDimacsClause_length
    (embedding : MotifEmbedding) (cube : Cover6Cube) :
    (cubeDimacsClause embedding cube).length =
      (cubeFixedPairs cube).length := by
  simp [cubeDimacsClause]

/-- Central partial-cube theorem: the clause is false exactly when every
fixed graph6 bit has the required value. -/
theorem cubeDimacsBlocker_eval_false_iff
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (cube : Cover6Cube) :
    CNF.Clause.eval coloring (cubeDimacsBlocker embedding cube) = false ↔
      CubeMatchesLocal (embeddedLocalEdges coloring embedding) cube := by
  simp only [CNF.Clause.eval, cubeDimacsBlocker, cubeDimacsClause,
    List.map_map, List.any_map, Function.comp_apply,
    dimacsLit_blockingDimacsLiteral, List.any_eq_false,
    CubeMatchesLocal, embeddedLocalEdges]
  constructor
  · intro hall left right hordered hfixed
    have hmember : (left, right) ∈ cubeFixedPairs cube :=
      (mem_cubeFixedPairs_iff cube left right).2 ⟨hordered, hfixed⟩
    have hliteral := hall (left, right) hmember
    cases hactual : coloring
        (symmetricEdgeVarTwelve (embedding left) (embedding right)) <;>
      cases hrequired : cube.ones.testBit
        (graph6EdgePosition left.val right.val) <;> simp_all [motifPairPosition]
  · intro hmatch pair hpair
    have hproperties := (mem_cubeFixedPairs_iff
      cube pair.1 pair.2).1 hpair
    have hequal := hmatch pair.1 pair.2 hproperties.1 hproperties.2
    cases hactual : coloring
        (symmetricEdgeVarTwelve (embedding pair.1) (embedding pair.2)) <;>
      cases hrequired : cube.ones.testBit
        (graph6EdgePosition pair.1.val pair.2.val) <;>
          simp_all [motifPairPosition]

/-! ## Generic safety interfaces -/

/-- Equality with all 21 edges and non-edges of one labelled motif. -/
def LocalEdgesMatchMotif
    (localEdges : LocalEdgeAssignment) (motif : Graph) : Prop :=
  ∀ left right : MotifVertex, left < right →
    localEdges left right = edge motif left.val right.val

/-- A semantic admissibility predicate may encode local `R(4,4)` freeness or
any other condition used by a finite cube checker.  Safety means that every
admissible completion of this cube is the specified labelled motif. -/
def CubeSafeForMotifUnder
    (admissible : LocalEdgeAssignment → Prop)
    (cube : Cover6Cube) (motif : Graph) : Prop :=
  ∀ localEdges, admissible localEdges →
    CubeMatchesLocal localEdges cube →
    LocalEdgesMatchMotif localEdges motif

/-- A false partial blocker yields a declarative occurrence once a separate
checker has proved that this cube safely forces the selected motif under the
stated admissibility condition. -/
theorem safeCubeBlocker_false_gives_occurrence
    (admissible : LocalEdgeAssignment → Prop)
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (cube : Cover6Cube) (motif : Graph)
    (hmotif : motif ∈ cover6Motifs)
    (hinjective : Function.Injective embedding)
    (hadmissible : admissible (embeddedLocalEdges coloring embedding))
    (hsafe : CubeSafeForMotifUnder admissible cube motif)
    (hfalse :
      CNF.Clause.eval coloring (cubeDimacsBlocker embedding cube) = false) :
    InducedMotifOccurrence 7 coloring motif := by
  have hcube :=
    (cubeDimacsBlocker_eval_false_iff coloring embedding cube).1 hfalse
  have hlocalMatch := hsafe _ hadmissible hcube
  have hfullMatch : EmbeddingMatchesMotif coloring embedding motif := by
    intro left right hordered
    exact hlocalMatch left right hordered
  have hfullFalse :=
    (motifDimacsBlocker_eval_false_iff coloring embedding motif).2 hfullMatch
  exact false_motifDimacsBlocker_gives_occurrence
    coloring embedding motif hmotif hinjective hfullFalse

/-- Actual cover6 cubes may force different members of the six-motif family
on different admissible completions.  This is the precise generic interface
needed by a future finite `R(4,4)` cube-safety certificate. -/
def CubeSafeForCover6Under
    (admissible : LocalEdgeAssignment → Prop)
    (cube : Cover6Cube) : Prop :=
  ∀ localEdges, admissible localEdges →
    CubeMatchesLocal localEdges cube →
    ∃ motif, motif ∈ cover6Motifs ∧
      LocalEdgesMatchMotif localEdges motif

theorem safeCover6CubeBlocker_false_gives_occurrence
    (admissible : LocalEdgeAssignment → Prop)
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (cube : Cover6Cube)
    (hinjective : Function.Injective embedding)
    (hadmissible : admissible (embeddedLocalEdges coloring embedding))
    (hsafe : CubeSafeForCover6Under admissible cube)
    (hfalse :
      CNF.Clause.eval coloring (cubeDimacsBlocker embedding cube) = false) :
    ∃ motif, motif ∈ cover6Motifs ∧
      InducedMotifOccurrence 7 coloring motif := by
  have hcube :=
    (cubeDimacsBlocker_eval_false_iff coloring embedding cube).1 hfalse
  obtain ⟨motif, hmotif, hlocalMatch⟩ := hsafe _ hadmissible hcube
  refine ⟨motif, hmotif, ?_⟩
  have hfullMatch : EmbeddingMatchesMotif coloring embedding motif := by
    intro left right hordered
    exact hlocalMatch left right hordered
  have hfullFalse :=
    (motifDimacsBlocker_eval_false_iff coloring embedding motif).2 hfullMatch
  exact false_motifDimacsBlocker_gives_occurrence
    coloring embedding motif hmotif hinjective hfullFalse

#print axioms cubeDimacsBlocker_eval_false_iff
#print axioms safeCubeBlocker_false_gives_occurrence
#print axioms safeCover6CubeBlocker_false_gives_occurrence

end LRATCatcher.Tests.R44Cover6CubeBridge
