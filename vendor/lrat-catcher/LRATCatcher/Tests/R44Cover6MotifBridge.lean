import LRATCatcher.Tests.R44OrderTwelveTwoCenterCases

/-!
  # Exact cover6 motifs and their DIMACS blocker semantics

  This module materializes the six order-seven graph6 records used by the
  complement-closed cover6 route.  It also proves the small generic bridge
  needed by a future generated CNF equality: a full 21-literal DIMACS blocker
  is false exactly when the selected seven ambient vertices induce the stated
  motif.  No external DIMACS file or SAT result is imported here.
-/

namespace LRATCatcher.Tests.R44Cover6MotifBridge

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry

abbrev AmbientVertex := Fin 12
abbrev MotifVertex := Fin 7
abbrev MotifEmbedding := MotifVertex → AmbientVertex

/-! ## A deliberately small order-seven graph6 decoder -/

/-- The graph6 payload bit at a zero-based position after the order byte.
For the six short records used here, every character is an ordinary graph6
sextet and the graph order is the leading `F` (`7 + 63`). -/
def graph6PayloadBit (record : String) (position : Nat) : Bool :=
  let character := record.toList.getD (position / 6 + 1) '\x00'
  let sextet := character.toNat - 63
  sextet.testBit (5 - position % 6)

/-- graph6 uses the column-wise upper-triangle order
`(0,1),(0,2),(1,2),...`; this is also the local mask order used by the
cover6 generators. -/
def graph6EdgePosition (left right : Nat) : Nat :=
  let low := min left right
  let high := max left right
  high * (high - 1) / 2 + low

/-- Decode an order-seven graph6 record into the packed symmetric adjacency
rows used throughout the catalogue development. -/
def decodeGraph6Seven (record : String) : Graph :=
  (List.range 7).map fun left =>
    (List.range 7).foldl (fun row right =>
      if left = right then row
      else if graph6PayloadBit record (graph6EdgePosition left right) then
        row + 2 ^ right
      else row) 0

def motifFAtHCaretG : Graph := decodeGraph6Seven "F@h^g"
def motifFKDhw : Graph := decodeGraph6Seven "FKDhw"
def motifFGBacktickXo : Graph := decodeGraph6Seven "FG`Xo"
def motifFdWBraceW : Graph := decodeGraph6Seven "FdW}w"
def motifFHFLw : Graph := decodeGraph6Seven "FHFLw"
def motifFIIXw : Graph := decodeGraph6Seven "FIIXw"

/-- Frozen graph6 file order of the complement-closed six-motif family. -/
def cover6Graph6Records : List String :=
  ["F@h^g", "FKDhw", "FG`Xo", "FdW}w", "FHFLw", "FIIXw"]

/-- The exact decoded motif family, in the same order as the TSV file. -/
def cover6Motifs : List Graph :=
  [motifFAtHCaretG, motifFKDhw, motifFGBacktickXo,
    motifFdWBraceW, motifFHFLw, motifFIIXw]

theorem cover6Motifs_eq_decode_records :
    cover6Motifs = cover6Graph6Records.map decodeGraph6Seven := by
  rfl

/-- Independently inspectable packed rows for all six raw graph6 records. -/
theorem cover6Motifs_eq_packedRows :
    cover6Motifs = [
      [80, 96, 88, 100, 37, 90, 47],
      [8, 36, 98, 81, 104, 86, 60],
      [16, 36, 66, 96, 97, 26, 28],
      [74, 81, 56, 101, 102, 92, 59],
      [96, 36, 74, 84, 104, 83, 61],
      [32, 12, 82, 98, 100, 89, 60]] := by
  native_decide

theorem cover6Motifs_length : cover6Motifs.length = 6 := by
  native_decide

theorem cover6Motif_length {motif : Graph}
    (hmotif : motif ∈ cover6Motifs) : motif.length = 7 := by
  simp only [cover6Motifs, List.mem_cons, List.not_mem_nil, or_false] at hmotif
  rcases hmotif with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem cover6Motif_wellFormed {motif : Graph}
    (hmotif : motif ∈ cover6Motifs) :
    wellFormedGraph 7 motif = true := by
  simp only [cover6Motifs, List.mem_cons, List.not_mem_nil, or_false] at hmotif
  rcases hmotif with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-! ## The three exact complement pairs -/

structure ComplementPairWitness where
  source : Graph
  target : Graph
  permutation : List Nat

/-- The permutation maps a source label to a target label.  Only distinct
pairs are tested, so the complement relation remains loop-free. -/
def checkComplementPair (witness : ComplementPairWitness) : Bool :=
  isPermutation witness.permutation 7 &&
    (subsets 7 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          edge witness.source left right ==
            !(edge witness.target
              (witness.permutation.getD left 7)
              (witness.permutation.getD right 7))
      | _ => false

/-- Explicit complement isomorphisms in the three consecutive graph6 pairs. -/
def cover6ComplementPairs : List ComplementPairWitness := [
  { source := motifFAtHCaretG, target := motifFKDhw,
    permutation := [5, 6, 2, 4, 3, 1, 0] },
  { source := motifFGBacktickXo, target := motifFdWBraceW,
    permutation := [6, 3, 4, 5, 2, 1, 0] },
  { source := motifFHFLw, target := motifFIIXw,
    permutation := [6, 5, 2, 3, 4, 1, 0] }
]

theorem cover6ComplementPairs_checked :
    cover6ComplementPairs.all checkComplementPair = true := by
  native_decide

/-! ## Exact one-based DIMACS blocker -/

/-- All 21 local pairs in the same column-wise order as graph6 and the
cover6 cube generator. -/
def motifUpperPairs : List (MotifVertex × MotifVertex) :=
  (List.finRange 7).flatMap fun right =>
    (List.finRange 7).filterMap fun left =>
      if left < right then some (left, right) else none

theorem mem_motifUpperPairs_iff (left right : MotifVertex) :
    (left, right) ∈ motifUpperPairs ↔ left < right := by
  native_decide +revert

theorem motifUpperPairs_length : motifUpperPairs.length = 21 := by
  native_decide

/-- Symmetric zero-based `K_12` edge variable.  Blocker callers always use
distinct vertices, because their embedding is injective. -/
def symmetricEdgeVarTwelve (left right : AmbientVertex) : Nat :=
  if left < right then edgeVar 12 left.val right.val
  else edgeVar 12 right.val left.val

/-- The opposite-polarity literal that blocks `variable = value`.  It is
one-based as a DIMACS integer: a motif edge emits a negative literal and a
motif non-edge emits a positive literal. -/
def blockingDimacsLiteral (variableIndex : Nat) (value : Bool) : Int :=
  if value then -Int.ofNat (variableIndex + 1)
  else Int.ofNat (variableIndex + 1)

/-- Parsing audits both the one-based shift and blocker polarity. -/
theorem dimacsLit_blockingDimacsLiteral
    (variableIndex : Nat) (value : Bool) :
    LRATCatcher.dimacsLit (blockingDimacsLiteral variableIndex value) =
      (variableIndex, !value) := by
  cases value with
  | false =>
      unfold blockingDimacsLiteral LRATCatcher.dimacsLit
      change
        (variableIndex + 1 - 1,
          decide (0 < Int.ofNat (variableIndex + 1))) =
            (variableIndex, true)
      simp
  | true =>
      unfold blockingDimacsLiteral LRATCatcher.dimacsLit
      change
        (variableIndex + 1 - 1,
          decide (0 < -Int.ofNat (variableIndex + 1))) =
            (variableIndex, false)
      have hpositive : (0 : Int) < Int.ofNat (variableIndex + 1) :=
        Int.natCast_pos.mpr (by omega)
      have hnotPositive :
          ¬(0 : Int) < -Int.ofNat (variableIndex + 1) := by
        omega
      have hnonnegative :
          (0 : Int) ≤ Int.ofNat variableIndex := Int.natCast_nonneg _
      simp
      omega

/-- Full, uncompressed, 21-literal blocker for one labelled embedding of an
order-seven motif into `K_12`.  The large cover6 formula uses sound partial
cubes instead; this full blocker is the declarative reference semantics. -/
def motifDimacsBlocker
    (embedding : MotifEmbedding) (motif : Graph) : CNF.Clause Nat :=
  motifUpperPairs.map fun pair =>
    LRATCatcher.dimacsLit <|
      blockingDimacsLiteral
        (symmetricEdgeVarTwelve (embedding pair.1) (embedding pair.2))
        (edge motif pair.1.val pair.2.val)

/-- Exact labelled induced-match predicate corresponding to the 21 upper
triangle positions. -/
def EmbeddingMatchesMotif
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (motif : Graph) : Prop :=
  ∀ left right : MotifVertex, left < right →
    coloring (symmetricEdgeVarTwelve (embedding left) (embedding right)) =
      edge motif left.val right.val

/-- Central polarity theorem: falsifying the complete DIMACS blocker is
equivalent to matching every edge and non-edge of the motif. -/
theorem motifDimacsBlocker_eval_false_iff
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (motif : Graph) :
    CNF.Clause.eval coloring (motifDimacsBlocker embedding motif) = false ↔
      EmbeddingMatchesMotif coloring embedding motif := by
  simp only [CNF.Clause.eval, motifDimacsBlocker, List.any_map,
    Function.comp_apply, dimacsLit_blockingDimacsLiteral,
    List.any_eq_false, EmbeddingMatchesMotif]
  constructor
  · intro hall left right hordered
    have hmember : (left, right) ∈ motifUpperPairs :=
      (mem_motifUpperPairs_iff left right).2 hordered
    have hliteral := hall (left, right) hmember
    cases hactual : coloring
        (symmetricEdgeVarTwelve (embedding left) (embedding right)) <;>
      cases hexpected : edge motif left.val right.val <;> simp_all
  · intro hmatch pair hpair
    have hequal :=
      hmatch pair.1 pair.2 ((mem_motifUpperPairs_iff _ _).1 hpair)
    cases hactual : coloring
        (symmetricEdgeVarTwelve (embedding pair.1) (embedding pair.2)) <;>
      cases hexpected : edge motif pair.1.val pair.2.val <;> simp_all

/-! ## Bridge to the existing declarative occurrence predicate -/

theorem coloring_symmetricEdgeVarTwelve
    (coloring : Nat → Bool) (left right : AmbientVertex)
    (hne : left ≠ right) :
    coloring (symmetricEdgeVarTwelve left right) =
      coloringEdge 12 coloring left.val right.val := by
  unfold symmetricEdgeVarTwelve
  by_cases hordered : left < right
  · have horderedVal : left.val < right.val := hordered
    simp [hordered, coloringEdge, horderedVal]
  · have hnotOrderedVal : ¬left.val < right.val := by
      simpa using hordered
    have hvalNe : left.val ≠ right.val := fun hequal => hne (Fin.ext hequal)
    have hreverseVal : right.val < left.val := by omega
    simp [hordered, coloringEdge, hnotOrderedVal, hreverseVal]

/-- A false full blocker plus injectivity gives the exact existing
`InducedMotifOccurrence` object. -/
theorem false_motifDimacsBlocker_gives_occurrence
    (coloring : Nat → Bool) (embedding : MotifEmbedding)
    (motif : Graph) (hmotif : motif ∈ cover6Motifs)
    (hinjective : Function.Injective embedding)
    (hfalse :
      CNF.Clause.eval coloring (motifDimacsBlocker embedding motif) = false) :
    InducedMotifOccurrence 7 coloring motif := by
  have hmatch :=
    (motifDimacsBlocker_eval_false_iff coloring embedding motif).1 hfalse
  have hwellFormed := cover6Motif_wellFormed hmotif
  refine ⟨⟨cover6Motif_length hmotif, embedding, hinjective, ?_⟩⟩
  intro left right
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · have horderedFin : left < right := hordered
    have himageNe : embedding left ≠ embedding right := by
      intro himage
      exact (Nat.ne_of_lt hordered)
        (congrArg Fin.val (hinjective himage))
    calc
      edge motif left.val right.val =
          coloring (symmetricEdgeVarTwelve
            (embedding left) (embedding right)) :=
        (hmatch left right horderedFin).symm
      _ = coloringEdge 12 coloring
            (embedding left).val (embedding right).val :=
        coloring_symmetricEdgeVarTwelve coloring _ _ himageNe
  · have hsame : left = right := Fin.ext hequal
    subst right
    rw [wellFormedGraph_loop_false hwellFormed left.isLt]
    exact (coloringEdge_self 12 coloring (embedding left).val).symm
  · have hreverseFin : right < left := hreverse
    have himageNe : embedding right ≠ embedding left := by
      intro himage
      exact (Nat.ne_of_lt hreverse)
        (congrArg Fin.val (hinjective himage))
    calc
      edge motif left.val right.val = edge motif right.val left.val :=
        wellFormedGraph_edge_comm hwellFormed left.isLt right.isLt
      _ = coloring (symmetricEdgeVarTwelve
            (embedding right) (embedding left)) :=
        (hmatch right left hreverseFin).symm
      _ = coloringEdge 12 coloring
            (embedding right).val (embedding left).val :=
        coloring_symmetricEdgeVarTwelve coloring _ _ himageNe
      _ = coloringEdge 12 coloring
            (embedding left).val (embedding right).val :=
        coloringEdge_comm 12 coloring _ _

/-- Conversely, every declarative occurrence supplies a labelled full
DIMACS blocker that evaluates to false. -/
theorem occurrence_gives_false_motifDimacsBlocker
    (coloring : Nat → Bool) (motif : Graph)
    (hoccurrence : InducedMotifOccurrence 7 coloring motif) :
    ∃ embedding : MotifEmbedding,
      Function.Injective embedding ∧
      CNF.Clause.eval coloring
        (motifDimacsBlocker embedding motif) = false := by
  obtain ⟨occurrence⟩ := hoccurrence
  refine ⟨occurrence.embedding, occurrence.embedding_injective, ?_⟩
  apply (motifDimacsBlocker_eval_false_iff
    coloring occurrence.embedding motif).2
  intro left right hordered
  have himageNe : occurrence.embedding left ≠ occurrence.embedding right := by
    intro himage
    have horderedVal : left.val < right.val := hordered
    exact (Nat.ne_of_lt horderedVal)
      (congrArg Fin.val (occurrence.embedding_injective himage))
  calc
    coloring (symmetricEdgeVarTwelve
        (occurrence.embedding left) (occurrence.embedding right)) =
        coloringEdge 12 coloring
          (occurrence.embedding left).val (occurrence.embedding right).val :=
      coloring_symmetricEdgeVarTwelve coloring _ _ himageNe
    _ = edge motif left.val right.val :=
      (occurrence.map_edge left right).symm

#print axioms cover6Motifs_eq_packedRows
#print axioms cover6ComplementPairs_checked
#print axioms cover6Motif_wellFormed
#print axioms motifDimacsBlocker_eval_false_iff
#print axioms false_motifDimacsBlocker_gives_occurrence
#print axioms occurrence_gives_false_motifDimacsBlocker

end LRATCatcher.Tests.R44Cover6MotifBridge
