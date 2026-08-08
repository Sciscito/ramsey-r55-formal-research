import Lean.Data.Json.Parser
import LRATCatcher.Tests.R44Cover6SemanticComposition

/-!
  # Checked conditioned witnesses for the cover6 degree-eight core

  The tracked JSON certificate contains a fifteen-bit orbit witness for every
  conditioned K7 cube and every projected K6 cube.  This module decodes only
  the entries selected by the 6,152-clause LRAT dependency core.  Finite
  `native_decide` checks connect those compact words to the exact indexed CNF
  source; the remaining arguments are proposition-level transports.
-/

namespace LRATCatcher.Tests.R44Cover6ConditionedWitnesses

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
open LRATCatcher.Tests.R44Cover6SemanticComposition

set_option maxRecDepth 100000

/-! ## The tracked compact payload -/

def conditionedWitnessReportText : String :=
  include_str "../../../../scripts/r45_d12_cover9_universal/COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json"

def conditionedWitnessReport : Lean.Json :=
  match Lean.Json.parse conditionedWitnessReportText with
  | .ok report => report
  | .error _ => .null

def jsonStringArray (value : Lean.Json) : Array String :=
  match value.getArr? with
  | .error _ => #[]
  | .ok values => values.map fun item =>
      match item.getStr? with
      | .ok text => text
      | .error _ => ""

def certificatePayload (key : String) : Array String :=
  match conditionedWitnessReport.getObjVal? "certificate_payloads" with
  | .error _ => #[]
  | .ok payloads =>
      match payloads.getObjVal? key with
      | .error _ => #[]
      | .ok value => jsonStringArray value

def fullK7WitnessChunks : Array String :=
  certificatePayload "full_k7_witness_chunks"

def projectedK6WitnessChunks : Array String :=
  certificatePayload "projected_k6_lift_witness_chunks"

def witnessBits : Nat := 15
def witnessCodeLimit : Nat := 30240

def witnessCodeAt (chunks : Array String) (item : Nat) : Nat :=
  let bitStart := item * witnessBits
  let digitStart := bitStart / 6
  let shift := bitStart % 6
  let window := (List.range 3).foldl (fun value digit =>
    value + alphabetValue (dataCharAt chunks (digitStart + digit)) *
      2 ^ (6 * digit)) 0
  window / 2 ^ shift % 2 ^ witnessBits

def blockPayloadOffset : Nat → Nat
  | 4 => 0
  | 5 => 15480
  | 6 => 25680
  | 7 => 30360
  | _ => 0

def localPayloadOffset : Nat → Nat
  | 3 => 0
  | 4 => 540
  | 5 => 900
  | _ => 0

/-! ## Core positions, catalogue locations, and embeddings -/

def rootFreeSourceIndex (position : Fin 3514) : Nat :=
  (coreSourceIndex (rootFreeCorePosition position)).val

def rootFreeLocation (position : Fin 3514) : List Nat × Nat :=
  (blockLocation (rootFreeSourceIndex position - 717)).getD ([], 0)

def rootFreeItem (position : Fin 3514) : List Nat :=
  (rootFreeLocation position).1

def rootFreeCatalogueIndex (position : Fin 3514) : Nat :=
  (rootFreeLocation position).2

def rootFreePayloadIndex (position : Fin 3514) : Nat :=
  blockPayloadOffset (neighborCount (rootFreeItem position)) +
    rootFreeCatalogueIndex position

def rootFreeEmbedding (position : Fin 3514) : MotifEmbedding :=
  fun vertex => Fin.ofNat 12 ((rootFreeItem position).getD vertex.val 0)

def rootContainingSourceIndex (position : Fin 2409) : Nat :=
  (coreSourceIndex (rootContainingCorePosition position)).val

def rootContainingLocation (position : Fin 2409) : List Nat × Nat :=
  (localLocation (rootContainingSourceIndex position - 3211197)).getD ([], 0)

def rootContainingItem (position : Fin 2409) : List Nat :=
  (rootContainingLocation position).1

def rootContainingCatalogueIndex (position : Fin 2409) : Nat :=
  (rootContainingLocation position).2

def rootContainingNeighbourCount (position : Fin 2409) : Nat :=
  neighborCount (rootContainingItem position)

def rootContainingPayloadIndex (position : Fin 2409) : Nat :=
  localPayloadOffset (rootContainingNeighbourCount position) +
    rootContainingCatalogueIndex position

def rootContainingProjectedCube (position : Fin 2409) : Cover6Cube :=
  let cube := localCubeAt (rootContainingNeighbourCount position)
    (rootContainingCatalogueIndex position)
  { ones := cube.1, fixed := cube.2 }

/-- The six projected labels occupy local labels `0,...,5`; label six is an
unused dummy because the projected cube has no fixed bit incident to it. -/
def rootContainingProjectedEmbedding (position : Fin 2409) : MotifEmbedding :=
  fun vertex => Fin.ofNat 12 ((rootContainingItem position).getD vertex.val 0)

/-- The full lift uses local label zero for the ambient root and labels
`1,...,6` for the six vertices in combination order. -/
def rootContainingEmbedding (position : Fin 2409) : MotifEmbedding :=
  fun vertex =>
    if vertex.val = 0 then 0
    else Fin.ofNat 12
      ((rootContainingItem position).getD (vertex.val - 1) 0)

def projectedVertex (vertex : MotifVertex) : MotifVertex :=
  Fin.ofNat 7 (vertex.val - 1)

/-! ## Lehmer decoding and the six representative packages -/

def factorial : Nat → Nat
  | 0 => 1
  | value + 1 => (value + 1) * factorial value

def permutationUnrankAux : Nat → Nat → List Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, rank, remaining =>
      let factor := factorial fuel
      let digit := rank / factor
      let value := remaining.getD digit 0
      value :: permutationUnrankAux fuel (rank % factor)
        (remaining.erase value)

def permutationUnrank (rank : Nat) : List Nat :=
  permutationUnrankAux 7 rank (List.range 7)

def decodedToFun (rank : Fin 5040) (vertex : MotifVertex) : MotifVertex :=
  Fin.ofNat 7 ((permutationUnrank rank.val).getD vertex.val 7)

def decodedInvFun (rank : Fin 5040) (vertex : MotifVertex) : MotifVertex :=
  Fin.ofNat 7 ((permutationUnrank rank.val).idxOf vertex.val)

set_option maxHeartbeats 0 in
theorem permutationFiniteChecks :
    (∀ rank : Fin 5040,
      isPermutation (permutationUnrank rank.val) 7 = true) ∧
    (∀ (rank : Fin 5040) (vertex : MotifVertex),
      decodedInvFun rank (decodedToFun rank vertex) = vertex) ∧
    (∀ (rank : Fin 5040) (vertex : MotifVertex),
      decodedToFun rank (decodedInvFun rank vertex) = vertex) ∧
    (∀ (rank : Fin 5040) (vertex : MotifVertex),
      (decodedToFun rank vertex).val =
        (permutationUnrank rank.val).getD vertex.val 7) := by
  native_decide

theorem permutationUnrank_valid (rank : Fin 5040) :
    isPermutation (permutationUnrank rank.val) 7 = true :=
  permutationFiniteChecks.1 rank

/-- A fully computable finite permutation.  The inverse is obtained by looking
up the target label in the unranked target-to-source list. -/
def decodedPermutation (rank : Fin 5040) : FinPermutation 7 where
  toFun := decodedToFun rank
  invFun := decodedInvFun rank
  left_inv := permutationFiniteChecks.2.1 rank
  right_inv := permutationFiniteChecks.2.2.1 rank

@[simp] theorem decodedPermutation_apply_val
    (rank : Fin 5040) (vertex : MotifVertex) :
    (decodedPermutation rank vertex).val =
      (permutationUnrank rank.val).getD vertex.val 7 := by
  exact permutationFiniteChecks.2.2.2 rank vertex

structure RepresentativeWitness where
  cube : Cover6Cube
  inner : FinPermutation 7
  motif : Graph
  motif_mem : motif ∈ cover6Motifs
  forces : CubeForcesRelabeledMotif cube inner motif

def representativeCubeAt (index : Fin 6) : Cover6Cube :=
  match index.val with
  | 0 => representativeCube0
  | 1 => representativeCube1
  | 2 => representativeCube2
  | 3 => representativeCube3
  | 4 => representativeCube4
  | _ => representativeCube5

noncomputable def representativeWitness (index : Fin 6) : RepresentativeWitness :=
  match index.val with
  | 0 =>
      { cube := representativeCube0
        inner := representativeMotifPermutation0
        motif := motifFGBacktickXo
        motif_mem := by simp [cover6Motifs]
        forces := representativeCube0_forces_motif }
  | 1 =>
      { cube := representativeCube1
        inner := representativeMotifPermutation1
        motif := motifFdWBraceW
        motif_mem := by simp [cover6Motifs]
        forces := representativeCube1_forces_motif }
  | 2 =>
      { cube := representativeCube2
        inner := representativeMotifPermutation2
        motif := motifFIIXw
        motif_mem := by simp [cover6Motifs]
        forces := representativeCube2_forces_motif }
  | 3 =>
      { cube := representativeCube3
        inner := representativeMotifPermutation3
        motif := motifFHFLw
        motif_mem := by simp [cover6Motifs]
        forces := representativeCube3_forces_motif }
  | 4 =>
      { cube := representativeCube4
        inner := representativeMotifPermutation4
        motif := motifFKDhw
        motif_mem := by simp [cover6Motifs]
        forces := representativeCube4_forces_motif }
  | _ =>
      { cube := representativeCube5
        inner := representativeMotifPermutation5
        motif := motifFAtHCaretG
        motif_mem := by simp [cover6Motifs]
        forces := representativeCube5_forces_motif }

theorem representativeWitness_cube (index : Fin 6) :
    (representativeWitness index).cube = representativeCubeAt index := by
  rcases index with ⟨index, hindex⟩
  have hcases : index = 0 ∨ index = 1 ∨ index = 2 ∨
      index = 3 ∨ index = 4 ∨ index = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Decoded core witnesses -/

def rootFreeWitnessCode (position : Fin 3514) : Nat :=
  witnessCodeAt fullK7WitnessChunks (rootFreePayloadIndex position)

def rootContainingWitnessCode (position : Fin 2409) : Nat :=
  witnessCodeAt projectedK6WitnessChunks
    (rootContainingPayloadIndex position)

def rootFreeRepresentativeIndex (position : Fin 3514) : Fin 6 :=
  ⟨rootFreeWitnessCode position % 6, Nat.mod_lt _ (by decide)⟩

def rootContainingRepresentativeIndex (position : Fin 2409) : Fin 6 :=
  ⟨rootContainingWitnessCode position % 6, Nat.mod_lt _ (by decide)⟩

def rootFreePermutationRank (position : Fin 3514) : Fin 5040 :=
  Fin.ofNat 5040 (rootFreeWitnessCode position / 6)

def rootContainingPermutationRank (position : Fin 2409) : Fin 5040 :=
  Fin.ofNat 5040 (rootContainingWitnessCode position / 6)

noncomputable def rootFreeRepresentative (position : Fin 3514) :
    RepresentativeWitness :=
  representativeWitness (rootFreeRepresentativeIndex position)

noncomputable def rootContainingRepresentative (position : Fin 2409) :
    RepresentativeWitness :=
  representativeWitness (rootContainingRepresentativeIndex position)

def rootFreeCube (position : Fin 3514) : Cover6Cube :=
  permuteCube (decodedPermutation (rootFreePermutationRank position))
    (representativeCubeAt (rootFreeRepresentativeIndex position))

def rootContainingFullCube (position : Fin 2409) : Cover6Cube :=
  permuteCube (decodedPermutation (rootContainingPermutationRank position))
    (representativeCubeAt (rootContainingRepresentativeIndex position))

def rootContainingAmbientVertex
    (position : Fin 2409) (vertex : MotifVertex) : Nat :=
  (rootContainingItem position).getD (vertex.val - 1) 0

/-! ## Full K7 core blockers -/

def RootFreeFiniteCheck : Prop :=
  (∀ position : Fin 3514, rootFreePayloadIndex position < 32880) ∧
  (∀ (position : Fin 3514) (left right : MotifVertex),
    rootFreeEmbedding position left = rootFreeEmbedding position right →
      left = right) ∧
  (∀ position : Fin 3514,
    selectedCoreClause (rootFreeCorePosition position) =
      cubeDimacsBlocker (rootFreeEmbedding position)
        (rootFreeCube position))

def RootContainingFiniteCheck : Prop :=
  (∀ position : Fin 2409,
    rootContainingPayloadIndex position < 1200) ∧
  (∀ position : Fin 2409,
    selectedCoreClause (rootContainingCorePosition position) =
      cubeDimacsBlocker (rootContainingProjectedEmbedding position)
        (rootContainingProjectedCube position)) ∧
  (∀ (position : Fin 2409) (left right : MotifVertex),
    rootContainingEmbedding position left =
      rootContainingEmbedding position right → left = right) ∧
  (∀ (left right : MotifVertex), 0 < left.val → left < right →
    projectedVertex left < projectedVertex right) ∧
  (∀ (position : Fin 2409) (vertex : MotifVertex), 0 < vertex.val →
    rootContainingEmbedding position vertex =
      rootContainingProjectedEmbedding position (projectedVertex vertex)) ∧
  (∀ (position : Fin 2409) (left right : MotifVertex),
    0 < left.val → left < right →
    (rootContainingFullCube position).fixed.testBit
        (graph6EdgePosition left.val right.val) = true →
    (rootContainingProjectedCube position).fixed.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) = true ∧
      (rootContainingProjectedCube position).ones.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) =
        (rootContainingFullCube position).ones.testBit
          (graph6EdgePosition left.val right.val)) ∧
  (∀ (position : Fin 2409) (vertex : MotifVertex), 0 < vertex.val →
    1 ≤ rootContainingAmbientVertex position vertex ∧
      rootContainingAmbientVertex position vertex < 12) ∧
  (∀ position : Fin 2409,
    (rootContainingEmbedding position 0).val = 0) ∧
  (∀ (position : Fin 2409) (vertex : MotifVertex), 0 < vertex.val →
    (rootContainingEmbedding position vertex).val =
      rootContainingAmbientVertex position vertex) ∧
  (∀ (position : Fin 2409) (right : MotifVertex), 0 < right.val →
    (rootContainingFullCube position).fixed.testBit
        (graph6EdgePosition 0 right.val) = true →
    (rootContainingFullCube position).ones.testBit
        (graph6EdgePosition 0 right.val) =
      decide (rootContainingAmbientVertex position right ≤ 8))

instance rootFreeFiniteCheckDecidable : Decidable RootFreeFiniteCheck := by
  unfold RootFreeFiniteCheck
  infer_instance

instance rootContainingFiniteCheckDecidable :
    Decidable RootContainingFiniteCheck := by
  unfold RootContainingFiniteCheck
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option maxSynthPendingDepth 100 in
theorem payloadFiniteChecks :
    dataLength fullK7WitnessChunks = 82200 ∧
    dataLength projectedK6WitnessChunks = 3000 ∧
    (∀ position : Fin 3514,
      rootFreeWitnessCode position < witnessCodeLimit) ∧
    (∀ position : Fin 2409,
      rootContainingWitnessCode position < witnessCodeLimit) ∧
    RootFreeFiniteCheck ∧ RootContainingFiniteCheck := by
  native_decide

theorem witnessPayloadLengthChecks :
    dataLength fullK7WitnessChunks = 82200 ∧
      dataLength projectedK6WitnessChunks = 3000 := by
  exact ⟨payloadFiniteChecks.1, payloadFiniteChecks.2.1⟩

theorem rootFreeWitnessCode_lt (position : Fin 3514) :
    rootFreeWitnessCode position < witnessCodeLimit :=
  payloadFiniteChecks.2.2.1 position

theorem rootContainingWitnessCode_lt (position : Fin 2409) :
    rootContainingWitnessCode position < witnessCodeLimit :=
  payloadFiniteChecks.2.2.2.1 position

theorem fullK7WitnessPayload_length :
    dataLength fullK7WitnessChunks = 82200 :=
  witnessPayloadLengthChecks.1

theorem projectedK6WitnessPayload_length :
    dataLength projectedK6WitnessChunks = 3000 :=
  witnessPayloadLengthChecks.2

set_option maxHeartbeats 0 in
theorem rootFreeFiniteChecks : RootFreeFiniteCheck :=
  payloadFiniteChecks.2.2.2.2.1

set_option maxHeartbeats 0 in
theorem rootFreePayloadIndex_lt (position : Fin 3514) :
    rootFreePayloadIndex position < 32880 := by
  exact rootFreeFiniteChecks.1 position

set_option maxHeartbeats 0 in
theorem rootFreeEmbedding_injective (position : Fin 3514) :
    Function.Injective (rootFreeEmbedding position) := by
  exact rootFreeFiniteChecks.2.1 position

set_option maxHeartbeats 0 in
theorem rootFreeClause_eq (position : Fin 3514) :
    selectedCoreClause (rootFreeCorePosition position) =
      cubeDimacsBlocker (rootFreeEmbedding position)
        (rootFreeCube position) := by
  exact rootFreeFiniteChecks.2.2 position

theorem rootFreeCube_orbit (position : Fin 3514) :
    CubeInOrbitOf (rootFreeCube position)
      (rootFreeRepresentative position).cube := by
  refine ⟨decodedPermutation (rootFreePermutationRank position), ?_⟩
  unfold rootFreeRepresentative
  rw [representativeWitness_cube]
  rfl

noncomputable def rootFreeBlockerWitness (position : Fin 3514) :
    RootFreeBlockerWitness
      (selectedCoreClause (rootFreeCorePosition position)) :=
  { embedding := rootFreeEmbedding position
    cube := rootFreeCube position
    representative := (rootFreeRepresentative position).cube
    inner := (rootFreeRepresentative position).inner
    motif := (rootFreeRepresentative position).motif
    motif_mem := (rootFreeRepresentative position).motif_mem
    embedding_injective := rootFreeEmbedding_injective position
    orbit := rootFreeCube_orbit position
    representative_forces := (rootFreeRepresentative position).forces
    clause_eq := rootFreeClause_eq position }

/-! ## Projected K6 core blockers and their checked full lifts -/

set_option maxHeartbeats 0 in
theorem rootContainingFiniteChecks : RootContainingFiniteCheck :=
  payloadFiniteChecks.2.2.2.2.2

theorem rootContainingPayloadIndex_lt (position : Fin 2409) :
    rootContainingPayloadIndex position < 1200 := by
  exact rootContainingFiniteChecks.1 position

set_option maxHeartbeats 0 in
theorem rootContainingProjectedClause_eq (position : Fin 2409) :
    selectedCoreClause (rootContainingCorePosition position) =
      cubeDimacsBlocker (rootContainingProjectedEmbedding position)
        (rootContainingProjectedCube position) := by
  exact rootContainingFiniteChecks.2.1 position

set_option maxHeartbeats 0 in
theorem rootContainingEmbedding_injective (position : Fin 2409) :
    Function.Injective (rootContainingEmbedding position) := by
  exact rootContainingFiniteChecks.2.2.1 position

theorem rootContainingFullCube_orbit (position : Fin 2409) :
    CubeInOrbitOf (rootContainingFullCube position)
      (rootContainingRepresentative position).cube := by
  refine ⟨decodedPermutation (rootContainingPermutationRank position), ?_⟩
  unfold rootContainingRepresentative
  rw [representativeWitness_cube]
  rfl

set_option maxHeartbeats 0 in
theorem projectedVertex_lt
    (left right : MotifVertex) (hleft : 0 < left.val)
    (hordered : left < right) :
    projectedVertex left < projectedVertex right := by
  exact rootContainingFiniteChecks.2.2.2.1 left right hleft hordered

set_option maxHeartbeats 0 in
theorem rootContainingEmbedding_nonroot
    (position : Fin 2409) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    rootContainingEmbedding position vertex =
      rootContainingProjectedEmbedding position (projectedVertex vertex) := by
  exact rootContainingFiniteChecks.2.2.2.2.1 position vertex hvertex

set_option maxHeartbeats 0 in
theorem rootContaining_nonroot_bits
    (position : Fin 2409) (left right : MotifVertex)
    (hleft : 0 < left.val) (hordered : left < right)
    (hfixed : (rootContainingFullCube position).fixed.testBit
      (graph6EdgePosition left.val right.val) = true) :
    (rootContainingProjectedCube position).fixed.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) = true ∧
      (rootContainingProjectedCube position).ones.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) =
        (rootContainingFullCube position).ones.testBit
          (graph6EdgePosition left.val right.val) := by
  exact rootContainingFiniteChecks.2.2.2.2.2.1
    position left right hleft hordered hfixed

set_option maxHeartbeats 0 in
theorem rootContainingAmbientVertex_bounds
    (position : Fin 2409) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    1 ≤ rootContainingAmbientVertex position vertex ∧
      rootContainingAmbientVertex position vertex < 12 := by
  exact rootContainingFiniteChecks.2.2.2.2.2.2.1
    position vertex hvertex

set_option maxHeartbeats 0 in
theorem rootContainingEmbedding_root_val (position : Fin 2409) :
    (rootContainingEmbedding position 0).val = 0 := by
  exact rootContainingFiniteChecks.2.2.2.2.2.2.2.1 position

set_option maxHeartbeats 0 in
theorem rootContainingEmbedding_nonroot_val
    (position : Fin 2409) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    (rootContainingEmbedding position vertex).val =
      rootContainingAmbientVertex position vertex := by
  exact rootContainingFiniteChecks.2.2.2.2.2.2.2.2.1
    position vertex hvertex

set_option maxHeartbeats 0 in
theorem rootContaining_root_bit
    (position : Fin 2409) (right : MotifVertex)
    (hright : 0 < right.val)
    (hfixed : (rootContainingFullCube position).fixed.testBit
      (graph6EdgePosition 0 right.val) = true) :
    (rootContainingFullCube position).ones.testBit
        (graph6EdgePosition 0 right.val) =
      decide (rootContainingAmbientVertex position right ≤ 8) := by
  exact rootContainingFiniteChecks.2.2.2.2.2.2.2.2.2
    position right hright hfixed

theorem rootContainingProjected_false_gives_full_match
    (coloring : Nat → Bool) (p q : Nat)
    (hbranch : TwoCenterBranch coloring p q)
    (position : Fin 2409)
    (hfalse : CNF.Clause.eval coloring
      (selectedCoreClause (rootContainingCorePosition position)) = false) :
    CubeMatchesLocal
      (embeddedLocalEdges coloring (rootContainingEmbedding position))
      (rootContainingFullCube position) := by
  have hprojectedFalse : CNF.Clause.eval coloring
      (cubeDimacsBlocker (rootContainingProjectedEmbedding position)
        (rootContainingProjectedCube position)) = false := by
    rw [← rootContainingProjectedClause_eq position]
    exact hfalse
  have hprojectedMatch :=
    (cubeDimacsBlocker_eval_false_iff coloring
      (rootContainingProjectedEmbedding position)
      (rootContainingProjectedCube position)).1 hprojectedFalse
  intro left right hordered hfixed
  by_cases hleftZero : left.val = 0
  · have hleft : left = 0 := Fin.ext hleftZero
    subst left
    have hrightPositive : 0 < right.val := by
      exact hordered
    let ambient := rootContainingAmbientVertex position right
    have hambientBounds :=
      rootContainingAmbientVertex_bounds position right hrightPositive
    have hrootColor : coloringEdge 12 coloring 0 ambient =
        decide (ambient ≤ 8) := by
      by_cases hneighbor : ambient ≤ 8
      · have htrue := twoCenterBranch_root_true hbranch
          hambientBounds.1 (by omega : ambient < 9)
        simpa [hneighbor] using htrue
      · have hfalseRoot := twoCenterBranch_root_false hbranch
          (by omega : 9 ≤ ambient) hambientBounds.2
        simpa [hneighbor] using hfalseRoot
    have hembeddingRoot := rootContainingEmbedding_root_val position
    have hembeddingRight := rootContainingEmbedding_nonroot_val
      position right hrightPositive
    have hdistinct : rootContainingEmbedding position 0 ≠
        rootContainingEmbedding position right := by
      intro hequal
      have hvalues := congrArg Fin.val hequal
      rw [hembeddingRoot, hembeddingRight] at hvalues
      exact (by omega : False)
    have hambientColor := coloring_symmetricEdgeVarTwelve coloring
      (rootContainingEmbedding position 0)
      (rootContainingEmbedding position right) hdistinct
    rw [hembeddingRoot, hembeddingRight] at hambientColor
    have hrequired := rootContaining_root_bit position right
      hrightPositive hfixed
    change coloring (symmetricEdgeVarTwelve
      (rootContainingEmbedding position 0)
      (rootContainingEmbedding position right)) = _
    exact hambientColor.trans (hrootColor.trans hrequired.symm)
  · have hleftPositive : 0 < left.val := by omega
    have hbits := rootContaining_nonroot_bits position left right
      hleftPositive hordered hfixed
    have hprojectedOrdered := projectedVertex_lt left right
      hleftPositive hordered
    have hmatch := hprojectedMatch (projectedVertex left)
      (projectedVertex right) hprojectedOrdered hbits.1
    change coloring (symmetricEdgeVarTwelve
      (rootContainingEmbedding position left)
      (rootContainingEmbedding position right)) = _
    change coloring (symmetricEdgeVarTwelve
      (rootContainingProjectedEmbedding position (projectedVertex left))
      (rootContainingProjectedEmbedding position (projectedVertex right))) = _
      at hmatch
    have hrightPositive : 0 < right.val := by
      have horderedValues : left.val < right.val := hordered
      omega
    rw [rootContainingEmbedding_nonroot position left hleftPositive,
      rootContainingEmbedding_nonroot position right hrightPositive]
    exact hmatch.trans hbits.2

noncomputable def rootContainingBlockerWitness
    (coloring : Nat → Bool) (p q : Nat)
    (hbranch : TwoCenterBranch coloring p q) (position : Fin 2409) :
    RootContainingBlockerWitness coloring
      (selectedCoreClause (rootContainingCorePosition position)) :=
  { embedding := rootContainingEmbedding position
    cube := rootContainingFullCube position
    representative := (rootContainingRepresentative position).cube
    inner := (rootContainingRepresentative position).inner
    motif := (rootContainingRepresentative position).motif
    motif_mem := (rootContainingRepresentative position).motif_mem
    embedding_injective := rootContainingEmbedding_injective position
    orbit := rootContainingFullCube_orbit position
    representative_forces := (rootContainingRepresentative position).forces
    projected_false_gives_full_match :=
      rootContainingProjected_false_gives_full_match coloring p q hbranch position }

noncomputable def conditionedCoreProvider
    (coloring : Nat → Bool) (p q : Nat)
    (hbranch : TwoCenterBranch coloring p q) :
    CoreBlockerWitnessProvider coloring :=
  { rootFree := rootFreeBlockerWitness
    rootContaining := rootContainingBlockerWitness coloring p q hbranch }

/-- The finite payload closes the final provider assumption of the semantic
composition theorem. -/
theorem no_degreeEight_cover6_avoiding
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 8)
    (havoid : AvoidsCover6 coloring) : False := by
  apply no_degreeEight_cover6_avoiding_of_coreProvider coloring
    hfree hdegree havoid
  exact conditionedCoreProvider (twoCenterColoring coloring)
    (pValue coloring) (qValue coloring)
    (twoCenter_branch coloring hdegree)

/-- Positive formulation of the degree-eight cover theorem: one of the six
motifs occurs as an induced seven-vertex subgraph. -/
theorem degreeEight_has_cover6_motif
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree : positiveRootDegree coloring = 8) :
    ∃ motif, motif ∈ cover6Motifs ∧
      InducedMotifOccurrence 7 coloring motif := by
  apply Classical.byContradiction
  intro hnone
  apply no_degreeEight_cover6_avoiding coloring hfree hdegree
  intro motif hmotif hoccurrence
  exact hnone ⟨motif, hmotif, hoccurrence⟩

#print axioms rootFreeBlockerWitness
#print axioms rootContainingBlockerWitness
#print axioms conditionedCoreProvider
#print axioms no_degreeEight_cover6_avoiding
#print axioms degreeEight_has_cover6_motif

end LRATCatcher.Tests.R44Cover6ConditionedWitnesses
