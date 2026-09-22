import LRATCatcher.Tests.R44Cover6ConditionedWitnesses
import LRATCatcher.Tests.R44Cover6Master7R34FoDPOCore

/-!
  # Selected-core semantics for the FoDPO degree-seven branch

  This module checks only the 7,686 clauses retained by the tracked compact
  LRAT core.  Its compact payload contains one fifteen-bit orbit/lift witness
  for each of the 4,221 K7 clauses and 3,264 projected K6 clauses in core
  order.  No complete F7 stream and no assignment space is enumerated.
-/

namespace LRATCatcher.Tests.R44Cover6Master7R34FoDPOSemantics

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6CubeBridge
open LRATCatcher.Tests.R44Cover6RepresentativeCubes
open LRATCatcher.Tests.R44Cover6S7Transport
open LRATCatcher.Tests.R44Cover6SemanticComposition
open LRATCatcher.Tests.R44Cover6ConditionedWitnesses
open LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization
open LRATCatcher.Tests.R44Cover6Master8IndexedSource
open LRATCatcher.Tests.R44Cover6Master7R34IndexedSource
open LRATCatcher.Tests.R44Cover6Master7R34FoDPOCore

set_option maxRecDepth 100000

/-! ## Ordered taxonomy of the tracked core -/

def d7CoreArrayPosition (position : Fin 7686) :
    Fin foDPOCoreFinIndices.size :=
  ⟨position.val, by rw [foDPOCoreFinIndexCount]; exact position.isLt⟩

def d7CoreSourceIndex (position : Fin 7686) : Fin branchClauseCount :=
  foDPOCoreFinIndices[d7CoreArrayPosition position]

def d7SelectedCoreClause (position : Fin 7686) : CNF.Clause Nat :=
  (branchSource foDPOCatalogueIndex).clauseAt
    (d7CoreSourceIndex position)

def d7BaseCorePosition (position : Fin 183) : Fin 7686 :=
  ⟨position.val, by omega⟩

def d7RootFreeCorePosition (position : Fin 4221) : Fin 7686 :=
  ⟨183 + position.val, by omega⟩

def d7RootContainingCorePosition (position : Fin 3264) : Fin 7686 :=
  ⟨4404 + position.val, by omega⟩

def d7UnitCorePosition (position : Fin 18) : Fin 7686 :=
  ⟨7668 + position.val, by omega⟩

theorem d7BaseCoreSourceIndex_range (position : Fin 183) :
    (d7CoreSourceIndex (d7BaseCorePosition position)).val <
      d7BaseClauseCount := by
  native_decide +revert

theorem d7RootFreeCoreSourceIndex_range (position : Fin 4221) :
    d7BlockClauseStart ≤
        (d7CoreSourceIndex (d7RootFreeCorePosition position)).val ∧
      (d7CoreSourceIndex (d7RootFreeCorePosition position)).val <
        d7LocalClauseStart := by
  native_decide +revert

theorem d7RootContainingCoreSourceIndex_range (position : Fin 3264) :
    d7LocalClauseStart ≤
        (d7CoreSourceIndex (d7RootContainingCorePosition position)).val ∧
      (d7CoreSourceIndex (d7RootContainingCorePosition position)).val <
        f7ClauseCount := by
  native_decide +revert

theorem d7UnitCoreSourceIndex_range (position : Fin 18) :
    f7ClauseCount ≤
        (d7CoreSourceIndex (d7UnitCorePosition position)).val ∧
      (d7CoreSourceIndex (d7UnitCorePosition position)).val <
        branchClauseCount := by
  native_decide +revert

/-! ## Compact selected witness stream -/

/-- Concatenated fifteen-bit codes: 4,221 K7 orbit witnesses, followed by
3,264 canonical K6 full-lift witnesses. -/
def d7CoreWitnessPayload : String :=
  include_str "../../../../scripts/r45_d12_cover9_universal/MASTER7_R34_FODPO_CORE_SEMANTIC_WITNESSES_V1.bin"

def d7CoreWitnessChunks : Array String := #[d7CoreWitnessPayload]

def d7CoreWitnessChunkSize : Nat := 18713
def d7CoreWitnessCharAt (index : Nat) : Char :=
  let chunk := d7CoreWitnessChunks.getD (index / d7CoreWitnessChunkSize) ""
  String.Pos.Raw.get! chunk ⟨index % d7CoreWitnessChunkSize⟩

def d7CoreWitnessCodeAt (item : Nat) : Nat :=
  let bitStart := item * witnessBits
  let digitStart := bitStart / 6
  let shift := bitStart % 6
  let window := (List.range 3).foldl (fun value digit =>
    value + alphabetValue (d7CoreWitnessCharAt (digitStart + digit)) *
      2 ^ (6 * digit)) 0
  window / 2 ^ shift % 2 ^ witnessBits

def d7RootFreeWitnessCode (position : Fin 4221) : Nat :=
  d7CoreWitnessCodeAt position.val

def d7RootContainingWitnessCode (position : Fin 3264) : Nat :=
  d7CoreWitnessCodeAt (4221 + position.val)

/-! ## K7 blocker reconstruction -/

def d7RootFreeSourceIndex (position : Fin 4221) : Nat :=
  (d7CoreSourceIndex (d7RootFreeCorePosition position)).val

def d7RootFreeLocation (position : Fin 4221) : List Nat × Nat :=
  (d7BlockLocation (d7RootFreeSourceIndex position - d7BlockClauseStart)).getD
    ([], 0)

def d7RootFreeItem (position : Fin 4221) : List Nat :=
  (d7RootFreeLocation position).1

def d7RootFreeCatalogueIndex (position : Fin 4221) : Nat :=
  (d7RootFreeLocation position).2

def d7RootFreeEmbedding (position : Fin 4221) : MotifEmbedding :=
  fun vertex => Fin.ofNat 12 ((d7RootFreeItem position).getD vertex.val 0)

def d7RootFreeRepresentativeIndex (position : Fin 4221) : Fin 6 :=
  ⟨d7RootFreeWitnessCode position % 6, Nat.mod_lt _ (by decide)⟩

def d7RootFreePermutationRank (position : Fin 4221) : Fin 5040 :=
  Fin.ofNat 5040 (d7RootFreeWitnessCode position / 6)

noncomputable def d7RootFreeRepresentative (position : Fin 4221) :
    RepresentativeWitness :=
  representativeWitness (d7RootFreeRepresentativeIndex position)

def d7RootFreeCube (position : Fin 4221) : Cover6Cube :=
  permuteCube (decodedPermutation (d7RootFreePermutationRank position))
    (representativeCubeAt (d7RootFreeRepresentativeIndex position))

def D7RootFreeFiniteCheck : Prop :=
  dataLength d7CoreWitnessChunks = 18713 ∧
  (∀ position : Fin 4221,
    d7RootFreeWitnessCode position < witnessCodeLimit) ∧
  (∀ (position : Fin 4221) (left right : MotifVertex),
    d7RootFreeEmbedding position left = d7RootFreeEmbedding position right →
      left = right) ∧
  (∀ position : Fin 4221,
    d7SelectedCoreClause (d7RootFreeCorePosition position) =
      cubeDimacsBlocker (d7RootFreeEmbedding position)
        (d7RootFreeCube position))

instance d7RootFreeFiniteCheckDecidable :
    Decidable D7RootFreeFiniteCheck := by
  unfold D7RootFreeFiniteCheck
  infer_instance

/-! ## Projected K6 blocker reconstruction -/

def d7RootContainingSourceIndex (position : Fin 3264) : Nat :=
  (d7CoreSourceIndex (d7RootContainingCorePosition position)).val

def d7RootContainingLocation (position : Fin 3264) : List Nat × Nat :=
  (d7LocalLocation
    (d7RootContainingSourceIndex position - d7LocalClauseStart)).getD ([], 0)

def d7RootContainingItem (position : Fin 3264) : List Nat :=
  (d7RootContainingLocation position).1

def d7RootContainingCatalogueIndex (position : Fin 3264) : Nat :=
  (d7RootContainingLocation position).2

def d7RootContainingNeighbourCount (position : Fin 3264) : Nat :=
  d7NeighborCount (d7RootContainingItem position)

def d7RootContainingProjectedCube (position : Fin 3264) : Cover6Cube :=
  let cube := d7LocalCubeAt (d7RootContainingNeighbourCount position)
    (d7RootContainingCatalogueIndex position)
  { ones := cube.1, fixed := cube.2 }

def d7RootContainingProjectedEmbedding (position : Fin 3264) :
    MotifEmbedding :=
  fun vertex =>
    Fin.ofNat 12 ((d7RootContainingItem position).getD vertex.val 0)

def d7RootContainingEmbedding (position : Fin 3264) : MotifEmbedding :=
  fun vertex =>
    if vertex.val = 0 then 0
    else Fin.ofNat 12
      ((d7RootContainingItem position).getD (vertex.val - 1) 0)

def d7RootContainingRepresentativeIndex (position : Fin 3264) : Fin 6 :=
  ⟨d7RootContainingWitnessCode position % 6, Nat.mod_lt _ (by decide)⟩

def d7RootContainingPermutationRank (position : Fin 3264) : Fin 5040 :=
  Fin.ofNat 5040 (d7RootContainingWitnessCode position / 6)

noncomputable def d7RootContainingRepresentative (position : Fin 3264) :
    RepresentativeWitness :=
  representativeWitness (d7RootContainingRepresentativeIndex position)

def d7RootContainingFullCube (position : Fin 3264) : Cover6Cube :=
  permuteCube (decodedPermutation (d7RootContainingPermutationRank position))
    (representativeCubeAt (d7RootContainingRepresentativeIndex position))

def d7RootContainingAmbientVertex
    (position : Fin 3264) (vertex : MotifVertex) : Nat :=
  (d7RootContainingItem position).getD (vertex.val - 1) 0

def D7RootContainingFiniteCheck : Prop :=
  (∀ position : Fin 3264,
    d7RootContainingWitnessCode position < witnessCodeLimit) ∧
  (∀ position : Fin 3264,
    d7SelectedCoreClause (d7RootContainingCorePosition position) =
      cubeDimacsBlocker (d7RootContainingProjectedEmbedding position)
        (d7RootContainingProjectedCube position)) ∧
  (∀ (position : Fin 3264) (left right : MotifVertex),
    d7RootContainingEmbedding position left =
      d7RootContainingEmbedding position right → left = right) ∧
  (∀ (left right : MotifVertex), 0 < left.val → left < right →
    projectedVertex left < projectedVertex right) ∧
  (∀ (position : Fin 3264) (vertex : MotifVertex), 0 < vertex.val →
    d7RootContainingEmbedding position vertex =
      d7RootContainingProjectedEmbedding position
        (projectedVertex vertex)) ∧
  (∀ (position : Fin 3264) (left right : MotifVertex),
    0 < left.val → left < right →
    (d7RootContainingFullCube position).fixed.testBit
        (graph6EdgePosition left.val right.val) = true →
    (d7RootContainingProjectedCube position).fixed.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) = true ∧
      (d7RootContainingProjectedCube position).ones.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) =
        (d7RootContainingFullCube position).ones.testBit
          (graph6EdgePosition left.val right.val)) ∧
  (∀ (position : Fin 3264) (vertex : MotifVertex), 0 < vertex.val →
    1 ≤ d7RootContainingAmbientVertex position vertex ∧
      d7RootContainingAmbientVertex position vertex < 12) ∧
  (∀ position : Fin 3264,
    (d7RootContainingEmbedding position 0).val = 0) ∧
  (∀ (position : Fin 3264) (vertex : MotifVertex), 0 < vertex.val →
    (d7RootContainingEmbedding position vertex).val =
      d7RootContainingAmbientVertex position vertex) ∧
  (∀ (position : Fin 3264) (right : MotifVertex), 0 < right.val →
    (d7RootContainingFullCube position).fixed.testBit
        (graph6EdgePosition 0 right.val) = true →
    (d7RootContainingFullCube position).ones.testBit
        (graph6EdgePosition 0 right.val) =
      decide (d7RootContainingAmbientVertex position right ≤ 7))

instance d7RootContainingFiniteCheckDecidable :
    Decidable D7RootContainingFiniteCheck := by
  unfold D7RootContainingFiniteCheck
  infer_instance

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 100 in
theorem d7CorePayloadFiniteChecks :
    D7RootFreeFiniteCheck ∧ D7RootContainingFiniteCheck := by
  native_decide

theorem d7RootFreeFiniteChecks : D7RootFreeFiniteCheck :=
  d7CorePayloadFiniteChecks.1

theorem d7RootContainingFiniteChecks : D7RootContainingFiniteCheck :=
  d7CorePayloadFiniteChecks.2

theorem d7RootFreeEmbedding_injective (position : Fin 4221) :
    Function.Injective (d7RootFreeEmbedding position) :=
  d7RootFreeFiniteChecks.2.2.1 position

theorem d7RootFreeClause_eq (position : Fin 4221) :
    d7SelectedCoreClause (d7RootFreeCorePosition position) =
      cubeDimacsBlocker (d7RootFreeEmbedding position)
        (d7RootFreeCube position) :=
  d7RootFreeFiniteChecks.2.2.2 position

theorem d7RootFreeCube_orbit (position : Fin 4221) :
    CubeInOrbitOf (d7RootFreeCube position)
      (d7RootFreeRepresentative position).cube := by
  refine ⟨decodedPermutation (d7RootFreePermutationRank position), ?_⟩
  unfold d7RootFreeRepresentative
  rw [representativeWitness_cube]
  rfl

noncomputable def d7RootFreeBlockerWitness (position : Fin 4221) :
    RootFreeBlockerWitness
      (d7SelectedCoreClause (d7RootFreeCorePosition position)) :=
  { embedding := d7RootFreeEmbedding position
    cube := d7RootFreeCube position
    representative := (d7RootFreeRepresentative position).cube
    inner := (d7RootFreeRepresentative position).inner
    motif := (d7RootFreeRepresentative position).motif
    motif_mem := (d7RootFreeRepresentative position).motif_mem
    embedding_injective := d7RootFreeEmbedding_injective position
    orbit := d7RootFreeCube_orbit position
    representative_forces := (d7RootFreeRepresentative position).forces
    clause_eq := d7RootFreeClause_eq position }

theorem d7RootContainingProjectedClause_eq (position : Fin 3264) :
    d7SelectedCoreClause (d7RootContainingCorePosition position) =
      cubeDimacsBlocker (d7RootContainingProjectedEmbedding position)
        (d7RootContainingProjectedCube position) :=
  d7RootContainingFiniteChecks.2.1 position

theorem d7RootContainingEmbedding_injective (position : Fin 3264) :
    Function.Injective (d7RootContainingEmbedding position) :=
  d7RootContainingFiniteChecks.2.2.1 position

theorem d7RootContainingFullCube_orbit (position : Fin 3264) :
    CubeInOrbitOf (d7RootContainingFullCube position)
      (d7RootContainingRepresentative position).cube := by
  refine ⟨decodedPermutation (d7RootContainingPermutationRank position), ?_⟩
  unfold d7RootContainingRepresentative
  rw [representativeWitness_cube]
  rfl

theorem d7ProjectedVertex_lt
    (left right : MotifVertex) (hleft : 0 < left.val)
    (hordered : left < right) :
    projectedVertex left < projectedVertex right :=
  d7RootContainingFiniteChecks.2.2.2.1 left right hleft hordered

theorem d7RootContainingEmbedding_nonroot
    (position : Fin 3264) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    d7RootContainingEmbedding position vertex =
      d7RootContainingProjectedEmbedding position
        (projectedVertex vertex) :=
  d7RootContainingFiniteChecks.2.2.2.2.1 position vertex hvertex

theorem d7RootContaining_nonroot_bits
    (position : Fin 3264) (left right : MotifVertex)
    (hleft : 0 < left.val) (hordered : left < right)
    (hfixed : (d7RootContainingFullCube position).fixed.testBit
      (graph6EdgePosition left.val right.val) = true) :
    (d7RootContainingProjectedCube position).fixed.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) = true ∧
      (d7RootContainingProjectedCube position).ones.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) =
        (d7RootContainingFullCube position).ones.testBit
          (graph6EdgePosition left.val right.val) :=
  d7RootContainingFiniteChecks.2.2.2.2.2.1
    position left right hleft hordered hfixed

theorem d7RootContainingAmbientVertex_bounds
    (position : Fin 3264) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    1 ≤ d7RootContainingAmbientVertex position vertex ∧
      d7RootContainingAmbientVertex position vertex < 12 :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.1
    position vertex hvertex

theorem d7RootContainingEmbedding_root_val (position : Fin 3264) :
    (d7RootContainingEmbedding position 0).val = 0 :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.2.1 position

theorem d7RootContainingEmbedding_nonroot_val
    (position : Fin 3264) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    (d7RootContainingEmbedding position vertex).val =
      d7RootContainingAmbientVertex position vertex :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.2.2.1
    position vertex hvertex

theorem d7RootContaining_root_bit
    (position : Fin 3264) (right : MotifVertex)
    (hright : 0 < right.val)
    (hfixed : (d7RootContainingFullCube position).fixed.testBit
      (graph6EdgePosition 0 right.val) = true) :
    (d7RootContainingFullCube position).ones.testBit
        (graph6EdgePosition 0 right.val) =
      decide (d7RootContainingAmbientVertex position right ≤ 7) :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.2.2.2
    position right hright hfixed

/-! ## Base and unit clauses -/

theorem d7LeftTriangleItem_valid (index : Nat) (hindex : index < 35) :
    let item :=
      (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 1 7 3).getD
        index []
    item.length = 3 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 8) ∧ item.Nodup := by
  native_decide +revert

theorem d7RightTriangleItem_valid (index : Nat) (hindex : index < 4) :
    let item :=
      (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 8 4 3).getD
        index []
    item.length = 3 ∧
      (∀ value ∈ item, 8 ≤ value ∧ value < 12) ∧ item.Nodup := by
  native_decide +revert

theorem d7BaseClause_eval_true
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (index : Nat) (hindex : index < d7BaseClauseCount) :
    CNF.Clause.eval coloring (dimacsClause (d7BaseClause index)) = true := by
  by_cases hfour : index < 660
  · let item :=
      (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 1 11 4).getD
        (index / 2) []
    have hitemIndex : index / 2 < 330 := by omega
    have hvalid := fourBlockItem_valid hitemIndex
    change item.length = 4 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 12) ∧ item.Nodup at hvalid
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
      simpa [d7BaseClause, hfour, hpositive, item,
        LRATCatcher.Tests.R44Cover6Master8IndexedSource.baseClause] using
        hsatisfied
    · have hnotRed := hfree.1 item hvalid.1
          (fun value hvalue => (hvalid.2.1 value hvalue).2)
          hvalid.2.2
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_false_edge 12 item coloring hnotRed
      obtain ⟨left, right, hleft, hright, hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 item dimacsVariable hvariable
      have hsatisfied := signedPairClause_eval_true coloring item false
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [d7BaseClause, hfour, hpositive, item,
        LRATCatcher.Tests.R44Cover6Master8IndexedSource.baseClause] using
        hsatisfied
  · by_cases hleftBlock : index < 695
    · let item :=
        (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 1 7 3).getD
          (index - 660) []
      have hvalid := d7LeftTriangleItem_valid (index - 660) (by omega)
      change item.length = 3 ∧
        (∀ value ∈ item, 1 ≤ value ∧ value < 8) ∧ item.Nodup at hvalid
      let ambient := 0 :: item
      have hnotRed := hfree.1 ambient (by simp [ambient, hvalid.1])
        (by
          intro value hvalue
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · omega
          · have := hvalid.2.1 value hvalue
            omega)
        (by
          simp only [ambient, List.nodup_cons]
          exact ⟨by
            intro hzero
            have := hvalid.2.1 0 hzero
            omega, hvalid.2.2⟩)
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
          have hroot := hrootPositive right
            (hvalid.2.1 right hright).1 (hvalid.2.1 right hright).2
          have hrootRaw : coloring (edgeVar 12 0 right) = true := by
            simpa [coloringEdge, hleftRight] using hroot
          simp [hrootRaw] at hcolor
        · exact hleft
      have hsatisfied := signedPairClause_eval_true coloring item false
        hleft hright hleftRight (by
          have := hvalid.2.1 right hright
          omega) hcolor
      simpa [d7BaseClause, hfour, hleftBlock, item] using hsatisfied
    · have hrightIndex : index - 695 < 4 := by
        unfold d7BaseClauseCount at hindex
        omega
      let item :=
        (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 8 4 3).getD
          (index - 695) []
      have hvalid := d7RightTriangleItem_valid (index - 695) hrightIndex
      change item.length = 3 ∧
        (∀ value ∈ item, 8 ≤ value ∧ value < 12) ∧ item.Nodup at hvalid
      let ambient := 0 :: item
      have hnotBlue := hfree.2 ambient (by simp [ambient, hvalid.1])
        (by
          intro value hvalue
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · omega
          · exact (hvalid.2.1 value hvalue).2)
        (by
          simp only [ambient, List.nodup_cons]
          exact ⟨by
            intro hzero
            have := hvalid.2.1 0 hzero
            omega, hvalid.2.2⟩)
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
      have hleft : left ∈ item := by
        rcases List.mem_cons.mp hleftAmbient with hzero | hleft
        · subst left
          have hroot := hrootRight right
            (hvalid.2.1 right hright).1 (hvalid.2.1 right hright).2
          have hrootRaw : coloring (edgeVar 12 0 right) = false := by
            simpa [coloringEdge, hleftRight] using hroot
          simp [hrootRaw] at hcolor
        · exact hleft
      have hsatisfied := signedPairClause_eval_true coloring item true
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [d7BaseClause, hfour, hleftBlock, item] using hsatisfied

theorem d7SelectedBaseClause_eq (position : Fin 183) :
    d7SelectedCoreClause (d7BaseCorePosition position) =
      dimacsClause (d7BaseClause
        (d7CoreSourceIndex (d7BaseCorePosition position)).val) := by
  native_decide +revert

def d7SelectedUnitTailPosition (position : Fin 18) : Fin 21 :=
  ⟨(d7CoreSourceIndex (d7UnitCorePosition position)).val - f7ClauseCount,
    by
      have h := d7UnitCoreSourceIndex_range position
      unfold branchClauseCount r34UnitClauseCount at h
      omega⟩

theorem d7SelectedUnitClause_eq (position : Fin 18) :
    d7SelectedCoreClause (d7UnitCorePosition position) =
      (branchSource foDPOCatalogueIndex).clauseAt
        ⟨f7ClauseCount + (d7SelectedUnitTailPosition position).val, by
          change f7ClauseCount + (d7SelectedUnitTailPosition position).val <
            branchClauseCount
          dsimp [branchClauseCount, f7ClauseCount, r34UnitClauseCount]
          omega⟩ := by
  native_decide +revert

/-! ## Projected full-lift semantics -/

theorem d7RootContainingProjected_false_gives_full_match
    (coloring : Nat → Bool)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (position : Fin 3264)
    (hfalse : CNF.Clause.eval coloring
      (d7SelectedCoreClause (d7RootContainingCorePosition position)) = false) :
    CubeMatchesLocal
      (embeddedLocalEdges coloring (d7RootContainingEmbedding position))
      (d7RootContainingFullCube position) := by
  have hprojectedFalse : CNF.Clause.eval coloring
      (cubeDimacsBlocker (d7RootContainingProjectedEmbedding position)
        (d7RootContainingProjectedCube position)) = false := by
    rw [← d7RootContainingProjectedClause_eq position]
    exact hfalse
  have hprojectedMatch :=
    (cubeDimacsBlocker_eval_false_iff coloring
      (d7RootContainingProjectedEmbedding position)
      (d7RootContainingProjectedCube position)).1 hprojectedFalse
  intro left right hordered hfixed
  by_cases hleftZero : left.val = 0
  · have hleft : left = 0 := Fin.ext hleftZero
    subst left
    have hrightPositive : 0 < right.val := hordered
    let ambient := d7RootContainingAmbientVertex position right
    have hambientBounds :=
      d7RootContainingAmbientVertex_bounds position right hrightPositive
    have hrootColor : coloringEdge 12 coloring 0 ambient =
        decide (ambient ≤ 7) := by
      by_cases hneighbor : ambient ≤ 7
      · simpa [hneighbor] using hrootPositive ambient
          hambientBounds.1 (by omega : ambient < 8)
      · simpa [hneighbor] using hrootRight ambient
          (by omega : 8 ≤ ambient) hambientBounds.2
    have hembeddingRoot := d7RootContainingEmbedding_root_val position
    have hembeddingRight := d7RootContainingEmbedding_nonroot_val
      position right hrightPositive
    have hdistinct : d7RootContainingEmbedding position 0 ≠
        d7RootContainingEmbedding position right := by
      intro hequal
      have hvalues := congrArg Fin.val hequal
      rw [hembeddingRoot, hembeddingRight] at hvalues
      exact (by omega : False)
    have hambientColor := coloring_symmetricEdgeVarTwelve coloring
      (d7RootContainingEmbedding position 0)
      (d7RootContainingEmbedding position right) hdistinct
    rw [hembeddingRoot, hembeddingRight] at hambientColor
    have hrequired := d7RootContaining_root_bit position right
      hrightPositive hfixed
    change coloring (symmetricEdgeVarTwelve
      (d7RootContainingEmbedding position 0)
      (d7RootContainingEmbedding position right)) = _
    exact hambientColor.trans (hrootColor.trans hrequired.symm)
  · have hleftPositive : 0 < left.val := by omega
    have hbits := d7RootContaining_nonroot_bits position left right
      hleftPositive hordered hfixed
    have hprojectedOrdered := d7ProjectedVertex_lt left right
      hleftPositive hordered
    have hmatch := hprojectedMatch (projectedVertex left)
      (projectedVertex right) hprojectedOrdered hbits.1
    change coloring (symmetricEdgeVarTwelve
      (d7RootContainingEmbedding position left)
      (d7RootContainingEmbedding position right)) = _
    change coloring (symmetricEdgeVarTwelve
      (d7RootContainingProjectedEmbedding position (projectedVertex left))
      (d7RootContainingProjectedEmbedding position (projectedVertex right))) = _
      at hmatch
    have hrightPositive : 0 < right.val := by
      have horderedValues : left.val < right.val := hordered
      omega
    rw [d7RootContainingEmbedding_nonroot position left hleftPositive,
      d7RootContainingEmbedding_nonroot position right hrightPositive]
    exact hmatch.trans hbits.2

noncomputable def d7RootContainingBlockerWitness
    (coloring : Nat → Bool)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (position : Fin 3264) :
    RootContainingBlockerWitness coloring
      (d7SelectedCoreClause (d7RootContainingCorePosition position)) :=
  { embedding := d7RootContainingEmbedding position
    cube := d7RootContainingFullCube position
    representative := (d7RootContainingRepresentative position).cube
    inner := (d7RootContainingRepresentative position).inner
    motif := (d7RootContainingRepresentative position).motif
    motif_mem := (d7RootContainingRepresentative position).motif_mem
    embedding_injective := d7RootContainingEmbedding_injective position
    orbit := d7RootContainingFullCube_orbit position
    representative_forces := (d7RootContainingRepresentative position).forces
    projected_false_gives_full_match :=
      d7RootContainingProjected_false_gives_full_match coloring
        hrootPositive hrootRight position }

/-! ## Selected-core evaluation and branch contradiction -/

theorem d7SelectedCoreClause_eval_true
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (havoid : AvoidsCover6 coloring)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (hunit : ∀ position : Fin 18,
      CNF.Clause.eval coloring
        (d7SelectedCoreClause (d7UnitCorePosition position)) = true)
    (position : Fin 7686) :
    CNF.Clause.eval coloring (d7SelectedCoreClause position) = true := by
  by_cases hbase : position.val < 183
  · let basePosition : Fin 183 := ⟨position.val, hbase⟩
    have hposition : d7BaseCorePosition basePosition = position := by
      apply Fin.ext
      simp [d7BaseCorePosition, basePosition]
    rw [← hposition, d7SelectedBaseClause_eq]
    exact d7BaseClause_eval_true coloring hfree hrootPositive hrootRight
      _ (d7BaseCoreSourceIndex_range basePosition)
  · by_cases hrootFree : position.val < 4404
    · let payloadPosition : Fin 4221 :=
        ⟨position.val - 183, by omega⟩
      have hposition : d7RootFreeCorePosition payloadPosition = position := by
        apply Fin.ext
        simp [d7RootFreeCorePosition, payloadPosition]
        omega
      rw [← hposition]
      exact rootFreeBlockerWitness_eval_true hfree havoid
        (d7RootFreeBlockerWitness payloadPosition)
    · by_cases hrootContaining : position.val < 7668
      · let payloadPosition : Fin 3264 :=
          ⟨position.val - 4404, by omega⟩
        have hposition :
            d7RootContainingCorePosition payloadPosition = position := by
          apply Fin.ext
          simp [d7RootContainingCorePosition, payloadPosition]
          omega
        rw [← hposition]
        exact rootContainingBlockerWitness_eval_true hfree havoid
          (d7RootContainingBlockerWitness coloring hrootPositive hrootRight
            payloadPosition)
      · let unitPosition : Fin 18 := ⟨position.val - 7668, by omega⟩
        have hposition : d7UnitCorePosition unitPosition = position := by
          apply Fin.ext
          simp [d7UnitCorePosition, unitPosition]
          omega
        rw [← hposition]
        exact hunit unitPosition

theorem d7CoreSelection_eval_true
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (havoid : AvoidsCover6 coloring)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (hunit : ∀ position : Fin 18,
      CNF.Clause.eval coloring
        (d7SelectedCoreClause (d7UnitCorePosition position)) = true) :
    CNF.eval coloring
      ((branchSource foDPOCatalogueIndex).selectCNF
        foDPOCoreFinIndices) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hsize :
      ((branchSource foDPOCatalogueIndex).selectCNF
        foDPOCoreFinIndices).clauses.size = 7686 := by
    unfold LRATCatcher.Tests.R44Cover6Master8CoreBridge.IndexedCNFSource.selectCNF
    simpa using foDPOCoreFinIndexCount
  let position : Fin 7686 := ⟨index, by omega⟩
  have hsatisfied := d7SelectedCoreClause_eval_true coloring hfree havoid
    hrootPositive hrootRight hunit position
  simpa [LRATCatcher.Tests.R44Cover6Master8CoreBridge.IndexedCNFSource.selectCNF,
    d7SelectedCoreClause, d7CoreSourceIndex, d7CoreArrayPosition, position]
    using hsatisfied

theorem no_degreeSeven_foDPO_cover6_avoiding
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree :
      LRATCatcher.Tests.R44OrderTwelveTwoCenterCases.positiveRootDegree
        coloring = 7)
    (havoid : AvoidsCover6 coloring)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring foDPOCatalogueIndex
      sourceToRepresentative) : False := by
  let normalized :=
    d7R34RelabeledColoring coloring sourceToRepresentative
  have hnormalizedFree : isRamseyFree 12 4 4 normalized :=
    (d7R34Relabeled_isRamseyFree_iff coloring sourceToRepresentative).mp hfree
  have hnormalizedAvoid : AvoidsCover6 normalized :=
    (d7R34Relabeled_avoidsCover6_iff coloring sourceToRepresentative).mp havoid
  have hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 normalized 0 vertex = true := by
    intro vertex hlower hupper
    let localIndex : Fin 7 := ⟨vertex - 1, by omega⟩
    have hroot := d7R34Relabeled_root_positive coloring hdegree
      sourceToRepresentative localIndex
    have hlabel : (d7PositiveLabel localIndex).val = vertex := by
      simp [d7PositiveLabel, localIndex]
      omega
    simpa [normalized, hlabel] using hroot
  have hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 normalized 0 vertex = false := by
    intro vertex hlower hupper
    let localIndex : Fin 4 := ⟨vertex - 8, by omega⟩
    have hroot := d7R34Relabeled_root_right coloring hdegree
      sourceToRepresentative localIndex
    have hlabel : (d7RightLabel localIndex).val = vertex := by
      simp [d7RightLabel, localIndex]
      omega
    simpa [normalized, hlabel] using hroot
  have hunit : ∀ position : Fin 18,
      CNF.Clause.eval normalized
        (d7SelectedCoreClause (d7UnitCorePosition position)) = true := by
    intro position
    rw [d7SelectedUnitClause_eq]
    exact foDPORelabeled_unitTail_eval_true coloring
      sourceToRepresentative hmap (d7SelectedUnitTailPosition position)
  have htrue := d7CoreSelection_eval_true normalized hnormalizedFree
    hnormalizedAvoid hrootPositive hrootRight hunit
  have hfalse := foDPOCoreSelection_unsat normalized
  exact Bool.noConfusion (htrue.symm.trans hfalse)

#print axioms d7CorePayloadFiniteChecks
#print axioms d7BaseClause_eval_true
#print axioms d7CoreSelection_eval_true
#print axioms no_degreeSeven_foDPO_cover6_avoiding

end LRATCatcher.Tests.R44Cover6Master7R34FoDPOSemantics
