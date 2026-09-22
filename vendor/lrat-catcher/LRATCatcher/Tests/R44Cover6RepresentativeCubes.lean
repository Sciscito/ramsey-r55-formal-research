import LRATCatcher.Tests.R44Cover6CubeBridge

/-!
  # Local R(4,4) admissibility and the six representative cover6 cubes

  This module is deliberately finite and local.  It defines the mathematical
  admissibility condition on a seven-vertex edge assignment, materializes the
  six frozen `(ones, fixed)` representatives, and checks that each one has a
  unique admissible 21-bit completion.  The target mask is then identified
  with an explicit relabeling of one of the six graph6 motifs.
-/

namespace LRATCatcher.Tests.R44Cover6RepresentativeCubes

open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6CubeBridge

/-! ## Explicit local R(4,4) condition -/

def combinations {Alpha : Type} : List Alpha → Nat → List (List Alpha)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | head :: tail, size + 1 =>
      (combinations tail size).map (head :: .) ++
        combinations tail (size + 1)

def motifFourSubsets : List (List MotifVertex) :=
  combinations (List.finRange 7) 4

def motifPairsWithin
    (vertices : List MotifVertex) : List (MotifVertex × MotifVertex) :=
  vertices.flatMap fun left =>
    vertices.filterMap fun right =>
      if left < right then some (left, right) else none

/-- Boolean executable form: every four-set has at least one edge and at
least one non-edge. -/
def localR44Check (localEdges : LocalEdgeAssignment) : Bool :=
  motifFourSubsets.all fun vertices =>
    let pairs := motifPairsWithin vertices
    pairs.any (fun pair => localEdges pair.1 pair.2) &&
      pairs.any (fun pair => !(localEdges pair.1 pair.2))

/-- Propositional local admissibility used by the cube-safety interface. -/
def LocalR44Admissible (localEdges : LocalEdgeAssignment) : Prop :=
  localR44Check localEdges = true

/-- Human-facing expansion of admissibility: each four-set explicitly
contains a positive and a negative pair. -/
def EveryFourHasBothColors (localEdges : LocalEdgeAssignment) : Prop :=
  ∀ vertices, vertices ∈ motifFourSubsets →
    (∃ pair, pair ∈ motifPairsWithin vertices ∧
      localEdges pair.1 pair.2 = true) ∧
    (∃ pair, pair ∈ motifPairsWithin vertices ∧
      localEdges pair.1 pair.2 = false)

theorem localR44Admissible_iff
    (localEdges : LocalEdgeAssignment) :
    LocalR44Admissible localEdges ↔ EveryFourHasBothColors localEdges := by
  simp only [LocalR44Admissible, localR44Check, List.all_eq_true,
    Bool.and_eq_true, List.any_eq_true, EveryFourHasBothColors]
  constructor
  · intro hall vertices hvertices
    obtain ⟨htrue, hfalse⟩ := hall vertices hvertices
    constructor
    · simpa using htrue
    · obtain ⟨pair, hpair, hedge⟩ := hfalse
      exact ⟨pair, hpair, by cases hvalue : localEdges pair.1 pair.2 <;> simp_all⟩
  · intro hall vertices hvertices
    obtain ⟨⟨truePair, htruePair, htrue⟩,
      ⟨falsePair, hfalsePair, hfalse⟩⟩ := hall vertices hvertices
    constructor
    · exact ⟨truePair, htruePair, htrue⟩
    · exact ⟨falsePair, hfalsePair, by simp [hfalse]⟩

/-! ## Packed masks and the frozen representatives -/

def maskLocalEdges (mask : Nat) : LocalEdgeAssignment := fun left right =>
  mask.testBit (graph6EdgePosition left.val right.val)

def representativeCube0 : Cover6Cube :=
  { ones := 0x3, fixed := 0xDF677 }

def representativeCube1 : Cover6Cube :=
  { ones := 0x3E6BE, fixed := 0x1BE6BE }

def representativeCube2 : Cover6Cube :=
  { ones := 0x84AE, fixed := 0x18FDFE }

def representativeCube3 : Cover6Cube :=
  { ones := 0x8CF5, fixed := 0x1B8FFD }

def representativeCube4 : Cover6Cube :=
  { ones := 0x897E, fixed := 0x15FDFE }

def representativeCube5 : Cover6Cube :=
  { ones := 0x84ED, fixed := 0x1DF5EF }

def representativeCubes : List Cover6Cube := [
  representativeCube0, representativeCube1, representativeCube2,
  representativeCube3, representativeCube4, representativeCube5
]

def representativeTargets : List Nat :=
  [0x12098B, 0x3E6BE, 0x386AE, 0x49CF5, 0x8897E, 0x28EED]

private theorem cover6Cube_wellFormed_of_fin21
    (cube : Cover6Cube)
    (honesBound : cube.ones < 2 ^ 21)
    (hfixedBound : cube.fixed < 2 ^ 21)
    (hfixedBits : ∀ position : Fin 21,
      cube.ones.testBit position.val = true →
        cube.fixed.testBit position.val = true) :
    cube.WellFormed := by
  exact ⟨honesBound, hfixedBound, fun position hposition hones =>
    hfixedBits ⟨position, hposition⟩ hones⟩

theorem representativeCube0_wellFormed :
    representativeCube0.WellFormed := by
  apply cover6Cube_wellFormed_of_fin21
  · native_decide
  · native_decide
  · native_decide

theorem representativeCube1_wellFormed :
    representativeCube1.WellFormed := by
  apply cover6Cube_wellFormed_of_fin21
  · native_decide
  · native_decide
  · native_decide

theorem representativeCube2_wellFormed :
    representativeCube2.WellFormed := by
  apply cover6Cube_wellFormed_of_fin21
  · native_decide
  · native_decide
  · native_decide

theorem representativeCube3_wellFormed :
    representativeCube3.WellFormed := by
  apply cover6Cube_wellFormed_of_fin21
  · native_decide
  · native_decide
  · native_decide

theorem representativeCube4_wellFormed :
    representativeCube4.WellFormed := by
  apply cover6Cube_wellFormed_of_fin21
  · native_decide
  · native_decide
  · native_decide

theorem representativeCube5_wellFormed :
    representativeCube5.WellFormed := by
  apply cover6Cube_wellFormed_of_fin21
  · native_decide
  · native_decide
  · native_decide

/-! A Boolean packed-mask view used only to make the six finite uniqueness
checks executable.  The following theorem reconnects it to the proposition
`CubeMatchesLocal` consumed by the semantic bridge. -/

def cubeMatchesMaskCheck (mask : Nat) (cube : Cover6Cube) : Bool :=
  motifUpperPairs.all fun pair =>
    let position := motifPairPosition pair
    if cube.fixed.testBit position then
      mask.testBit position == cube.ones.testBit position
    else true

theorem cubeMatchesMaskCheck_eq_true_iff
    (mask : Nat) (cube : Cover6Cube) :
    cubeMatchesMaskCheck mask cube = true ↔
      CubeMatchesLocal (maskLocalEdges mask) cube := by
  constructor
  · intro hcheck left right hordered hfixed
    have hall := List.all_eq_true.mp hcheck
    have hpair := hall (left, right)
      ((mem_motifUpperPairs_iff left right).2 hordered)
    change
      (if cube.fixed.testBit
          (motifPairPosition (left, right)) then
        mask.testBit (motifPairPosition (left, right)) ==
          cube.ones.testBit (motifPairPosition (left, right))
      else true) = true at hpair
    rw [show cube.fixed.testBit (motifPairPosition (left, right)) = true by
      simpa [motifPairPosition] using hfixed] at hpair
    simpa [maskLocalEdges, motifPairPosition] using beq_iff_eq.mp hpair
  · intro hmatch
    apply List.all_eq_true.mpr
    intro pair hpair
    have hordered := (mem_motifUpperPairs_iff pair.1 pair.2).1 hpair
    by_cases hfixed :
        cube.fixed.testBit (motifPairPosition pair) = true
    · have hequal := hmatch pair.1 pair.2 hordered (by
        simpa [motifPairPosition] using hfixed)
      change
        (if cube.fixed.testBit (motifPairPosition pair) then
          mask.testBit (motifPairPosition pair) ==
            cube.ones.testBit (motifPairPosition pair)
        else true) = true
      rw [hfixed]
      apply beq_iff_eq.mpr
      simpa [maskLocalEdges, motifPairPosition] using hequal
    · have hfixedFalse :
          cube.fixed.testBit (motifPairPosition pair) = false := by
        cases hvalue : cube.fixed.testBit (motifPairPosition pair) <;>
          simp_all
      change
        (if cube.fixed.testBit (motifPairPosition pair) then
          mask.testBit (motifPairPosition pair) ==
            cube.ones.testBit (motifPairPosition pair)
        else true) = true
      simp [hfixedFalse]

/-! The packed mask below uses exactly the same 21 positions as the semantic
upper-triangle interface.  These two small finite lemmas make that indexing
correspondence explicit, instead of hiding it inside a later computation. -/

def motifPairForPosition
    (position : Fin 21) : MotifVertex × MotifVertex :=
  motifUpperPairs.getD position.val (0, 0)

theorem motifPairForPosition_ordered (position : Fin 21) :
    (motifPairForPosition position).1 <
      (motifPairForPosition position).2 := by
  native_decide +revert

theorem motifPairForPosition_position (position : Fin 21) :
    motifPairPosition (motifPairForPosition position) = position.val := by
  native_decide +revert

theorem cubeMatchesLocal_fixed_bit
    (mask : Nat) (cube : Cover6Cube)
    (hmatch : CubeMatchesLocal (maskLocalEdges mask) cube)
    (position : Fin 21)
    (hfixed : cube.fixed.testBit position.val = true) :
    mask.testBit position.val = cube.ones.testBit position.val := by
  have hfixedAtPair : cube.fixed.testBit
      (motifPairPosition (motifPairForPosition position)) = true := by
    rw [motifPairForPosition_position]
    exact hfixed
  have hequal := hmatch
    (motifPairForPosition position).1
    (motifPairForPosition position).2
    (motifPairForPosition_ordered position) (by
      simpa [motifPairPosition] using hfixedAtPair)
  change mask.testBit
      (motifPairPosition (motifPairForPosition position)) =
    cube.ones.testBit
      (motifPairPosition (motifPairForPosition position)) at hequal
  rw [motifPairForPosition_position] at hequal
  exact hequal

/-- A bounded semantic match is the usual packed-mask equation.  The
well-formedness hypothesis is used precisely to rule out an unfixed `ones`
bit and to bound both cube masks to the 21 local positions. -/
theorem cubeMatchesLocal_and_eq_ones
    (mask : Nat) (cube : Cover6Cube)
    (hmask : mask < 2 ^ 21)
    (hwellFormed : cube.WellFormed)
    (hmatch : CubeMatchesLocal (maskLocalEdges mask) cube) :
    mask &&& cube.fixed = cube.ones := by
  apply Nat.eq_of_testBit_eq
  intro position
  rw [Nat.testBit_and]
  by_cases hposition : position < 21
  · let finitePosition : Fin 21 := ⟨position, hposition⟩
    by_cases hfixed : cube.fixed.testBit position = true
    · have hequal := cubeMatchesLocal_fixed_bit mask cube hmatch
        finitePosition (by simpa [finitePosition] using hfixed)
      change mask.testBit position = cube.ones.testBit position at hequal
      rw [hfixed, hequal]
      simp
    · have hfixedFalse : cube.fixed.testBit position = false := by
        cases hvalue : cube.fixed.testBit position <;> simp_all
      have honesFalse : cube.ones.testBit position = false := by
        cases hones : cube.ones.testBit position with
        | false => rfl
        | true =>
            exact False.elim (hfixed
              (hwellFormed.2.2 position hposition hones))
      simp [hfixedFalse, honesFalse]
  · have hge : 21 ≤ position := Nat.le_of_not_gt hposition
    have hpow : 2 ^ 21 ≤ 2 ^ position :=
      Nat.pow_le_pow_right Nat.zero_lt_two hge
    have hmaskBit : mask.testBit position = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hmask hpow)
    have hfixedBit : cube.fixed.testBit position = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hwellFormed.2.1 hpow)
    have honesBit : cube.ones.testBit position = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hwellFormed.1 hpow)
    simp [hmaskBit, hfixedBit, honesBit]

/-! ## Finite completion enumerator and first uniqueness check -/

/-- Enumerate the width-`width` completions of `(ones,fixed)` without
scanning all `2^width` masks.  A free bit doubles the current list; a fixed
bit selects exactly its required value. -/
def cubeCompletionsAux (cube : Cover6Cube) : Nat → List Nat
  | 0 => [0]
  | position + 1 =>
      let previous := cubeCompletionsAux cube position
      if cube.fixed.testBit position then
        if cube.ones.testBit position then
          previous.map fun mask => mask + 2 ^ position
        else previous
      else
        previous ++ previous.map fun mask => mask + 2 ^ position

private theorem mod_two_pow_succ (mask position : Nat) :
    mask % 2 ^ (position + 1) =
      2 ^ position * (mask.testBit position).toNat +
        mask % 2 ^ position := by
  rw [Nat.mod_pow_succ, Nat.add_comm, Nat.toNat_testBit]

/-- Completeness of the compact enumerator.  Working modulo `2^width`
avoids an exhaustive search: the induction appends exactly the current high
bit to the already-enumerated lower prefix. -/
theorem cubeCompletionsAux_complete_mod
    (cube : Cover6Cube) (width mask : Nat)
    (hmatch : ∀ position, position < width →
      cube.fixed.testBit position = true →
      mask.testBit position = cube.ones.testBit position) :
    mask % 2 ^ width ∈ cubeCompletionsAux cube width := by
  induction width with
  | zero => simp [cubeCompletionsAux, Nat.mod_one]
  | succ width inductionHypothesis =>
      have hlower : mask % 2 ^ width ∈ cubeCompletionsAux cube width :=
        inductionHypothesis (fun position hposition hfixed =>
          hmatch position (Nat.lt_succ_of_lt hposition) hfixed)
      by_cases hfixed : cube.fixed.testBit width = true
      · by_cases hones : cube.ones.testBit width = true
        · have hbit := hmatch width (Nat.lt_succ_self width) hfixed
          have hmod : mask % 2 ^ (width + 1) =
              mask % 2 ^ width + 2 ^ width := by
            rw [mod_two_pow_succ]
            simp [hbit, hones, Nat.add_comm]
          simp only [cubeCompletionsAux, hfixed, hones, if_true]
          exact List.mem_map.mpr ⟨mask % 2 ^ width, hlower, hmod.symm⟩
        · have honesFalse : cube.ones.testBit width = false := by
            cases hvalue : cube.ones.testBit width <;> simp_all
          have hbit := hmatch width (Nat.lt_succ_self width) hfixed
          have hmod : mask % 2 ^ (width + 1) =
              mask % 2 ^ width := by
            rw [mod_two_pow_succ]
            simp [hbit, honesFalse]
          simp only [cubeCompletionsAux, hfixed, honesFalse, if_true]
          rwa [hmod]
      · have hfixedFalse : cube.fixed.testBit width = false := by
          cases hvalue : cube.fixed.testBit width <;> simp_all
        cases hbit : mask.testBit width with
        | false =>
            have hmod : mask % 2 ^ (width + 1) =
                mask % 2 ^ width := by
              rw [mod_two_pow_succ]
              simp [hbit]
            simp only [cubeCompletionsAux, hfixedFalse]
            apply List.mem_append.mpr
            left
            rwa [hmod]
        | true =>
            have hmod : mask % 2 ^ (width + 1) =
                mask % 2 ^ width + 2 ^ width := by
              rw [mod_two_pow_succ]
              simp [hbit, Nat.add_comm]
            simp only [cubeCompletionsAux, hfixedFalse]
            apply List.mem_append.mpr
            right
            exact List.mem_map.mpr
              ⟨mask % 2 ^ width, hlower, hmod.symm⟩

def cubeCompletions (cube : Cover6Cube) : List Nat :=
  cubeCompletionsAux cube 21

/-- Packed-mask correspondence to a cube.  This finite presentation is used
by the checker; `cubeMatchesMaskCheck_eq_true_iff` supplies the separate
literal-level proposition consumed by the DIMACS bridge. -/
def PackedCubeCompletion (cube : Cover6Cube) (mask : Nat) : Prop :=
  mask ∈ cubeCompletions cube

theorem cubeCompletionsAux_complete
    (cube : Cover6Cube) (width mask : Nat)
    (hmask : mask < 2 ^ width)
    (hmatch : ∀ position, position < width →
      cube.fixed.testBit position = true →
      mask.testBit position = cube.ones.testBit position) :
    mask ∈ cubeCompletionsAux cube width := by
  have hcompletion :=
    cubeCompletionsAux_complete_mod cube width mask hmatch
  rwa [Nat.mod_eq_of_lt hmask] at hcompletion

/-- Generic semantic-to-enumerator bridge.  `WellFormed` records the frozen
cube invariant expected by callers; completeness itself only needs the
21-bit mask bound and the fixed-bit equalities supplied by `CubeMatchesLocal`.
-/
theorem cubeMatchesLocal_is_completion
    (mask : Nat) (cube : Cover6Cube)
    (hmask : mask < 2 ^ 21)
    (_hwellFormed : cube.WellFormed)
    (hmatch : CubeMatchesLocal (maskLocalEdges mask) cube) :
    PackedCubeCompletion cube mask := by
  apply cubeCompletionsAux_complete cube 21 mask hmask
  intro position hposition hfixed
  exact cubeMatchesLocal_fixed_bit mask cube hmatch
    ⟨position, hposition⟩ hfixed

theorem representativeCube0_match_is_completion
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube0) :
    PackedCubeCompletion representativeCube0 mask :=
  cubeMatchesLocal_is_completion mask representativeCube0 hmask
    representativeCube0_wellFormed hmatch

theorem representativeCube1_match_is_completion
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube1) :
    PackedCubeCompletion representativeCube1 mask :=
  cubeMatchesLocal_is_completion mask representativeCube1 hmask
    representativeCube1_wellFormed hmatch

theorem representativeCube2_match_is_completion
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube2) :
    PackedCubeCompletion representativeCube2 mask :=
  cubeMatchesLocal_is_completion mask representativeCube2 hmask
    representativeCube2_wellFormed hmatch

theorem representativeCube3_match_is_completion
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube3) :
    PackedCubeCompletion representativeCube3 mask :=
  cubeMatchesLocal_is_completion mask representativeCube3 hmask
    representativeCube3_wellFormed hmatch

theorem representativeCube4_match_is_completion
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube4) :
    PackedCubeCompletion representativeCube4 mask :=
  cubeMatchesLocal_is_completion mask representativeCube4 hmask
    representativeCube4_wellFormed hmatch

theorem representativeCube5_match_is_completion
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube5) :
    PackedCubeCompletion representativeCube5 mask :=
  cubeMatchesLocal_is_completion mask representativeCube5 hmask
    representativeCube5_wellFormed hmatch

def admissibleCubeCompletions (cube : Cover6Cube) : List Nat :=
  (cubeCompletions cube).filter fun mask =>
    localR44Check (maskLocalEdges mask)

theorem representativeCube0_completion_count :
    (cubeCompletions representativeCube0).length = 64 := by
  native_decide

theorem representativeCube_completion_counts :
    representativeCubes.map (fun cube => (cubeCompletions cube).length) =
      [64, 64, 32, 32, 16, 16] := by
  native_decide

/-- The first 15-bit representative has exactly one locally R(4,4)-free
completion.  Only its 64 completions are inspected. -/
theorem representativeCube0_admissible_completions :
    admissibleCubeCompletions representativeCube0 = [0x12098B] := by
  native_decide

theorem representativeCube1_admissible_completions :
    admissibleCubeCompletions representativeCube1 = [0x3E6BE] := by
  native_decide

theorem representativeCube2_admissible_completions :
    admissibleCubeCompletions representativeCube2 = [0x386AE] := by
  native_decide

theorem representativeCube3_admissible_completions :
    admissibleCubeCompletions representativeCube3 = [0x49CF5] := by
  native_decide

theorem representativeCube4_admissible_completions :
    admissibleCubeCompletions representativeCube4 = [0x8897E] := by
  native_decide

theorem representativeCube5_admissible_completions :
    admissibleCubeCompletions representativeCube5 = [0x28EED] := by
  native_decide

private theorem unique_target_of_admissible_completions
    {cube : Cover6Cube} {target mask : Nat}
    (hchecked : admissibleCubeCompletions cube = [target])
    (hcompletion : PackedCubeCompletion cube mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = target := by
  have hfiltered : mask ∈ admissibleCubeCompletions cube :=
    List.mem_filter.mpr ⟨hcompletion, hadmissible⟩
  rw [hchecked] at hfiltered
  simpa using hfiltered

/-- Proposition-level uniqueness: packed correspondence plus local R44
admissibility forces the concrete target mask. -/
theorem representativeCube0_unique_target
    (mask : Nat)
    (hcompletion : PackedCubeCompletion representativeCube0 mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x12098B := by
  have hfiltered :
      mask ∈ admissibleCubeCompletions representativeCube0 := by
    exact List.mem_filter.mpr ⟨hcompletion, hadmissible⟩
  rw [representativeCube0_admissible_completions] at hfiltered
  simpa using hfiltered

theorem representativeCube1_unique_target
    (mask : Nat)
    (hcompletion : PackedCubeCompletion representativeCube1 mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x3E6BE :=
  unique_target_of_admissible_completions
    representativeCube1_admissible_completions hcompletion hadmissible

theorem representativeCube2_unique_target
    (mask : Nat)
    (hcompletion : PackedCubeCompletion representativeCube2 mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x386AE :=
  unique_target_of_admissible_completions
    representativeCube2_admissible_completions hcompletion hadmissible

theorem representativeCube3_unique_target
    (mask : Nat)
    (hcompletion : PackedCubeCompletion representativeCube3 mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x49CF5 :=
  unique_target_of_admissible_completions
    representativeCube3_admissible_completions hcompletion hadmissible

theorem representativeCube4_unique_target
    (mask : Nat)
    (hcompletion : PackedCubeCompletion representativeCube4 mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x8897E :=
  unique_target_of_admissible_completions
    representativeCube4_admissible_completions hcompletion hadmissible

theorem representativeCube5_unique_target
    (mask : Nat)
    (hcompletion : PackedCubeCompletion representativeCube5 mask)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x28EED :=
  unique_target_of_admissible_completions
    representativeCube5_admissible_completions hcompletion hadmissible

/-- Direct proposition-level endpoint from the semantic cube interface:
boundedness, cube matching, and local R(4,4) admissibility force the unique
target completion. -/
theorem representativeCube0_match_r44_unique
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube0)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x12098B := by
  exact representativeCube0_unique_target mask
    (representativeCube0_match_is_completion mask hmask hmatch)
    hadmissible

theorem representativeCube1_match_r44_unique
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube1)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x3E6BE := by
  exact representativeCube1_unique_target mask
    (representativeCube1_match_is_completion mask hmask hmatch)
    hadmissible

theorem representativeCube2_match_r44_unique
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube2)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x386AE := by
  exact representativeCube2_unique_target mask
    (representativeCube2_match_is_completion mask hmask hmatch)
    hadmissible

theorem representativeCube3_match_r44_unique
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube3)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x49CF5 := by
  exact representativeCube3_unique_target mask
    (representativeCube3_match_is_completion mask hmask hmatch)
    hadmissible

theorem representativeCube4_match_r44_unique
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube4)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x8897E := by
  exact representativeCube4_unique_target mask
    (representativeCube4_match_is_completion mask hmask hmatch)
    hadmissible

theorem representativeCube5_match_r44_unique
    (mask : Nat)
    (hmask : mask < 2 ^ 21)
    (hmatch : CubeMatchesLocal
      (maskLocalEdges mask) representativeCube5)
    (hadmissible : LocalR44Admissible (maskLocalEdges mask)) :
    mask = 0x28EED := by
  exact representativeCube5_unique_target mask
    (representativeCube5_match_is_completion mask hmask hmatch)
    hadmissible

/-! ## Target-to-motif relabeling -/

def permutedMotifMask (motif : Graph) (permutation : List Nat) : Nat :=
  motifUpperPairs.foldl (fun mask pair =>
    if edge motif
        (permutation.getD pair.1.val 7)
        (permutation.getD pair.2.val 7) then
      mask + 2 ^ graph6EdgePosition pair.1.val pair.2.val
    else mask) 0

/-- Direction audit for the first witness: the permutation maps each target
label to the corresponding raw `FG`Xo` motif label. -/
theorem representativeTarget0_eq_permuted_motif :
    permutedMotifMask motifFGBacktickXo [4, 5, 6, 0, 3, 1, 2] =
      0x12098B := by
  native_decide

theorem representativeTarget1_eq_permuted_motif :
    permutedMotifMask motifFdWBraceW [3, 4, 5, 6, 1, 0, 2] =
      0x3E6BE := by
  native_decide

theorem representativeTarget2_eq_permuted_motif :
    permutedMotifMask motifFIIXw [5, 2, 6, 3, 1, 0, 4] =
      0x386AE := by
  native_decide

theorem representativeTarget3_eq_permuted_motif :
    permutedMotifMask motifFHFLw [5, 6, 3, 2, 0, 4, 1] =
      0x49CF5 := by
  native_decide

theorem representativeTarget4_eq_permuted_motif :
    permutedMotifMask motifFKDhw [5, 3, 6, 4, 2, 0, 1] =
      0x8897E := by
  native_decide

theorem representativeTarget5_eq_permuted_motif :
    permutedMotifMask motifFAtHCaretG [6, 5, 4, 2, 3, 1, 0] =
      0x28EED := by
  native_decide

#print axioms localR44Admissible_iff
#print axioms cubeCompletionsAux_complete
#print axioms cubeMatchesLocal_is_completion
#print axioms representativeCube0_match_is_completion
#print axioms representativeCube0_unique_target
#print axioms representativeCube0_match_r44_unique
#print axioms representativeTarget0_eq_permuted_motif
#print axioms representativeCube5_match_r44_unique
#print axioms representativeTarget5_eq_permuted_motif

end LRATCatcher.Tests.R44Cover6RepresentativeCubes
