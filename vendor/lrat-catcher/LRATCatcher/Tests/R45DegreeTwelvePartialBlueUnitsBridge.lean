import LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation
import LRATCatcher.Tests.R45DegreeTwelveCatalogueUnitsBridge

/-!
  # Partial blue-block unit semantics for the degree-twelve branch

  A partial pattern assigns `hole`, `color1`, or `color2` to each of the 66
  local edges of the twelve-vertex blue-neighbour block.  Holes emit no unit.
  Two archive conventions occur in the project, so orientation is a required
  parameter rather than an implicit convention:

  * raw HOL: `color1 = blue = false`, `color2 = red = true`;
  * complemented B (the degree-eight architecture): `color1 = true`,
    `color2 = false`.

  The emitted variables are exactly DIMACS variables 211 through 276, i.e.
  the edges among reduced vertices `12, ..., 23`.  This module is generic in
  the pattern and contains no concrete consensus-cover data.
-/

namespace LRATCatcher.Tests.R45DegreeTwelvePartialBlueUnitsBridge

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45RootDegreeCore
open LRATCatcher.Tests.R45DegreeTwelveBridge
open LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation
open LRATCatcher.Tests.R45DegreeTwelveCatalogueUnitsBridge
open LRATCatcher.Tests.R45DegreeEightPilotSemantics

/-! ## Generic ternary patterns and their direct units -/

/-- A ternary archive symbol.  The names `color1` and `color2` deliberately
preserve the source data vocabulary; their Boolean meaning is supplied only
by an explicit `BluePatternOrientation`. -/
inductive PartialBlueColour where
  | hole
  | color1
  | color2
  deriving DecidableEq, Repr

/-- The two color conventions used by the existing certificates. -/
inductive BluePatternOrientation where
  /-- Raw HOL convention: `color1 = blue = false`, `color2 = red = true`. -/
  | rawHOL
  /-- Complemented-B convention: `color1 = true`, `color2 = false`. -/
  | complementedB
  deriving DecidableEq, Repr

/-- Required SAT/Lean Boolean value under an explicit archive orientation. -/
def PartialBlueColour.requiredValue :
    PartialBlueColour → BluePatternOrientation → Option Bool
  | .hole, _ => none
  | .color1, .rawHOL => some false
  | .color2, .rawHOL => some true
  | .color1, .complementedB => some true
  | .color2, .complementedB => some false

@[simp] theorem requiredValue_hole (orientation : BluePatternOrientation) :
    PartialBlueColour.hole.requiredValue orientation = none := rfl

@[simp] theorem requiredValue_rawHOL_color1 :
    PartialBlueColour.color1.requiredValue .rawHOL = some false := rfl

@[simp] theorem requiredValue_rawHOL_color2 :
    PartialBlueColour.color2.requiredValue .rawHOL = some true := rfl

@[simp] theorem requiredValue_complementedB_color1 :
    PartialBlueColour.color1.requiredValue .complementedB = some true := rfl

@[simp] theorem requiredValue_complementedB_color2 :
    PartialBlueColour.color2.requiredValue .complementedB = some false := rfl

/-- A partial pattern indexed by the local zero-based `edgeVar 12` index. -/
abbrev PartialBluePattern := Nat → PartialBlueColour

/-- One optional unit for a local pair.  The shift by twelve places the pair
inside the blue-neighbour block of the reduced `K_24`.  Orientation is never
inferred from the archive digits. -/
def partialBlueUnit (orientation : BluePatternOrientation)
    (pattern : PartialBluePattern) (pair : Nat × Nat) : Option Int :=
  match (pattern (edgeVar 12 pair.1 pair.2)).requiredValue orientation with
  | none => none
  | some value => some (edgeUnit (pair.1 + 12) (pair.2 + 12) value)

/-- All fixed literals of an oriented partial pattern, in Python
upper-triangle order. -/
def partialBlueUnits (orientation : BluePatternOrientation)
    (pattern : PartialBluePattern) : List Int :=
  (upperPairs 12).filterMap (partialBlueUnit orientation pattern)

/-- Units under the raw HOL archive convention. -/
abbrev rawHOLPartialBlueUnits (pattern : PartialBluePattern) : List Int :=
  partialBlueUnits .rawHOL pattern

/-- Units under the complemented-B convention used by the degree-eight
architecture. -/
abbrev complementedBPartialBlueUnits
    (pattern : PartialBluePattern) : List Int :=
  partialBlueUnits .complementedB pattern

/-- Under raw HOL, `color1` is blue/false and hence a negative literal. -/
theorem partialBlueUnit_rawHOL_color1_negative
    (pattern : PartialBluePattern) (pair : Nat × Nat)
    (hcolor : pattern (edgeVar 12 pair.1 pair.2) = .color1) :
    partialBlueUnit .rawHOL pattern pair =
      some (-Int.ofNat (edgeVar 24 (pair.1 + 12) (pair.2 + 12) + 1)) := by
  simp [partialBlueUnit, hcolor, edgeUnit]

/-- Under raw HOL, `color2` is red/true and hence a positive literal. -/
theorem partialBlueUnit_rawHOL_color2_positive
    (pattern : PartialBluePattern) (pair : Nat × Nat)
    (hcolor : pattern (edgeVar 12 pair.1 pair.2) = .color2) :
    partialBlueUnit .rawHOL pattern pair =
      some (Int.ofNat (edgeVar 24 (pair.1 + 12) (pair.2 + 12) + 1)) := by
  simp [partialBlueUnit, hcolor, edgeUnit]

/-- Under complemented B, `color1` is true and hence a positive literal. -/
theorem partialBlueUnit_complementedB_color1_positive
    (pattern : PartialBluePattern) (pair : Nat × Nat)
    (hcolor : pattern (edgeVar 12 pair.1 pair.2) = .color1) :
    partialBlueUnit .complementedB pattern pair =
      some (Int.ofNat (edgeVar 24 (pair.1 + 12) (pair.2 + 12) + 1)) := by
  simp [partialBlueUnit, hcolor, edgeUnit]

/-- Under complemented B, `color2` is false and hence a negative literal. -/
theorem partialBlueUnit_complementedB_color2_negative
    (pattern : PartialBluePattern) (pair : Nat × Nat)
    (hcolor : pattern (edgeVar 12 pair.1 pair.2) = .color2) :
    partialBlueUnit .complementedB pattern pair =
      some (-Int.ofNat (edgeVar 24 (pair.1 + 12) (pair.2 + 12) + 1)) := by
  simp [partialBlueUnit, hcolor, edgeUnit]

/-- A hole emits no literal under either orientation. -/
theorem partialBlueUnit_hole
    (orientation : BluePatternOrientation)
    (pattern : PartialBluePattern) (pair : Nat × Nat)
    (hhole : pattern (edgeVar 12 pair.1 pair.2) = .hole) :
    partialBlueUnit orientation pattern pair = none := by
  simp [partialBlueUnit, hhole]
/-- The one-based DIMACS variable of every shifted local edge lies in the
closed interval 211..276. -/
theorem blueBlock_dimacsVariable_range
    (left right : Fin 12) (hordered : left < right) :
    211 ≤ edgeVar 24 (left.val + 12) (right.val + 12) + 1 ∧
      edgeVar 24 (left.val + 12) (right.val + 12) + 1 ≤ 276 := by
  native_decide +revert

/-! ## Semantic match under a local permutation -/

/-- A target-to-source permutation witnessing that every non-hole archive
symbol has the Boolean value dictated by the explicit orientation. -/
structure PartialBluePatternMatch
    (orientation : BluePatternOrientation)
    (rawColoring : Nat → Bool) (pattern : PartialBluePattern) where
  permutation : FinPermutation 12
  fixed_edge : ∀ left right : Fin 12, left < right → ∀ value : Bool,
    (pattern (edgeVar 12 left.val right.val)).requiredValue orientation =
        some value →
      coloringEdge 12 rawColoring
          (permutation left).val (permutation right).val = value

/-- A semantic match using the raw HOL (`color1 = false`) convention. -/
abbrev RawHOLPartialBluePatternMatch
    (rawColoring : Nat → Bool) (pattern : PartialBluePattern) :=
  PartialBluePatternMatch .rawHOL rawColoring pattern

/-- A semantic match using the complemented-B (`color1 = true`) convention. -/
abbrev ComplementedBPartialBluePatternMatch
    (rawColoring : Nat → Bool) (pattern : PartialBluePattern) :=
  PartialBluePatternMatch .complementedB rawColoring pattern

namespace PartialBluePatternMatch

/-- Literal-level semantics of an arbitrary oriented partial pattern.  This
single theorem audits the `+12` block shift, the zero-based/DIMACS-one-based
conversion, and the orientation-selected literal polarity. -/
theorem allUnitsSatisfied
    {orientation : BluePatternOrientation}
    {rawColoring : Nat → Bool} {pattern : PartialBluePattern}
    (witness : PartialBluePatternMatch orientation rawColoring pattern)
    (assignment : Nat → Bool)
    (hassignment : ∀ left right : Fin 12, left < right →
      assignment (edgeVar 24 (left.val + 12) (right.val + 12)) =
        coloringEdge 12 rawColoring
          (witness.permutation left).val
          (witness.permutation right).val) :
    AllUnitsSatisfied assignment (partialBlueUnits orientation pattern) := by
  intro literal hliteral
  simp only [partialBlueUnits, List.mem_filterMap] at hliteral
  obtain ⟨pair, hpair, hunit⟩ := hliteral
  obtain ⟨horderedNat, hright⟩ := upperPairs_twelve_ordered pair hpair
  let left : Fin 12 := ⟨pair.1, by omega⟩
  let right : Fin 12 := ⟨pair.2, hright⟩
  have hordered : left < right := by
    simpa [left, right] using horderedNat
  cases hrequired :
      (pattern (edgeVar 12 pair.1 pair.2)).requiredValue orientation with
  | none =>
      simp [partialBlueUnit, hrequired] at hunit
  | some value =>
      have hequal :
          edgeUnit (pair.1 + 12) (pair.2 + 12) value = literal := by
        apply Option.some.inj
        simpa only [partialBlueUnit, hrequired] using hunit
      have hfixed :
          (pattern (edgeVar 12 left.val right.val)).requiredValue orientation =
            some value := by
        simpa only [left, right] using hrequired
      rw [← hequal]
      apply (edgeUnit_satisfied_iff assignment
        (pair.1 + 12) (pair.2 + 12) value).2
      calc
        assignment (edgeVar 24 (pair.1 + 12) (pair.2 + 12)) =
            coloringEdge 12 rawColoring
              (witness.permutation left).val
              (witness.permutation right).val := by
          simpa [left, right] using hassignment left right hordered
        _ = value := witness.fixed_edge left right hordered value hfixed

end PartialBluePatternMatch

/-! ## The actual degree-twelve blue block -/

/-- The globally relabeled reduced assignment reads the raw blue-neighbour
colouring through the selected local blue permutation. -/
theorem reducedAssignment_global_blue
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation bluePermutation : FinPermutation 12)
    (left right : Fin 12) (hordered : left < right) :
    reducedAssignment
        (degreeTwelveGlobalPermutation coloring root hroot hdegree
          redPermutation bluePermutation) coloring
        (edgeVar 24 (left.val + 12) (right.val + 12)) =
      coloringEdge 12
        (blueDegreeTwelveRawColoring coloring root hroot hdegree)
        (bluePermutation left).val (bluePermutation right).val := by
  let global := degreeTwelveGlobalPermutation coloring root hroot hdegree
    redPermutation bluePermutation
  let left24 : Fin 24 := ⟨left.val + 12, by omega⟩
  let right24 : Fin 24 := ⟨right.val + 12, by omega⟩
  have hordered24 : left24 < right24 := by
    simpa [left24, right24] using hordered
  have hne : bluePermutation left ≠ bluePermutation right := by
    intro hequal
    exact (by
      have := FinPermutation.injective bluePermutation hequal
      omega)
  calc
    reducedAssignment global coloring
        (edgeVar 24 (left.val + 12) (right.val + 12)) =
        LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
          (permutedNonRootEmbedding global left24).val
          (permutedNonRootEmbedding global right24).val := by
      simpa [left24, right24] using
        reducedAssignment_edgeVar global coloring left24 right24 hordered24
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 25 coloring
        (blueDegreeTwelveEmbedding coloring root hroot hdegree
          (bluePermutation left)).val
        (blueDegreeTwelveEmbedding coloring root hroot hdegree
          (bluePermutation right)).val := by
      simp [global, permutedNonRootEmbedding, canonicalNonRootVertex,
        left24, right24]
    _ = LRATCatcher.Tests.R55DegreeBounds.ramseyEdge 12
        (blueDegreeTwelveRawColoring coloring root hroot hdegree)
          (bluePermutation left).val (bluePermutation right).val := by
      symm
      simpa [blueDegreeTwelveRawColoring] using
        ramseyEdge_inducedColoring
          (blueDegreeTwelveEmbedding coloring root hroot hdegree)
          coloring false localEdgePair_edgeVar_twelve
          (bluePermutation left) (bluePermutation right) hne
    _ = coloringEdge 12
        (blueDegreeTwelveRawColoring coloring root hroot hdegree)
          (bluePermutation left).val (bluePermutation right).val := by rfl

/-- End-to-end reusable bridge for a partial blue-block motif under an
explicit orientation.  A semantic match supplies the local blue permutation;
the same permutation is installed in the ambient `Fin 25` relabeling. -/
theorem bluePatternMatch_global_allUnitsSatisfied
    {orientation : BluePatternOrientation}
    {coloring : Nat → Bool} {pattern : PartialBluePattern}
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation : FinPermutation 12)
    (witness : PartialBluePatternMatch orientation
      (blueDegreeTwelveRawColoring coloring root hroot hdegree) pattern) :
    AllUnitsSatisfied
      (reducedAssignment
        (degreeTwelveGlobalPermutation coloring root hroot hdegree
          redPermutation witness.permutation) coloring)
      (partialBlueUnits orientation pattern) := by
  apply witness.allUnitsSatisfied
  intro left right hordered
  exact reducedAssignment_global_blue coloring root hroot hdegree
    redPermutation witness.permutation left right hordered

/-- Explicit raw-HOL corollary: `color1 = blue = false` and
`color2 = red = true`. -/
theorem rawHOLBluePatternMatch_global_allUnitsSatisfied
    {coloring : Nat → Bool} {pattern : PartialBluePattern}
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation : FinPermutation 12)
    (witness : RawHOLPartialBluePatternMatch
      (blueDegreeTwelveRawColoring coloring root hroot hdegree) pattern) :
    AllUnitsSatisfied
      (reducedAssignment
        (degreeTwelveGlobalPermutation coloring root hroot hdegree
          redPermutation witness.permutation) coloring)
      (rawHOLPartialBlueUnits pattern) :=
  bluePatternMatch_global_allUnitsSatisfied
    (orientation := .rawHOL) root hroot hdegree redPermutation witness

/-- Explicit complemented-B corollary: `color1 = true` and
`color2 = false`, matching the degree-eight architecture. -/
theorem complementedBBluePatternMatch_global_allUnitsSatisfied
    {coloring : Nat → Bool} {pattern : PartialBluePattern}
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (redPermutation : FinPermutation 12)
    (witness : ComplementedBPartialBluePatternMatch
      (blueDegreeTwelveRawColoring coloring root hroot hdegree) pattern) :
    AllUnitsSatisfied
      (reducedAssignment
        (degreeTwelveGlobalPermutation coloring root hroot hdegree
          redPermutation witness.permutation) coloring)
      (complementedBPartialBlueUnits pattern) :=
  bluePatternMatch_global_allUnitsSatisfied
    (orientation := .complementedB) root hroot hdegree redPermutation witness

#print axioms partialBlueUnit_rawHOL_color1_negative
#print axioms partialBlueUnit_rawHOL_color2_positive
#print axioms partialBlueUnit_complementedB_color1_positive
#print axioms partialBlueUnit_complementedB_color2_negative
#print axioms blueBlock_dimacsVariable_range
#print axioms PartialBluePatternMatch.allUnitsSatisfied
#print axioms reducedAssignment_global_blue
#print axioms bluePatternMatch_global_allUnitsSatisfied
#print axioms rawHOLBluePatternMatch_global_allUnitsSatisfied
#print axioms complementedBBluePatternMatch_global_allUnitsSatisfied
end LRATCatcher.Tests.R45DegreeTwelvePartialBlueUnitsBridge
