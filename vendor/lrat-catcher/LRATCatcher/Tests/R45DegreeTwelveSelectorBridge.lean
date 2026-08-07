import LRATCatcher.Tests.R45DegreeTwelveBridge

/-!
  # Four-bit selector bridge for the red-degree-twelve branch

  The generated guarded master uses DIMACS variables `277, ..., 280` as a
  four-bit little-endian code.  Since `Std.Sat.CNF` variables are zero based,
  these are Lean variables `276, ..., 279`.  Codes `0, ..., 11` select the
  twelve order-12 `R(3,5)` catalogue representatives in list order.  Codes
  `12, ..., 15` are excluded together by `not (bit 2 and bit 3)`.

  This module proves the selector/catalogue correspondence and turns the
  semantic degree-twelve classification into a valid selector case.  It does
  not identify this Lean data with a parsed DIMACS file and contains no LRAT
  claim.
-/

namespace LRATCatcher.Tests.R45DegreeTwelveSelectorBridge

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45DegreeTwelveBridge

/-! ## Exact four-bit codec used by the Python generator -/

/-- First selector variable in zero-based Lean numbering.  This is DIMACS
variable 277. -/
abbrev selectorStart : Nat := 276

abbrev selectorWidth : Nat := 4
abbrev selectorCodeCount : Nat := 16
abbrev catalogueCodeCount : Nat := 12

theorem selectorCodeCardinality :
    2 ^ selectorWidth = selectorCodeCount := by
  native_decide

/-- The little-endian bit vector of a natural-number selector code. -/
def selectorCodeBits (code : Nat) : Fin selectorWidth → Bool :=
  fun bit => code.testBit bit.val

/-- Read the four selector bits from an arbitrary SAT assignment. -/
def decodeSelectorBits (assignment : Nat → Bool) :
    Fin selectorWidth → Bool :=
  fun bit => assignment (selectorStart + bit.val)

/-- Preserve the order-24 edge variables while writing one little-endian
selector code into Lean variables 276 through 279. -/
def extendWithDegreeTwelveCode (assignment : Nat → Bool)
    (code varIndex : Nat) : Bool :=
  if varIndex < selectorStart then
    assignment varIndex
  else if varIndex < selectorStart + selectorWidth then
    code.testBit (varIndex - selectorStart)
  else
    assignment varIndex

@[simp] theorem extendWithDegreeTwelveCode_of_lt
    (assignment : Nat → Bool) (code varIndex : Nat)
    (hvarIndex : varIndex < selectorStart) :
    extendWithDegreeTwelveCode assignment code varIndex =
      assignment varIndex := by
  simp [extendWithDegreeTwelveCode, hvarIndex]

@[simp] theorem extendWithDegreeTwelveCode_selectorBit
    (assignment : Nat → Bool) (code : Nat) (bit : Fin selectorWidth) :
    extendWithDegreeTwelveCode assignment code
        (selectorStart + bit.val) =
      code.testBit bit.val := by
  have hnotBefore : ¬ selectorStart + bit.val < selectorStart := by omega
  have hinSelector :
      selectorStart + bit.val < selectorStart + selectorWidth := by omega
  unfold extendWithDegreeTwelveCode
  rw [if_neg hnotBefore, if_pos hinSelector]
  simp

/-- Encoding followed by four-bit decoding recovers exactly the
little-endian code bits. -/
@[simp] theorem decodeSelectorBits_extendWithDegreeTwelveCode
    (assignment : Nat → Bool) (code : Nat) :
    decodeSelectorBits (extendWithDegreeTwelveCode assignment code) =
      selectorCodeBits code := by
  funext bit
  exact extendWithDegreeTwelveCode_selectorBit assignment code bit

/-- Within the four-bit range, the selector bit vector determines the code
uniquely. -/
theorem selectorCodeBits_injective_below_sixteen
    {left right : Nat}
    (hleft : left < selectorCodeCount)
    (hright : right < selectorCodeCount)
    (hbits : selectorCodeBits left = selectorCodeBits right) :
    left = right := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < selectorWidth
  · have hvalue := congrFun hbits (⟨bit, hbit⟩ : Fin selectorWidth)
    simpa [selectorCodeBits] using hvalue
  · have hpow : 2 ^ selectorWidth ≤ 2 ^ bit :=
      Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    have hleftPow : left < 2 ^ bit := by
      rw [selectorCodeCardinality] at hpow
      exact Nat.lt_of_lt_of_le hleft hpow
    have hrightPow : right < 2 ^ bit := by
      rw [selectorCodeCardinality] at hpow
      exact Nat.lt_of_lt_of_le hright hpow
    rw [Nat.testBit_lt_two_pow hleftPow,
      Nat.testBit_lt_two_pow hrightPow]

/-! ## Guards and the common invalid-code blocker -/

/-- This literal is true precisely when the selected bit differs from the
corresponding bit of `code`. -/
def selectorMismatchLiteral (code bit : Nat) : Nat × Bool :=
  (selectorStart + bit, !(code.testBit bit))

/-- Negation of the complete four-bit equality test for `code`. -/
def selectorMismatchClause (code : Nat) : CNF.Clause Nat :=
  (List.range selectorWidth).map (selectorMismatchLiteral code)

/-- The Lean form of DIMACS clause `-279 -280 0`, which excludes exactly
codes 12 through 15. -/
def invalidSelectorCodeClause : CNF.Clause Nat :=
  [(selectorStart + 2, false), (selectorStart + 3, false)]

theorem selectorMismatchClause_selected_false
    (assignment : Nat → Bool) (code : Nat) :
    CNF.Clause.eval (extendWithDegreeTwelveCode assignment code)
      (selectorMismatchClause code) = false := by
  rw [CNF.Clause.eval, List.any_eq_false]
  intro literal hliteral
  simp only [selectorMismatchClause, List.mem_map] at hliteral
  obtain ⟨bit, hbit, rfl⟩ := hliteral
  have hbitLt : bit < selectorWidth := List.mem_range.mp hbit
  simp only [selectorMismatchLiteral]
  change ¬
    (extendWithDegreeTwelveCode assignment code (selectorStart + bit) ==
      !(code.testBit bit)) = true
  rw [extendWithDegreeTwelveCode_selectorBit assignment code
    (⟨bit, hbitLt⟩ : Fin selectorWidth)]
  cases code.testBit bit <;> decide

private theorem exists_selectorBit_ne
    {left right : Nat}
    (hleft : left < selectorCodeCount)
    (hright : right < selectorCodeCount)
    (hne : left ≠ right) :
    ∃ bit : Fin selectorWidth,
      left.testBit bit.val ≠ right.testBit bit.val := by
  by_cases hwitness :
      ∃ bit : Fin selectorWidth,
        left.testBit bit.val ≠ right.testBit bit.val
  · exact hwitness
  · exfalso
    apply hne
    apply selectorCodeBits_injective_below_sixteen hleft hright
    funext bit
    by_cases hbit : left.testBit bit.val = right.testBit bit.val
    · exact hbit
    · exact False.elim (hwitness ⟨bit, hbit⟩)

theorem selectorMismatchClause_other_true
    (assignment : Nat → Bool) {selected other : Nat}
    (hselected : selected < selectorCodeCount)
    (hother : other < selectorCodeCount)
    (hne : selected ≠ other) :
    CNF.Clause.eval (extendWithDegreeTwelveCode assignment selected)
      (selectorMismatchClause other) = true := by
  obtain ⟨bit, hbit⟩ :=
    exists_selectorBit_ne hselected hother hne
  rw [CNF.Clause.eval, List.any_eq_true]
  refine ⟨selectorMismatchLiteral other bit.val, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨bit.val, List.mem_range.mpr bit.isLt, rfl⟩
  · unfold selectorMismatchLiteral
    change
      (extendWithDegreeTwelveCode assignment selected
          (selectorStart + bit.val) ==
        !(other.testBit bit.val)) = true
    rw [extendWithDegreeTwelveCode_selectorBit assignment selected bit]
    cases hselectedBit : selected.testBit bit.val <;>
      cases hotherBit : other.testBit bit.val <;>
      simp_all

theorem invalidSelectorCodeClause_valid_true
    (assignment : Nat → Bool) {code : Nat} (hcode : code < 12) :
    CNF.Clause.eval (extendWithDegreeTwelveCode assignment code)
      invalidSelectorCodeClause = true := by
  simp only [invalidSelectorCodeClause, CNF.Clause.eval, List.any_cons,
    List.any_nil, Bool.or_false]
  rw [extendWithDegreeTwelveCode_selectorBit assignment code
      (⟨2, by native_decide⟩ : Fin selectorWidth),
    extendWithDegreeTwelveCode_selectorBit assignment code
      (⟨3, by native_decide⟩ : Fin selectorWidth)]
  native_decide +revert

theorem invalidSelectorCodeClause_invalid_false
    (assignment : Nat → Bool) {code : Nat}
    (hlower : 12 ≤ code) (hupper : code < selectorCodeCount) :
    CNF.Clause.eval (extendWithDegreeTwelveCode assignment code)
      invalidSelectorCodeClause = false := by
  simp only [invalidSelectorCodeClause, CNF.Clause.eval, List.any_cons,
    List.any_nil, Bool.or_false]
  rw [extendWithDegreeTwelveCode_selectorBit assignment code
      (⟨2, by native_decide⟩ : Fin selectorWidth),
    extendWithDegreeTwelveCode_selectorBit assignment code
      (⟨3, by native_decide⟩ : Fin selectorWidth)]
  have hcases : code = 12 ∨ code = 13 ∨ code = 14 ∨ code = 15 := by
    change code < 16 at hupper
    omega
  rcases hcases with rfl | rfl | rfl | rfl <;> native_decide

/-! ## Catalogue correspondence -/

/-- Packed adjacency rows obtained by decoding the twelve records of
`r35_12.g6` in file order.  Keeping this small constant here makes the
selector-to-row ordering inspectable on the Lean side. -/
def decodedR35OrderTwelveRows : List Graph := [
  [1344, 2688, 2848, 1808, 2152, 1172, 657, 354, 141, 78, 2089, 1046],
  [3136, 896, 1360, 2656, 2692, 1416, 141, 114, 2086, 1050, 549, 281],
  [784, 2624, 3200, 1312, 1121, 2200, 402, 612, 2121, 1155, 540, 294],
  [2592, 1600, 2184, 1284, 3456, 1217, 2338, 564, 600, 387, 58, 85],
  [276, 552, 2177, 1090, 577, 386, 2200, 1124, 3105, 3090, 904, 836],
  [1090, 2305, 2568, 1156, 3712, 3392, 673, 344, 674, 340, 57, 54],
  [2066, 1057, 328, 644, 577, 386, 1172, 2152, 2596, 1304, 2626, 1409],
  [50, 193, 3080, 772, 3585, 2433, 2818, 1570, 1128, 216, 404, 116],
  [50, 193, 2312, 1540, 1409, 2625, 1314, 2578, 596, 424, 2136, 1188],
  [262, 2113, 1153, 400, 2088, 592, 1058, 524, 1545, 2464, 2372, 1554],
  [30, 3201, 2817, 705, 1313, 2704, 3336, 298, 212, 1068, 594, 102],
  [30, 3201, 2625, 2817, 1313, 2256, 1316, 802, 216, 1164, 594, 46]
]

/-- The concrete row list above is exactly Lean's certified order-12
catalogue, including ordering. -/
theorem decodedR35OrderTwelveRows_eq_catalogue :
    decodedR35OrderTwelveRows = catalogues.getD 12 [] := by
  native_decide

theorem decodedR35OrderTwelveRows_length :
    decodedR35OrderTwelveRows.length = catalogueCodeCount := by
  native_decide

/-- The catalogue representative selected by a numeric code. -/
def catalogueRepresentative (code : Nat) : Graph :=
  (catalogues.getD 12 []).getD code []

theorem catalogueRepresentative_eq_getD (code : Nat) :
    catalogueRepresentative code =
      (catalogues.getD 12 []).getD code [] := rfl

theorem catalogueRepresentative_eq_decodedRow (code : Nat) :
    catalogueRepresentative code =
      decodedR35OrderTwelveRows.getD code [] := by
  rw [decodedR35OrderTwelveRows_eq_catalogue]
  rfl

/-- A semantic case carried by one of the twelve valid four-bit codes. -/
structure GuardedCatalogueCase (graph : Graph) where
  code : Nat
  valid : code < catalogueCodeCount
  isomorphic : GraphIsomorphicFin graph (catalogueRepresentative code)

namespace GuardedCatalogueCase

theorem code_below_selectorRange {graph : Graph}
    (guardedCase : GuardedCatalogueCase graph) :
    guardedCase.code < selectorCodeCount := by
  change guardedCase.code < 16
  have hvalid : guardedCase.code < 12 := by
    simpa [catalogueCodeCount] using guardedCase.valid
  omega

theorem selected_guard_false {graph : Graph}
    (guardedCase : GuardedCatalogueCase graph)
    (assignment : Nat → Bool) :
    CNF.Clause.eval
        (extendWithDegreeTwelveCode assignment guardedCase.code)
        (selectorMismatchClause guardedCase.code) = false := by
  exact selectorMismatchClause_selected_false assignment guardedCase.code

theorem other_guard_true {graph : Graph}
    (guardedCase : GuardedCatalogueCase graph)
    (assignment : Nat → Bool) {other : Nat}
    (hother : other < selectorCodeCount)
    (hne : guardedCase.code ≠ other) :
    CNF.Clause.eval
        (extendWithDegreeTwelveCode assignment guardedCase.code)
        (selectorMismatchClause other) = true := by
  exact selectorMismatchClause_other_true assignment
    guardedCase.code_below_selectorRange hother hne

theorem invalid_blocker_true {graph : Graph}
    (guardedCase : GuardedCatalogueCase graph)
    (assignment : Nat → Bool) :
    CNF.Clause.eval
        (extendWithDegreeTwelveCode assignment guardedCase.code)
        invalidSelectorCodeClause = true := by
  exact invalidSelectorCodeClause_valid_true assignment guardedCase.valid

end GuardedCatalogueCase

/-- Every Ramsey-free rooted coloring of exact red degree twelve selects one
of the twelve valid guarded-master codes, in exactly the catalogue order used
by `R45DegreeTwelveBridge`. -/
theorem red_degree_twelve_enters_guarded_catalogue_case
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Nonempty
      (GuardedCatalogueCase
        (redDegreeTwelveGraph coloring root hdegree)) := by
  obtain ⟨code, hcode, hisomorphic⟩ :=
    red_degree_twelve_enters_one_of_twelve_types
      hfree root hroot hdegree
  exact ⟨{
    code := code
    valid := hcode
    isomorphic := by
      simpa [catalogueRepresentative] using hisomorphic
  }⟩

/-- Fully exposed form convenient for the next guarded-master semantics
module: the chosen code has the exact little-endian selector bits, satisfies
the common blocker, and names an isomorphic catalogue representative. -/
theorem red_degree_twelve_enters_encoded_selector_case
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (assignment : Nat → Bool) :
    ∃ code, code < 12 ∧
      decodeSelectorBits
          (extendWithDegreeTwelveCode assignment code) =
        selectorCodeBits code ∧
      CNF.Clause.eval
          (extendWithDegreeTwelveCode assignment code)
          invalidSelectorCodeClause = true ∧
      GraphIsomorphicFin
        (redDegreeTwelveGraph coloring root hdegree)
        (catalogueRepresentative code) := by
  obtain ⟨guardedCase⟩ :=
    red_degree_twelve_enters_guarded_catalogue_case
      hfree root hroot hdegree
  exact ⟨guardedCase.code, guardedCase.valid,
    decodeSelectorBits_extendWithDegreeTwelveCode assignment guardedCase.code,
    guardedCase.invalid_blocker_true assignment,
    guardedCase.isomorphic⟩

theorem valid_selector_code_count :
    (List.range catalogueCodeCount).length = 12 := by
  native_decide

#print axioms selectorCodeBits_injective_below_sixteen
#print axioms selectorMismatchClause_other_true
#print axioms invalidSelectorCodeClause_valid_true
#print axioms invalidSelectorCodeClause_invalid_false
#print axioms decodedR35OrderTwelveRows_eq_catalogue
#print axioms red_degree_twelve_enters_guarded_catalogue_case
#print axioms red_degree_twelve_enters_encoded_selector_case

end LRATCatcher.Tests.R45DegreeTwelveSelectorBridge
