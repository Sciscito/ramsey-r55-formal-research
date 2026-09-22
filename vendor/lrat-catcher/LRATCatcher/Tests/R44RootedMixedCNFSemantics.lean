import LRATCatcher.Tests.R44RootedGen4416Semantics
import LRATCatcher.Tests.R44RootedMixedClauses

/-!
  # From semantic mixed obstructions to the certified classifier CNF

  This module proves that the four semantic mixed-clique families imply all
  guarded local clauses used by the rooted `gen4416` classifier.
-/

namespace LRATCatcher.Tests.R44RootedMixedCNFSemantics

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedGen4416Semantics
open LRATCatcher.Tests.R44RootedMixedClauses

private theorem mem_pythonCombinations_properties
    {ambient vertices : List Nat} {size : Nat}
    (hmem : vertices ∈ pythonCombinations ambient size) :
    vertices.length = size ∧ vertices.Sublist ambient := by
  induction ambient generalizing size vertices with
  | nil =>
      cases size with
      | zero =>
          have hvertices : vertices = [] := by
            simpa [pythonCombinations] using hmem
          subst vertices
          simp
      | succ size =>
          simp [pythonCombinations] at hmem
  | cons head tail ih =>
      cases size with
      | zero =>
          have hvertices : vertices = [] := by
            simpa [pythonCombinations] using hmem
          subst vertices
          simp
      | succ size =>
          have hcases :
              vertices ∈
                (pythonCombinations tail size).map (head :: ·) ++
                  pythonCombinations tail (size + 1) := by
            simpa only [pythonCombinations] using hmem
          rcases List.mem_append.mp hcases with hwith | hwithout
          · rcases List.mem_map.mp hwith with ⟨rest, hrest, rfl⟩
            rcases ih hrest with ⟨hlength, hsublist⟩
            exact ⟨by simp [hlength], hsublist.cons_cons head⟩
          · rcases ih hwithout with ⟨hlength, hsublist⟩
            exact ⟨hlength, hsublist.cons head⟩

private theorem mem_pythonCombinations_range_two
    {bound : Nat} {vertices : List Nat}
    (hmem : vertices ∈ pythonCombinations (List.range bound) 2) :
    ∃ first second,
      vertices = [first, second] ∧ first < second ∧ second < bound := by
  rcases mem_pythonCombinations_properties hmem with ⟨hlength, hsublist⟩
  have hpairwise : vertices.Pairwise (fun left right => left < right) :=
    (List.pairwise_lt_range (n := bound)).sublist hsublist
  have hbound : ∀ vertex, vertex ∈ vertices → vertex < bound := by
    intro vertex hvertex
    exact List.mem_range.mp (hsublist.mem hvertex)
  have hshape : ∃ first second, vertices = [first, second] :=
    ⟨vertices[0]'(hlength ▸ by decide),
      vertices[1]'(hlength ▸ by decide),
      List.eq_getElem_of_length_eq_two vertices hlength⟩
  rcases hshape with ⟨first, second, rfl⟩
  simp at hpairwise
  exact ⟨first, second, rfl, hpairwise, hbound second (by simp)⟩

private theorem mem_pythonCombinations_range_three
    {bound : Nat} {vertices : List Nat}
    (hmem : vertices ∈ pythonCombinations (List.range bound) 3) :
    ∃ first second third,
      vertices = [first, second, third] ∧
        first < second ∧ second < third ∧ third < bound := by
  rcases mem_pythonCombinations_properties hmem with ⟨hlength, hsublist⟩
  have hpairwise : vertices.Pairwise (fun left right => left < right) :=
    (List.pairwise_lt_range (n := bound)).sublist hsublist
  have hbound : ∀ vertex, vertex ∈ vertices → vertex < bound := by
    intro vertex hvertex
    exact List.mem_range.mp (hsublist.mem hvertex)
  have hshape : ∃ first second third,
      vertices = [first, second, third] :=
    ⟨vertices[0]'(hlength ▸ by decide),
      vertices[1]'(hlength ▸ by decide),
      vertices[2]'(hlength ▸ by decide),
      List.eq_getElem_of_length_eq_three vertices hlength⟩
  rcases hshape with ⟨first, second, third, rfl⟩
  simp at hpairwise
  exact ⟨first, second, third, rfl, hpairwise.1.1,
    hpairwise.2, hbound third (by simp)⟩
@[simp] private theorem selectedAssignment_crossVariable
    (leftSelector antiSelector mask left anti : Nat)
    (hleft : left < 7) (hanti : anti < 8) :
    selectedAssignment leftSelector antiSelector mask
        (crossVariable left anti - 1) =
      maskBit mask (8 * left + anti) := by
  have hindex : crossVariable left anti - 1 = 8 * left + anti := by
    unfold crossVariable
    omega
  rw [hindex]
  simp [selectedAssignment]
  omega

private theorem selectedAssignment_otherSelector
    (leftSelector antiSelector mask otherLeft otherAnti : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3)
    (hotherLeft : otherLeft < 9) (hotherAnti : otherAnti < 3)
    (hdifferent : ¬(otherLeft = leftSelector ∧
      otherAnti = antiSelector)) :
    selectedAssignment leftSelector antiSelector mask
        (selectorVariable otherLeft otherAnti - 1) = false := by
  have hnotCross :
      ¬ selectorVariable otherLeft otherAnti - 1 < 56 := by
    simp [selectorVariable]
    omega
  simp only [selectedAssignment, hnotCross, ↓reduceIte]
  simp [selectorVariable]
  omega

@[simp] private theorem selectedAssignment_selectedSelector
    (leftSelector antiSelector mask : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3) :
    selectedAssignment leftSelector antiSelector mask
        (selectorVariable leftSelector antiSelector - 1) = true := by
  have hnotCross :
      ¬ selectorVariable leftSelector antiSelector - 1 < 56 := by
    simp [selectorVariable]
    omega
  simp [selectedAssignment, hnotCross]

private theorem inactive_guard_eval_true
    (leftSelector antiSelector mask otherLeft otherAnti : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3)
    (hotherLeft : otherLeft < 9) (hotherAnti : otherAnti < 3)
    (hdifferent : ¬(otherLeft = leftSelector ∧
      otherAnti = antiSelector)) (tail : List Int) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
        (dimacsClause
          (negativeVariable (selectorVariable otherLeft otherAnti) :: tail)) =
      true := by
  simp [dimacsClause, selectedAssignment_otherSelector _ _ _ _ _
    hleft hanti hotherLeft hotherAnti hdifferent]

private theorem active_negative_three_eval_true
    (leftSelector antiSelector mask left first second third : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hleft : left < 7) (hfirst : first < 8)
    (hsecond : second < 8) (hthird : third < 8)
    (hnot : ¬(maskBit mask (8 * left + first) = true ∧
      maskBit mask (8 * left + second) = true ∧
      maskBit mask (8 * left + third) = true)) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause
        [negativeVariable (selectorVariable leftSelector antiSelector),
         negativeVariable (crossVariable left first),
         negativeVariable (crossVariable left second),
         negativeVariable (crossVariable left third)]) = true := by
  simp only [dimacsClause, List.map_cons, List.map_nil,
    dimacsLit_negativeVariable, CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    selectedAssignment_selectedSelector _ _ _ hleftSelector hantiSelector,
    selectedAssignment_crossVariable _ _ _ _ _ hleft hfirst,
    selectedAssignment_crossVariable _ _ _ _ _ hleft hsecond,
    selectedAssignment_crossVariable _ _ _ _ _ hleft hthird]
  cases hfirstBit : maskBit mask (8 * left + first) <;>
    cases hsecondBit : maskBit mask (8 * left + second) <;>
    cases hthirdBit : maskBit mask (8 * left + third) <;>
    simp_all
private theorem active_negative_four_eval_true
    (leftSelector antiSelector mask leftFirst leftSecond antiFirst antiSecond : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hleftFirst : leftFirst < 7) (hleftSecond : leftSecond < 7)
    (hantiFirst : antiFirst < 8) (hantiSecond : antiSecond < 8)
    (hnot : ¬(maskBit mask (8 * leftFirst + antiFirst) = true ∧
      maskBit mask (8 * leftFirst + antiSecond) = true ∧
      maskBit mask (8 * leftSecond + antiFirst) = true ∧
      maskBit mask (8 * leftSecond + antiSecond) = true)) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause
        [negativeVariable (selectorVariable leftSelector antiSelector),
         negativeVariable (crossVariable leftFirst antiFirst),
         negativeVariable (crossVariable leftFirst antiSecond),
         negativeVariable (crossVariable leftSecond antiFirst),
         negativeVariable (crossVariable leftSecond antiSecond)]) = true := by
  simp only [dimacsClause, List.map_cons, List.map_nil,
    dimacsLit_negativeVariable, CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    selectedAssignment_selectedSelector _ _ _ hleftSelector hantiSelector,
    selectedAssignment_crossVariable _ _ _ _ _ hleftFirst hantiFirst,
    selectedAssignment_crossVariable _ _ _ _ _ hleftFirst hantiSecond,
    selectedAssignment_crossVariable _ _ _ _ _ hleftSecond hantiFirst,
    selectedAssignment_crossVariable _ _ _ _ _ hleftSecond hantiSecond]
  cases h00 : maskBit mask (8 * leftFirst + antiFirst) <;>
    cases h01 : maskBit mask (8 * leftFirst + antiSecond) <;>
    cases h10 : maskBit mask (8 * leftSecond + antiFirst) <;>
    cases h11 : maskBit mask (8 * leftSecond + antiSecond) <;>
    simp_all
private theorem active_positive_three_eval_true
    (leftSelector antiSelector mask first second third anti : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hfirst : first < 7) (hsecond : second < 7)
    (hthird : third < 7) (hanti : anti < 8)
    (hnot : ¬(maskBit mask (8 * first + anti) = false ∧
      maskBit mask (8 * second + anti) = false ∧
      maskBit mask (8 * third + anti) = false)) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause
        [negativeVariable (selectorVariable leftSelector antiSelector),
         positiveVariable (crossVariable first anti),
         positiveVariable (crossVariable second anti),
         positiveVariable (crossVariable third anti)]) = true := by
  have hpFirst : 0 < crossVariable first anti := by
    unfold crossVariable
    omega
  have hpSecond : 0 < crossVariable second anti := by
    unfold crossVariable
    omega
  have hpThird : 0 < crossVariable third anti := by
    unfold crossVariable
    omega
  simp only [dimacsClause, List.map_cons, List.map_nil,
    dimacsLit_negativeVariable,
    dimacsLit_positiveVariable _ hpFirst,
    dimacsLit_positiveVariable _ hpSecond,
    dimacsLit_positiveVariable _ hpThird,
    CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    selectedAssignment_selectedSelector _ _ _ hleftSelector hantiSelector,
    selectedAssignment_crossVariable _ _ _ _ _ hfirst hanti,
    selectedAssignment_crossVariable _ _ _ _ _ hsecond hanti,
    selectedAssignment_crossVariable _ _ _ _ _ hthird hanti]
  cases hfirstBit : maskBit mask (8 * first + anti) <;>
    cases hsecondBit : maskBit mask (8 * second + anti) <;>
    cases hthirdBit : maskBit mask (8 * third + anti) <;>
    simp_all
private theorem active_positive_four_eval_true
    (leftSelector antiSelector mask leftFirst leftSecond antiFirst antiSecond : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hleftFirst : leftFirst < 7) (hleftSecond : leftSecond < 7)
    (hantiFirst : antiFirst < 8) (hantiSecond : antiSecond < 8)
    (hnot : ¬(maskBit mask (8 * leftFirst + antiFirst) = false ∧
      maskBit mask (8 * leftFirst + antiSecond) = false ∧
      maskBit mask (8 * leftSecond + antiFirst) = false ∧
      maskBit mask (8 * leftSecond + antiSecond) = false)) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause
        [negativeVariable (selectorVariable leftSelector antiSelector),
         positiveVariable (crossVariable leftFirst antiFirst),
         positiveVariable (crossVariable leftFirst antiSecond),
         positiveVariable (crossVariable leftSecond antiFirst),
         positiveVariable (crossVariable leftSecond antiSecond)]) = true := by
  have hp00 : 0 < crossVariable leftFirst antiFirst := by
    unfold crossVariable
    omega
  have hp01 : 0 < crossVariable leftFirst antiSecond := by
    unfold crossVariable
    omega
  have hp10 : 0 < crossVariable leftSecond antiFirst := by
    unfold crossVariable
    omega
  have hp11 : 0 < crossVariable leftSecond antiSecond := by
    unfold crossVariable
    omega
  simp only [dimacsClause, List.map_cons, List.map_nil,
    dimacsLit_negativeVariable,
    dimacsLit_positiveVariable _ hp00,
    dimacsLit_positiveVariable _ hp01,
    dimacsLit_positiveVariable _ hp10,
    dimacsLit_positiveVariable _ hp11,
    CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    selectedAssignment_selectedSelector _ _ _ hleftSelector hantiSelector,
    selectedAssignment_crossVariable _ _ _ _ _ hleftFirst hantiFirst,
    selectedAssignment_crossVariable _ _ _ _ _ hleftFirst hantiSecond,
    selectedAssignment_crossVariable _ _ _ _ _ hleftSecond hantiFirst,
    selectedAssignment_crossVariable _ _ _ _ _ hleftSecond hantiSecond]
  cases h00Bit : maskBit mask (8 * leftFirst + antiFirst) <;>
    cases h01Bit : maskBit mask (8 * leftFirst + antiSecond) <;>
    cases h10Bit : maskBit mask (8 * leftSecond + antiFirst) <;>
    cases h11Bit : maskBit mask (8 * leftSecond + antiSecond) <;>
    simp_all
private theorem active_k4OneLeftThreeAnti_clause_eval_true
    (leftSelector antiSelector mask : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hvalid : K4OneLeftThreeAntiValid leftSelector antiSelector mask)
    (clause : List Int)
    (hclause : clause ∈
      k4OneLeftThreeAntiClauses leftSelector antiSelector
        (r34Catalogue8.getD antiSelector [])) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause clause) = true := by
  simp only [k4OneLeftThreeAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨antiTriple, hantiTriple, hclause⟩
  by_cases hindependent :
      isIndependent (r34Catalogue8.getD antiSelector []) antiTriple = true
  · rw [if_pos hindependent] at hclause
    rcases List.mem_map.mp hclause with ⟨left, hleft, rfl⟩
    rcases mem_pythonCombinations_range_three hantiTriple with
      ⟨first, second, third, rfl, hfirstSecond, hsecondThird,
        hthirdBound⟩
    have hleftBound := List.mem_range.mp hleft
    have hfirstBound : first < 8 := by omega
    have hsecondBound : second < 8 := by omega
    have hforbidden := hvalid left first second third hleftBound
      hfirstSecond hsecondThird hthirdBound hindependent
    simpa using active_negative_three_eval_true
      leftSelector antiSelector mask left first second third
      hleftSelector hantiSelector hleftBound hfirstBound hsecondBound
      hthirdBound hforbidden
  · rw [if_neg hindependent] at hclause
    simp at hclause
private theorem active_k4TwoLeftTwoAnti_clause_eval_true
    (leftSelector antiSelector mask : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hvalid : K4TwoLeftTwoAntiValid leftSelector antiSelector mask)
    (clause : List Int)
    (hclause : clause ∈
      k4TwoLeftTwoAntiClauses leftSelector antiSelector
        (r34Catalogue7.getD leftSelector [])
        (r34Catalogue8.getD antiSelector [])) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause clause) = true := by
  simp only [k4TwoLeftTwoAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨leftPair, hleftPair, hclause⟩
  by_cases hleftClique :
      isClique (r34Catalogue7.getD leftSelector []) leftPair = true
  · rw [if_pos hleftClique] at hclause
    rcases List.mem_filterMap.mp hclause with
      ⟨antiPair, hantiPair, hoption⟩
    by_cases hantiIndependent :
        isIndependent (r34Catalogue8.getD antiSelector []) antiPair = true
    · simp only [hantiIndependent, ↓reduceIte, Option.some.injEq] at hoption
      subst clause
      rcases mem_pythonCombinations_range_two hleftPair with
        ⟨leftFirst, leftSecond, rfl, hleftOrder, hleftSecondBound⟩
      rcases mem_pythonCombinations_range_two hantiPair with
        ⟨antiFirst, antiSecond, rfl, hantiOrder, hantiSecondBound⟩
      have hleftFirstBound : leftFirst < 7 := by omega
      have hantiFirstBound : antiFirst < 8 := by omega
      have hforbidden := hvalid leftFirst leftSecond antiFirst antiSecond
        hleftOrder hleftSecondBound hantiOrder hantiSecondBound
        hleftClique hantiIndependent
      simpa using active_negative_four_eval_true
        leftSelector antiSelector mask leftFirst leftSecond antiFirst antiSecond
        hleftSelector hantiSelector hleftFirstBound hleftSecondBound
        hantiFirstBound hantiSecondBound hforbidden
    · simp at hoption
      exact (hantiIndependent hoption.1).elim
  · rw [if_neg hleftClique] at hclause
    simp at hclause
private theorem active_i4ThreeLeftOneAnti_clause_eval_true
    (leftSelector antiSelector mask : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hvalid : I4ThreeLeftOneAntiValid leftSelector antiSelector mask)
    (clause : List Int)
    (hclause : clause ∈
      i4ThreeLeftOneAntiClauses leftSelector antiSelector
        (r34Catalogue7.getD leftSelector [])) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause clause) = true := by
  simp only [i4ThreeLeftOneAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨leftTriple, hleftTriple, hclause⟩
  by_cases hleftIndependent :
      isIndependent (r34Catalogue7.getD leftSelector []) leftTriple = true
  · rw [if_pos hleftIndependent] at hclause
    rcases List.mem_map.mp hclause with ⟨anti, hanti, rfl⟩
    rcases mem_pythonCombinations_range_three hleftTriple with
      ⟨first, second, third, rfl, hfirstSecond, hsecondThird,
        hthirdBound⟩
    have hantiBound := List.mem_range.mp hanti
    have hfirstBound : first < 7 := by omega
    have hsecondBound : second < 7 := by omega
    have hforbidden := hvalid first second third anti hfirstSecond
      hsecondThird hthirdBound hantiBound hleftIndependent
    simpa using active_positive_three_eval_true
      leftSelector antiSelector mask first second third anti
      hleftSelector hantiSelector hfirstBound hsecondBound hthirdBound
      hantiBound hforbidden
  · rw [if_neg hleftIndependent] at hclause
    simp at hclause
private theorem active_i4TwoLeftTwoAnti_clause_eval_true
    (leftSelector antiSelector mask : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hvalid : I4TwoLeftTwoAntiValid leftSelector antiSelector mask)
    (clause : List Int)
    (hclause : clause ∈
      i4TwoLeftTwoAntiClauses leftSelector antiSelector
        (r34Catalogue7.getD leftSelector [])
        (r34Catalogue8.getD antiSelector [])) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause clause) = true := by
  simp only [i4TwoLeftTwoAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨leftPair, hleftPair, hclause⟩
  by_cases hleftIndependent :
      isIndependent (r34Catalogue7.getD leftSelector []) leftPair = true
  · rw [if_pos hleftIndependent] at hclause
    rcases List.mem_filterMap.mp hclause with
      ⟨antiPair, hantiPair, hoption⟩
    by_cases hantiClique :
        isClique (r34Catalogue8.getD antiSelector []) antiPair = true
    · simp only [hantiClique, ↓reduceIte, Option.some.injEq] at hoption
      subst clause
      rcases mem_pythonCombinations_range_two hleftPair with
        ⟨leftFirst, leftSecond, rfl, hleftOrder, hleftSecondBound⟩
      rcases mem_pythonCombinations_range_two hantiPair with
        ⟨antiFirst, antiSecond, rfl, hantiOrder, hantiSecondBound⟩
      have hleftFirstBound : leftFirst < 7 := by omega
      have hantiFirstBound : antiFirst < 8 := by omega
      have hforbidden := hvalid leftFirst leftSecond antiFirst antiSecond
        hleftOrder hleftSecondBound hantiOrder hantiSecondBound
        hleftIndependent hantiClique
      simpa using active_positive_four_eval_true
        leftSelector antiSelector mask leftFirst leftSecond antiFirst antiSecond
        hleftSelector hantiSelector hleftFirstBound hleftSecondBound
        hantiFirstBound hantiSecondBound hforbidden
    · simp at hoption
      exact (hantiClique hoption.1).elim
  · rw [if_neg hleftIndependent] at hclause
    simp at hclause
private theorem active_local_clause_eval_true
    (leftSelector antiSelector mask : Nat)
    (hleftSelector : leftSelector < 9)
    (hantiSelector : antiSelector < 3)
    (hfamilies : MixedFamiliesValid leftSelector antiSelector mask)
    (clause : List Int)
    (hclause : clause ∈ localDimacsClauses leftSelector antiSelector) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause clause) = true := by
  unfold localDimacsClauses at hclause
  rcases List.mem_append.mp hclause with hfirstThree | hfourthFamily
  · rcases List.mem_append.mp hfirstThree with hfirstTwo | hthirdFamily
    · rcases List.mem_append.mp hfirstTwo with hfirstFamily | hsecondFamily
      · exact active_k4OneLeftThreeAnti_clause_eval_true
          leftSelector antiSelector mask hleftSelector hantiSelector
          hfamilies.k4OneLeftThreeAnti clause hfirstFamily
      · exact active_k4TwoLeftTwoAnti_clause_eval_true
          leftSelector antiSelector mask hleftSelector hantiSelector
          hfamilies.k4TwoLeftTwoAnti clause hsecondFamily
    · exact active_i4ThreeLeftOneAnti_clause_eval_true
        leftSelector antiSelector mask hleftSelector hantiSelector
        hfamilies.i4ThreeLeftOneAnti clause hthirdFamily
  · exact active_i4TwoLeftTwoAnti_clause_eval_true
      leftSelector antiSelector mask hleftSelector hantiSelector
      hfamilies.i4TwoLeftTwoAnti clause hfourthFamily
private theorem k4OneLeftThreeAnti_clause_guarded
    (leftSelector antiSelector : Nat) (antiGraph : Graph)
    (clause : List Int)
    (hclause : clause ∈
      k4OneLeftThreeAntiClauses leftSelector antiSelector antiGraph) :
    ∃ tail, clause =
      negativeVariable (selectorVariable leftSelector antiSelector) :: tail := by
  simp only [k4OneLeftThreeAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨antiTriple, hantiTriple, hclause⟩
  split at hclause
  · rcases List.mem_map.mp hclause with ⟨left, hleft, rfl⟩
    exact ⟨antiTriple.map fun anti =>
      negativeVariable (crossVariable left anti), rfl⟩
  · simp at hclause

private theorem i4ThreeLeftOneAnti_clause_guarded
    (leftSelector antiSelector : Nat) (leftGraph : Graph)
    (clause : List Int)
    (hclause : clause ∈
      i4ThreeLeftOneAntiClauses leftSelector antiSelector leftGraph) :
    ∃ tail, clause =
      negativeVariable (selectorVariable leftSelector antiSelector) :: tail := by
  simp only [i4ThreeLeftOneAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨leftTriple, hleftTriple, hclause⟩
  split at hclause
  · rcases List.mem_map.mp hclause with ⟨anti, hanti, rfl⟩
    exact ⟨leftTriple.map fun left =>
      positiveVariable (crossVariable left anti), rfl⟩
  · simp at hclause
private theorem k4TwoLeftTwoAnti_clause_guarded
    (leftSelector antiSelector : Nat) (leftGraph antiGraph : Graph)
    (clause : List Int)
    (hclause : clause ∈
      k4TwoLeftTwoAntiClauses leftSelector antiSelector leftGraph antiGraph) :
    ∃ tail, clause =
      negativeVariable (selectorVariable leftSelector antiSelector) :: tail := by
  simp only [k4TwoLeftTwoAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨leftPair, hleftPair, hclause⟩
  split at hclause
  · rcases List.mem_filterMap.mp hclause with
      ⟨antiPair, hantiPair, hoption⟩
    split at hoption
    · simp only [Option.some.injEq] at hoption
      subst clause
      exact ⟨leftPair.flatMap fun left => antiPair.map fun anti =>
        negativeVariable (crossVariable left anti), rfl⟩
    · simp at hoption
  · simp at hclause

private theorem i4TwoLeftTwoAnti_clause_guarded
    (leftSelector antiSelector : Nat) (leftGraph antiGraph : Graph)
    (clause : List Int)
    (hclause : clause ∈
      i4TwoLeftTwoAntiClauses leftSelector antiSelector leftGraph antiGraph) :
    ∃ tail, clause =
      negativeVariable (selectorVariable leftSelector antiSelector) :: tail := by
  simp only [i4TwoLeftTwoAntiClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨leftPair, hleftPair, hclause⟩
  split at hclause
  · rcases List.mem_filterMap.mp hclause with
      ⟨antiPair, hantiPair, hoption⟩
    split at hoption
    · simp only [Option.some.injEq] at hoption
      subst clause
      exact ⟨leftPair.flatMap fun left => antiPair.map fun anti =>
        positiveVariable (crossVariable left anti), rfl⟩
    · simp at hoption
  · simp at hclause
private theorem local_clause_guarded
    (leftSelector antiSelector : Nat) (clause : List Int)
    (hclause : clause ∈ localDimacsClauses leftSelector antiSelector) :
    ∃ tail, clause =
      negativeVariable (selectorVariable leftSelector antiSelector) :: tail := by
  unfold localDimacsClauses at hclause
  rcases List.mem_append.mp hclause with hfirstThree | hfourthFamily
  · rcases List.mem_append.mp hfirstThree with hfirstTwo | hthirdFamily
    · rcases List.mem_append.mp hfirstTwo with hfirstFamily | hsecondFamily
      · exact k4OneLeftThreeAnti_clause_guarded
          leftSelector antiSelector _ clause hfirstFamily
      · exact k4TwoLeftTwoAnti_clause_guarded
          leftSelector antiSelector _ _ clause hsecondFamily
    · exact i4ThreeLeftOneAnti_clause_guarded
        leftSelector antiSelector _ clause hthirdFamily
  · exact i4TwoLeftTwoAnti_clause_guarded
      leftSelector antiSelector _ _ clause hfourthFamily

private theorem inactive_local_clause_eval_true
    (leftSelector antiSelector mask otherLeft otherAnti : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3)
    (hotherLeft : otherLeft < 9) (hotherAnti : otherAnti < 3)
    (hdifferent : ¬(otherLeft = leftSelector ∧
      otherAnti = antiSelector)) (clause : List Int)
    (hclause : clause ∈ localDimacsClauses otherLeft otherAnti) :
    CNF.Clause.eval (selectedAssignment leftSelector antiSelector mask)
      (dimacsClause clause) = true := by
  rcases local_clause_guarded otherLeft otherAnti clause hclause with
    ⟨tail, rfl⟩
  exact inactive_guard_eval_true leftSelector antiSelector mask
    otherLeft otherAnti hleft hanti hotherLeft hotherAnti hdifferent tail
private theorem eval_mapped_dimacs_true
    (assignment : Nat → Bool) (clauses : List (List Int))
    (hall : ∀ clause, clause ∈ clauses →
      CNF.Clause.eval assignment (dimacsClause clause) = true) :
    CNF.eval assignment
      { clauses := (clauses.map dimacsClause).toArray } = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hindexList : index < clauses.length := by
    simpa using hindex
  simp only [List.getElem_toArray, List.getElem_map]
  exact hall clauses[index] (List.getElem_mem hindexList)

/-- The four semantic mixed obstruction families satisfy every guarded local
clause in the exact CNF reconstructed from the `gen4416` classifier. -/
theorem mixedFamilies_mixedR44Valid
    (leftSelector antiSelector mask : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3)
    (hfamilies : MixedFamiliesValid leftSelector antiSelector mask) :
    MixedR44Valid leftSelector antiSelector mask := by
  unfold MixedR44Valid localCNF
  apply eval_mapped_dimacs_true
  intro clause hclause
  unfold allLocalDimacsClauses at hclause
  rcases List.mem_flatMap.mp hclause with
    ⟨otherLeft, hotherLeft, hclause⟩
  rcases List.mem_flatMap.mp hclause with
    ⟨otherAnti, hotherAnti, hlocal⟩
  have hotherLeftBound := List.mem_range.mp hotherLeft
  have hotherAntiBound := List.mem_range.mp hotherAnti
  by_cases hselected :
      otherLeft = leftSelector ∧ otherAnti = antiSelector
  · rcases hselected with ⟨hleftEq, hantiEq⟩
    subst otherLeft
    subst otherAnti
    exact active_local_clause_eval_true leftSelector antiSelector mask
      hleft hanti hfamilies clause hlocal
  · exact inactive_local_clause_eval_true
      leftSelector antiSelector mask otherLeft otherAnti
      hleft hanti hotherLeftBound hotherAntiBound hselected clause hlocal

/-- A Ramsey-free canonical rooted coloring satisfies the exact local CNF
used by the checked classifier. -/
theorem ramseyFree_mixedR44Valid
    (leftSelector antiSelector mask : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3)
    (hfree : isRamseyFree 16 4 4
      (canonicalColoring leftSelector antiSelector mask)) :
    MixedR44Valid leftSelector antiSelector mask := by
  exact mixedFamilies_mixedR44Valid leftSelector antiSelector mask
    hleft hanti
    (ramseyFree_mixedFamiliesValid leftSelector antiSelector mask hfree)

#print axioms mixedFamilies_mixedR44Valid
#print axioms ramseyFree_mixedR44Valid
end LRATCatcher.Tests.R44RootedMixedCNFSemantics
