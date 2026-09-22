import LRATCatcher.Tests.R44RootedR34Catalogue
import LRATCatcher.Tests.R44RootedGen4416Classifier

/-!
  # Lean-side semantics of the rooted `gen4416` classifier

  The LRAT replay certifies a concrete DIMACS file.  This module reconstructs
  that formula from the certified `R(3,4)` subcatalogues and the 64 allowed
  cross-edge masks.  The computational equality below is the first semantic
  bridge: it pins every DIMACS variable, selector, mixed `K_4`/`I_4` clause,
  and mask blocker to an auditable Lean definition.
-/

namespace LRATCatcher.Tests.R44RootedGen4416Semantics

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedR34Catalogue

structure AllowedModel where
  leftSelector : Nat
  antiSelector : Nat
  mask : Nat
deriving DecidableEq, Repr

def allowedModels : List AllowedModel := [
  { leftSelector := 0, antiSelector := 2, mask := 7658540106213816 },
  { leftSelector := 0, antiSelector := 2, mask := 7803012962740533 },
  { leftSelector := 0, antiSelector := 2, mask := 12723097119988088 },
  { leftSelector := 0, antiSelector := 2, mask := 12799184136870195 },
  { leftSelector := 0, antiSelector := 2, mask := 14405683609303193 },
  { leftSelector := 0, antiSelector := 2, mask := 14524317875730477 },
  { leftSelector := 0, antiSelector := 2, mask := 14948764242917481 },
  { leftSelector := 0, antiSelector := 2, mask := 15034500931565595 },
  { leftSelector := 0, antiSelector := 2, mask := 20150307978988260 },
  { leftSelector := 0, antiSelector := 2, mask := 20235928252304022 },
  { leftSelector := 0, antiSelector := 2, mask := 28858999423488716 },
  { leftSelector := 0, antiSelector := 2, mask := 28935539166663303 },
  { leftSelector := 0, antiSelector := 2, mask := 29613729920719800 },
  { leftSelector := 0, antiSelector := 2, mask := 29758086361914165 },
  { leftSelector := 0, antiSelector := 2, mask := 33826783575159705 },
  { leftSelector := 0, antiSelector := 2, mask := 33945870567879469 },
  { leftSelector := 0, antiSelector := 2, mask := 38111723470048466 },
  { leftSelector := 0, antiSelector := 2, mask := 38230810462768230 },
  { leftSelector := 0, antiSelector := 2, mask := 42299507676013770 },
  { leftSelector := 0, antiSelector := 2, mask := 42443864117208135 },
  { leftSelector := 0, antiSelector := 2, mask := 43122054871264632 },
  { leftSelector := 0, antiSelector := 2, mask := 43198594614439219 },
  { leftSelector := 0, antiSelector := 2, mask := 51821665785623913 },
  { leftSelector := 0, antiSelector := 2, mask := 51907286058939675 },
  { leftSelector := 0, antiSelector := 2, mask := 57023093106362340 },
  { leftSelector := 0, antiSelector := 2, mask := 57108829795010454 },
  { leftSelector := 0, antiSelector := 2, mask := 57533276162197458 },
  { leftSelector := 0, antiSelector := 2, mask := 57651910428624742 },
  { leftSelector := 0, antiSelector := 2, mask := 59258409901057740 },
  { leftSelector := 0, antiSelector := 2, mask := 59334496917939847 },
  { leftSelector := 0, antiSelector := 2, mask := 64254581075187402 },
  { leftSelector := 0, antiSelector := 2, mask := 64399053931714119 },
  { leftSelector := 8, antiSelector := 0, mask := 6378634344189168 },
  { leftSelector := 8, antiSelector := 0, mask := 6378861088263408 },
  { leftSelector := 8, antiSelector := 0, mask := 11635331253980400 },
  { leftSelector := 8, antiSelector := 0, mask := 11635763351178480 },
  { leftSelector := 8, antiSelector := 0, mask := 15385834672407792 },
  { leftSelector := 8, antiSelector := 0, mask := 15386335220647152 },
  { leftSelector := 8, antiSelector := 0, mask := 16139365125507312 },
  { leftSelector := 8, antiSelector := 0, mask := 16139480636639472 },
  { leftSelector := 8, antiSelector := 0, mask := 19608867919641840 },
  { leftSelector := 8, antiSelector := 0, mask := 19609060438195440 },
  { leftSelector := 8, antiSelector := 0, mask := 24077202963053808 },
  { leftSelector := 8, antiSelector := 0, mask := 24077831856995568 },
  { leftSelector := 8, antiSelector := 0, mask := 24147709145659632 },
  { leftSelector := 8, antiSelector := 0, mask := 24148201137518832 },
  { leftSelector := 8, antiSelector := 0, mask := 24252227182710000 },
  { leftSelector := 8, antiSelector := 0, mask := 24252659279908080 },
  { leftSelector := 8, antiSelector := 0, mask := 24270253612910832 },
  { leftSelector := 8, antiSelector := 0, mask := 24270369124042992 },
  { leftSelector := 8, antiSelector := 0, mask := 38937102612446448 },
  { leftSelector := 8, antiSelector := 0, mask := 38937731506388208 },
  { leftSelector := 8, antiSelector := 0, mask := 47593827711372528 },
  { leftSelector := 8, antiSelector := 0, mask := 47594054455446768 },
  { leftSelector := 8, antiSelector := 0, mask := 47629013156938992 },
  { leftSelector := 8, antiSelector := 0, mask := 47629513705178352 },
  { leftSelector := 8, antiSelector := 0, mask := 47926789893012720 },
  { leftSelector := 8, antiSelector := 0, mask := 47926982411566320 },
  { leftSelector := 8, antiSelector := 0, mask := 48067596100580592 },
  { leftSelector := 8, antiSelector := 0, mask := 48067720168092912 },
  { leftSelector := 8, antiSelector := 0, mask := 55637733657818352 },
  { leftSelector := 8, antiSelector := 0, mask := 55637857725330672 },
  { leftSelector := 8, antiSelector := 0, mask := 56951638560356592 },
  { leftSelector := 8, antiSelector := 0, mask := 56952130552215792 }
]

def crossVariable (left anti : Nat) : Nat :=
  1 + 8 * left + anti

def selectorVariable (leftSelector antiSelector : Nat) : Nat :=
  57 + 3 * leftSelector + antiSelector

def positiveVariable (varIndex : Nat) : Int :=
  Int.ofNat varIndex

def negativeVariable (varIndex : Nat) : Int :=
  -(Int.ofNat varIndex)

/-- Python `itertools.combinations` order on an increasing ambient list. -/
def pythonCombinations : List Nat -> Nat -> List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | head :: tail, size + 1 =>
      (pythonCombinations tail size).map (head :: .) ++
        pythonCombinations tail (size + 1)

def isClique (graph : Graph) (vertices : List Nat) : Bool :=
  (pythonCombinations vertices 2).all fun pair =>
    match pair with
    | [left, right] => edge graph left right
    | _ => false

def isIndependent (graph : Graph) (vertices : List Nat) : Bool :=
  (pythonCombinations vertices 2).all fun pair =>
    match pair with
    | [left, right] => !(edge graph left right)
    | _ => false

def k4OneLeftThreeAntiClauses
    (leftSelector antiSelector : Nat) (antiGraph : Graph) : List (List Int) :=
  (pythonCombinations (List.range 8) 3).flatMap fun antiTriple =>
    if isIndependent antiGraph antiTriple then
      (List.range 7).map fun left =>
        negativeVariable (selectorVariable leftSelector antiSelector) ::
          antiTriple.map fun anti =>
            negativeVariable (crossVariable left anti)
    else
      []

def k4TwoLeftTwoAntiClauses
    (leftSelector antiSelector : Nat)
    (leftGraph antiGraph : Graph) : List (List Int) :=
  (pythonCombinations (List.range 7) 2).flatMap fun leftPair =>
    if isClique leftGraph leftPair then
      (pythonCombinations (List.range 8) 2).filterMap fun antiPair =>
        if isIndependent antiGraph antiPair then
          some (negativeVariable (selectorVariable leftSelector antiSelector) ::
            leftPair.flatMap fun left =>
              antiPair.map fun anti =>
                negativeVariable (crossVariable left anti))
        else
          none
    else
      []

def i4ThreeLeftOneAntiClauses
    (leftSelector antiSelector : Nat) (leftGraph : Graph) : List (List Int) :=
  (pythonCombinations (List.range 7) 3).flatMap fun leftTriple =>
    if isIndependent leftGraph leftTriple then
      (List.range 8).map fun anti =>
        negativeVariable (selectorVariable leftSelector antiSelector) ::
          leftTriple.map fun left =>
            positiveVariable (crossVariable left anti)
    else
      []

def i4TwoLeftTwoAntiClauses
    (leftSelector antiSelector : Nat)
    (leftGraph antiGraph : Graph) : List (List Int) :=
  (pythonCombinations (List.range 7) 2).flatMap fun leftPair =>
    if isIndependent leftGraph leftPair then
      (pythonCombinations (List.range 8) 2).filterMap fun antiPair =>
        if isClique antiGraph antiPair then
          some (negativeVariable (selectorVariable leftSelector antiSelector) ::
            leftPair.flatMap fun left =>
              antiPair.map fun anti =>
                positiveVariable (crossVariable left anti))
        else
          none
    else
      []

def localDimacsClauses
    (leftSelector antiSelector : Nat) : List (List Int) :=
  let leftGraph := r34Catalogue7.getD leftSelector []
  let antiGraph := r34Catalogue8.getD antiSelector []
  k4OneLeftThreeAntiClauses leftSelector antiSelector antiGraph ++
    k4TwoLeftTwoAntiClauses leftSelector antiSelector leftGraph antiGraph ++
    i4ThreeLeftOneAntiClauses leftSelector antiSelector leftGraph ++
    i4TwoLeftTwoAntiClauses leftSelector antiSelector leftGraph antiGraph

def allLocalDimacsClauses : List (List Int) :=
  (List.range 9).flatMap fun leftSelector =>
    (List.range 3).flatMap fun antiSelector =>
      localDimacsClauses leftSelector antiSelector

def selectorDimacsClause : List Int :=
  (List.range 27).map fun offset => positiveVariable (57 + offset)

def maskBit (mask bit : Nat) : Bool :=
  (mask / 2 ^ bit) % 2 == 1

def maskBlockingDimacsClause (model : AllowedModel) : List Int :=
  negativeVariable (selectorVariable model.leftSelector model.antiSelector) ::
    (List.range 56).map fun bit =>
      if maskBit model.mask bit then
        negativeVariable (bit + 1)
      else
        positiveVariable (bit + 1)

def classifierDimacsClauses : List (List Int) :=
  selectorDimacsClause ::
    (allLocalDimacsClauses ++ allowedModels.map maskBlockingDimacsClause)

def dimacsClause (clause : List Int) : CNF.Clause Nat :=
  clause.map LRATCatcher.dimacsLit

def classifierDecomposition : CNF Nat :=
  { clauses := (classifierDimacsClauses.map dimacsClause).toArray }

/-- Recover the exact formula appearing in the checked LRAT theorem. -/
def certifiedFormulaOfUnsat {formula : CNF Nat} (_ : formula.Unsat) : CNF Nat :=
  formula

def classifierFormula : CNF Nat :=
  certifiedFormulaOfUnsat
    LRATCatcher.Tests.r44_rooted_gen4416_classifier_unsat

theorem classifierFormula_unsat : classifierFormula.Unsat := by
  exact LRATCatcher.Tests.r44_rooted_gen4416_classifier_unsat

theorem allowedModels_length : allowedModels.length = 64 := by
  native_decide

theorem classifierDecomposition_numClauses :
    classifierDecomposition.clauses.size = 10880 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Byte-for-byte clause reconstruction of the certified external CNF. -/
theorem classifierFormula_eq_decomposition :
    classifierFormula = classifierDecomposition := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

/-! ## Semantic consequence of the LRAT refutation -/

def selectorCNF : CNF Nat :=
  { clauses := #[dimacsClause selectorDimacsClause] }

def localCNF : CNF Nat :=
  { clauses := (allLocalDimacsClauses.map dimacsClause).toArray }

def blockerCNF : CNF Nat :=
  { clauses := (allowedModels.map fun model =>
      dimacsClause (maskBlockingDimacsClause model)).toArray }

def classifierCoreCNF : CNF Nat :=
  selectorCNF ++ localCNF

theorem classifierDecomposition_eq_core_blockers :
    classifierDecomposition = classifierCoreCNF ++ blockerCNF := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

theorem classifierDecomposition_unsat : classifierDecomposition.Unsat :=
  Eq.mp (congrArg CNF.Unsat classifierFormula_eq_decomposition)
    classifierFormula_unsat

theorem classifierCoreBlockers_unsat :
    (classifierCoreCNF ++ blockerCNF).Unsat :=
  Eq.mp (congrArg CNF.Unsat classifierDecomposition_eq_core_blockers)
    classifierDecomposition_unsat

/-- A generic logical fact used to interpret a CNF consisting of a core and
one blocking clause per listed model. -/
theorem unsat_append_forces_false_clause {Model : Type}
    (core : CNF Nat) (models : List Model)
    (blocker : Model -> CNF.Clause Nat)
    (hunsat : (core ++ { clauses := (models.map blocker).toArray }).Unsat)
    (assignment : Nat -> Bool) (hcore : CNF.eval assignment core = true) :
    Exists (fun model => And (List.Mem model models)
      (CNF.Clause.eval assignment (blocker model) = false)) := by
  apply Classical.byContradiction
  intro hnone
  have heach : forall model, List.Mem model models ->
      CNF.Clause.eval assignment (blocker model) = true := by
    intro model hmodel
    cases hvalue : CNF.Clause.eval assignment (blocker model)
    case false =>
      exact False.elim
        (hnone (Exists.intro model (And.intro hmodel hvalue)))
    case true => rfl
  have hblockers :
      CNF.eval assignment
        { clauses := (models.map blocker).toArray } = true := by
    rw [CNF.eval, Array.all_eq_true]
    intro index hindex
    have hindexList : index < models.length := by simpa using hindex
    simp only [List.getElem_toArray, List.getElem_map]
    exact heach models[index] (List.getElem_mem hindexList)
  have hfalse := hunsat assignment
  rw [CNF.eval_append, hcore, hblockers] at hfalse
  contradiction

/-- The LRAT theorem forces at least one of the 64 blocker rows to match any
assignment satisfying the selector and all guarded mixed-clique clauses. -/
theorem classifierCore_forces_false_blocker
    (assignment : Nat -> Bool)
    (hcore : CNF.eval assignment classifierCoreCNF = true) :
    Exists (fun model => And (List.Mem model allowedModels)
      (CNF.Clause.eval assignment
        (dimacsClause (maskBlockingDimacsClause model)) = false)) := by
  exact unsat_append_forces_false_clause classifierCoreCNF allowedModels
    (fun model => dimacsClause (maskBlockingDimacsClause model))
    classifierCoreBlockers_unsat assignment hcore

@[simp] theorem dimacsLit_negativeVariable (varIndex : Nat) :
    LRATCatcher.dimacsLit (negativeVariable varIndex) =
      (varIndex - 1, false) := by
  simp [LRATCatcher.dimacsLit, negativeVariable]

@[simp] theorem dimacsLit_positiveVariable
    (varIndex : Nat) (hpositive : 0 < varIndex) :
    LRATCatcher.dimacsLit (positiveVariable varIndex) =
      (varIndex - 1, true) := by
  simp [LRATCatcher.dimacsLit, positiveVariable, hpositive]

/-- Propositional meaning of a false mask blocker.  Note the DIMACS-to-Lean
shift: cross variable `1 + bit` is assignment index `bit`, and selector
variable `57 + 3*a + b` is index `56 + 3*a + b`. -/
def AssignmentMatches
    (assignment : Nat -> Bool) (model : AllowedModel) : Prop :=
  And
    (assignment
      (selectorVariable model.leftSelector model.antiSelector - 1) = true)
    (forall bit, bit < 56 ->
      assignment bit = maskBit model.mask bit)

theorem maskBlockingClause_eval_false_iff
    (assignment : Nat -> Bool) (model : AllowedModel) :
    CNF.Clause.eval assignment
        (dimacsClause (maskBlockingDimacsClause model)) = false <->
      AssignmentMatches assignment model := by
  simp only [CNF.Clause.eval, dimacsClause, maskBlockingDimacsClause,
    List.map_cons, List.map_map, List.any_cons, List.any_map,
    Function.comp_apply, dimacsLit_negativeVariable,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.any_eq_false,
    List.mem_range, AssignmentMatches]
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      cases hvalue : assignment
          (selectorVariable model.leftSelector model.antiSelector - 1) <;>
        simp_all
    case right =>
      intro bit hbit
      have hliteral := h.2 bit hbit
      by_cases hmask : maskBit model.mask bit = true
      case pos =>
        simp [hmask, dimacsLit_negativeVariable] at hliteral
        cases hvalue : assignment bit <;> simp_all
      case neg =>
        have hmaskFalse : maskBit model.mask bit = false := by
          cases hvalue : maskBit model.mask bit <;> simp_all
        simp [hmaskFalse, dimacsLit_positiveVariable] at hliteral
        cases hvalue : assignment bit <;> simp_all
  case mpr =>
    intro h
    constructor
    case left => simp [h.1]
    case right =>
      intro bit hbit
      by_cases hmask : maskBit model.mask bit = true
      case pos =>
        simp [hmask, dimacsLit_negativeVariable, h.2 bit hbit]
      case neg =>
        have hmaskFalse : maskBit model.mask bit = false := by
          cases hvalue : maskBit model.mask bit <;> simp_all
        simp [hmaskFalse, dimacsLit_positiveVariable, h.2 bit hbit]

/-- Human-facing form of the finite classifier: every assignment satisfying
the Lean-defined rooted core agrees with one concrete allowed selector/mask
row. -/
theorem classifierCore_forces_allowed_model
    (assignment : Nat -> Bool)
    (hcore : CNF.eval assignment classifierCoreCNF = true) :
    Exists (fun model => And (List.Mem model allowedModels)
      (AssignmentMatches assignment model)) := by
  have hblocked := classifierCore_forces_false_blocker assignment hcore
  cases hblocked with
  | intro model hmodel =>
    exact Exists.intro model
      (And.intro hmodel.1
        ((maskBlockingClause_eval_false_iff assignment model).mp hmodel.2))
def allowedModelBounded (model : AllowedModel) : Bool :=
  decide (model.leftSelector < 9) && decide (model.antiSelector < 3) &&
    decide (model.mask < 2 ^ 56)

theorem allowedModels_bounded_checked :
    allowedModels.all allowedModelBounded = true := by
  native_decide

theorem allowedModel_bounds (model : AllowedModel)
    (hmodel : List.Mem model allowedModels) :
    And (And (model.leftSelector < 9) (model.antiSelector < 3))
      (model.mask < 2 ^ 56) := by
  have hcheck :=
    List.all_eq_true.mp allowedModels_bounded_checked model hmodel
  simpa [allowedModelBounded] using hcheck

/-- Assignment with exactly one selected catalogue pair and the supplied 56
cross bits. -/
def selectedAssignment
    (leftSelector antiSelector mask varIndex : Nat) : Bool :=
  if varIndex < 56 then maskBit mask varIndex
  else varIndex == selectorVariable leftSelector antiSelector - 1

/-- Syntactic mixed-clique validity of a selected rooted configuration.  The
next bridge will derive this predicate from semantic `R(4,4)`-freeness. -/
def MixedR44Valid (leftSelector antiSelector mask : Nat) : Prop :=
  CNF.eval (selectedAssignment leftSelector antiSelector mask) localCNF = true

theorem selectedAssignment_selector_sat
    (leftSelector antiSelector mask : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3) :
    CNF.eval (selectedAssignment leftSelector antiSelector mask)
      selectorCNF = true := by
  simp [CNF.eval, selectorCNF, CNF.Clause.eval, dimacsClause,
    selectorDimacsClause, positiveVariable, LRATCatcher.dimacsLit,
    selectedAssignment, selectorVariable]
  refine Exists.intro (3 * leftSelector + antiSelector)
    (And.intro (by omega) ?_)
  have hnatAbs :
      (57 + ((3 * leftSelector + antiSelector : Nat) : Int)).natAbs =
        57 + 3 * leftSelector + antiSelector := by
    apply Int.natAbs_eq_iff.mpr
    left
    omega
  rw [hnatAbs]
  have hnotlt :
      Not (57 + 3 * leftSelector + antiSelector - 1 < 56) := by
    omega
  simp [hnotlt]
  omega

/-- Concrete finite-classification theorem extracted from the LRAT proof.
For every bounded selector pair satisfying all guarded local clauses, Lean
returns an actual row of the 64-entry table with the same selectors and the
same 56 cross bits. -/
theorem selectedAssignment_forces_allowed_row
    (leftSelector antiSelector mask : Nat)
    (hleft : leftSelector < 9) (hanti : antiSelector < 3)
    (hvalid : MixedR44Valid leftSelector antiSelector mask) :
    Exists (fun model => And (List.Mem model allowedModels)
      (And (model.leftSelector = leftSelector)
        (And (model.antiSelector = antiSelector)
          (forall bit, bit < 56 ->
            maskBit model.mask bit = maskBit mask bit)))) := by
  have hselector := selectedAssignment_selector_sat
    leftSelector antiSelector mask hleft hanti
  have hcore :
      CNF.eval (selectedAssignment leftSelector antiSelector mask)
        classifierCoreCNF = true := by
    unfold MixedR44Valid at hvalid
    simp [classifierCoreCNF, hselector, hvalid]
  have hforced := classifierCore_forces_allowed_model
    (selectedAssignment leftSelector antiSelector mask) hcore
  cases hforced with
  | intro model hmodel =>
    have hb := allowedModel_bounds model hmodel.1
    have hmatch := hmodel.2
    have hselectorIndex :
        selectorVariable model.leftSelector model.antiSelector - 1 =
          selectorVariable leftSelector antiSelector - 1 := by
      have hnotlt :
          Not
            (selectorVariable model.leftSelector model.antiSelector - 1 <
              56) := by
        unfold selectorVariable
        omega
      simpa [AssignmentMatches, selectedAssignment, hnotlt] using hmatch.1
    have hleftEq : model.leftSelector = leftSelector := by
      unfold selectorVariable at hselectorIndex
      omega
    have hantiEq : model.antiSelector = antiSelector := by
      unfold selectorVariable at hselectorIndex
      omega
    exact Exists.intro model (And.intro hmodel.1
      (And.intro hleftEq (And.intro hantiEq (by
        intro bit hbit
        have hbitMatch := hmatch.2 bit hbit
        simp [selectedAssignment, hbit] at hbitMatch
        exact Eq.symm hbitMatch))))
#print axioms allowedModels_length
#print axioms classifierDecomposition_numClauses
#print axioms classifierFormula_eq_decomposition
#print axioms classifierCore_forces_allowed_model
#print axioms selectedAssignment_forces_allowed_row

end LRATCatcher.Tests.R44RootedGen4416Semantics
