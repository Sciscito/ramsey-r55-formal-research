import LRATCatcher.Showcases.Ramsey

/-!
  # Small semantic trust-chain test for the universal cover6 route

  The external 10-variable CNF says that a red/blue colouring of `K5` is
  `R(3,3)`-free and contains no induced positive path on three vertices.
  CaDiCaL refutes that formula with a 379-byte LRAT certificate.  This file
  reconstructs every clause in Lean and promotes the replay to the graph
  theorem that every `R(3,3)`-free colouring of `K5` contains an induced
  positive `P3`.
-/

namespace LRATCatcher.Tests.R44Cover6ToyChain

open Std.Sat
open LRATCatcher.Ramsey

abbrev Vertex := Fin 5
abbrev Embedding := Vertex × Vertex × Vertex

lrat_reflect cover6_toy_p3_unsat
  "../../scripts/r45_d12_cover9_universal/toy_cover6/cover6_toy_p3.cnf"
  "../../scripts/r45_d12_cover9_universal/toy_cover6/cover6_toy_p3.lrat"

def certifiedFormulaOfUnsat {formula : CNF Nat}
    (_ : formula.Unsat) : CNF Nat :=
  formula

def certifiedToyFormula : CNF Nat :=
  certifiedFormulaOfUnsat cover6_toy_p3_unsat

theorem certifiedToyFormula_unsat : certifiedToyFormula.Unsat :=
  cover6_toy_p3_unsat

/-! ## Mathematical motif and its exact blocking clauses -/

/-- Symmetric variable for an edge of `K5`; callers use distinct vertices. -/
def symmetricEdgeVar (left right : Vertex) : Nat :=
  if left.val < right.val then
    edgeVar 5 left.val right.val
  else
    edgeVar 5 right.val left.val

def toyEdge (coloring : Nat → Bool) (left right : Vertex) : Bool :=
  coloring (symmetricEdgeVar left right)

/-- A genuine induced positive path: the two centre edges are positive and
the endpoint edge is negative. -/
def HasInducedPositiveP3 (coloring : Nat → Bool) : Prop :=
  ∃ left center right : Vertex,
    left ≠ center ∧ center ≠ right ∧ left ≠ right ∧
    toyEdge coloring left center = true ∧
    toyEdge coloring center right = true ∧
    toyEdge coloring left right = false

def p3Embeddings : List Embedding :=
  (List.finRange 5).flatMap fun left =>
    (List.finRange 5).flatMap fun center =>
      (List.finRange 5).filterMap fun right =>
        if left ≠ center ∧ center ≠ right ∧ left ≠ right then
          some (left, center, right)
        else
          none

theorem mem_p3Embeddings_iff (left center right : Vertex) :
    (left, center, right) ∈ p3Embeddings ↔
      left ≠ center ∧ center ≠ right ∧ left ≠ right := by
  native_decide +revert

def p3Blocker (embedding : Embedding) : CNF.Clause Nat :=
  let left := embedding.1
  let center := embedding.2.1
  let right := embedding.2.2
  [(symmetricEdgeVar left center, false),
   (symmetricEdgeVar center right, false),
   (symmetricEdgeVar left right, true)]

def p3BlockerCNF : CNF Nat :=
  { clauses := (p3Embeddings.map p3Blocker).toArray }

def toyDecomposition : CNF Nat :=
  encode 5 3 3 ++ p3BlockerCNF

theorem p3Embeddings_length : p3Embeddings.length = 60 := by
  native_decide

theorem toyDecomposition_numClauses :
    toyDecomposition.clauses.size = 80 := by
  native_decide

theorem certifiedToyFormula_eq_decomposition :
    certifiedToyFormula = toyDecomposition := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

/-! ## Semantic bridge -/

theorem ramseyToyCNF_sat (coloring : Nat → Bool)
    (hfree : isRamseyFree 5 3 3 coloring) :
    CNF.eval coloring (encode 5 3 3) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  exact clause_sat_of_mem 5 3 3 coloring hfree _ (Array.getElem_mem hindex)

theorem p3Blocker_sat_of_no_occurrence
    (coloring : Nat → Bool)
    (hno : ¬ HasInducedPositiveP3 coloring)
    (left center right : Vertex)
    (hmem : (left, center, right) ∈ p3Embeddings) :
    CNF.Clause.eval coloring (p3Blocker (left, center, right)) = true := by
  have hdistinct := (mem_p3Embeddings_iff left center right).mp hmem
  cases hleftCenter : toyEdge coloring left center with
  | false =>
      have hedge : coloring (symmetricEdgeVar left center) = false := by
        simpa [toyEdge] using hleftCenter
      simp [p3Blocker, CNF.Clause.eval, hedge]
  | true =>
      cases hcenterRight : toyEdge coloring center right with
      | false =>
          have hedge : coloring (symmetricEdgeVar center right) = false := by
            simpa [toyEdge] using hcenterRight
          simp [p3Blocker, CNF.Clause.eval, hedge]
      | true =>
          cases hleftRight : toyEdge coloring left right with
          | false =>
              exfalso
              exact hno ⟨left, center, right,
                hdistinct.1, hdistinct.2.1, hdistinct.2.2,
                hleftCenter, hcenterRight, hleftRight⟩
          | true =>
              have hedge : coloring (symmetricEdgeVar left right) = true := by
                simpa [toyEdge] using hleftRight
              simp [p3Blocker, CNF.Clause.eval, hedge]

theorem p3BlockerCNF_sat_of_no_occurrence
    (coloring : Nat → Bool)
    (hno : ¬ HasInducedPositiveP3 coloring) :
    CNF.eval coloring p3BlockerCNF = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hmem := Array.getElem_mem hindex
  simp only [p3BlockerCNF, List.mem_toArray, List.mem_map] at hmem
  obtain ⟨embedding, hembedding, hequal⟩ := hmem
  change CNF.Clause.eval coloring
    ((p3Embeddings.map p3Blocker).toArray[index]) = true
  rcases embedding with ⟨left, center, right⟩
  have hsatisfied := p3Blocker_sat_of_no_occurrence coloring hno
    left center right hembedding
  exact (congrArg (CNF.Clause.eval coloring) hequal).symm.trans hsatisfied

/-- Graph-level conclusion of the complete toy chain.  The statement contains
no CNF or generator-facing hypothesis. -/
theorem every_r33_order_five_contains_induced_positive_p3
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 5 3 3 coloring) :
    HasInducedPositiveP3 coloring := by
  apply Classical.byContradiction
  intro hno
  have hramsey := ramseyToyCNF_sat coloring hfree
  have hblockers := p3BlockerCNF_sat_of_no_occurrence coloring hno
  have hsat : CNF.eval coloring certifiedToyFormula = true := by
    rw [certifiedToyFormula_eq_decomposition]
    simp [toyDecomposition, hramsey, hblockers]
  have hfalse := certifiedToyFormula_unsat coloring
  rw [hsat] at hfalse
  contradiction

#print axioms cover6_toy_p3_unsat
#print axioms certifiedToyFormula_eq_decomposition
#print axioms every_r33_order_five_contains_induced_positive_p3

end LRATCatcher.Tests.R44Cover6ToyChain
