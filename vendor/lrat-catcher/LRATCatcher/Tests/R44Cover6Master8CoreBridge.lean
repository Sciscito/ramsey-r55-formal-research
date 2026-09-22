import LRATCatcher.Basic

/-!
  # Generic UNSAT transfer from an indexed CNF core

  This module contains no Master8 clauses or certificate.  It isolates the
  small logical bridge needed after an external LRAT dependency reduction:
  an unsatisfiable sub-CNF makes every CNF containing its clauses
  unsatisfiable.

  `IndexedCNFSource` is the intended memory-safe interface for Master8.  A
  future source supplies one clause by index; selecting the certified core
  therefore materializes only those clauses, rather than the complete source
  CNF.
-/

namespace LRATCatcher.Tests.R44Cover6Master8CoreBridge

open Std.Sat

/-- Clause containment, ignoring order and multiplicity.  This is exactly the
logical relation needed to transfer UNSAT from a core to its parent CNF. -/
def ClauseSubset {Variable : Type}
    (core full : CNF Variable) : Prop :=
  ∀ clause, clause ∈ core.clauses → clause ∈ full.clauses

/-- UNSAT is monotone when clauses are added. -/
theorem unsat_of_clauseSubset {Variable : Type}
    {core full : CNF Variable}
    (hsubset : ClauseSubset core full)
    (hcore : core.Unsat) :
    full.Unsat := by
  intro assignment
  cases hfull : CNF.eval assignment full with
  | false => rfl
  | true =>
      have hfullClauses : ∀ index (hindex : index < full.clauses.size),
          CNF.Clause.eval assignment full.clauses[index] = true := by
        simpa only [CNF.eval, Array.all_eq_true] using hfull
      have hcoreEval : CNF.eval assignment core = true := by
        rw [CNF.eval, Array.all_eq_true]
        intro index hindex
        have hmemberCore : core.clauses[index] ∈ core.clauses :=
          Array.getElem_mem hindex
        have hmemberFull := hsubset core.clauses[index] hmemberCore
        rw [Array.mem_iff_getElem] at hmemberFull
        obtain ⟨fullIndex, fullBound, hequal⟩ := hmemberFull
        rw [← hequal]
        exact hfullClauses fullIndex fullBound
      have hfalse := hcore assignment
      rw [hcoreEval] at hfalse
      contradiction

/-! ## Direct selection from an already-materialized CNF -/

/-- Select clauses in the supplied index order.  Repeated indices are allowed;
they do not affect soundness. -/
def selectCNF {Variable : Type}
    (full : CNF Variable)
    (indices : Array (Fin full.clauses.size)) : CNF Variable :=
  { clauses := indices.map fun index => full.clauses[index.val] }

theorem selectCNF_clauseSubset {Variable : Type}
    (full : CNF Variable)
    (indices : Array (Fin full.clauses.size)) :
    ClauseSubset (selectCNF full indices) full := by
  intro clause hclause
  rw [selectCNF, Array.mem_map] at hclause
  obtain ⟨index, _hindex, rfl⟩ := hclause
  exact Array.getElem_mem index.isLt

theorem unsat_of_selectCNF_unsat {Variable : Type}
    (full : CNF Variable)
    (indices : Array (Fin full.clauses.size))
    (hcore : (selectCNF full indices).Unsat) :
    full.Unsat :=
  unsat_of_clauseSubset (selectCNF_clauseSubset full indices) hcore

/-! ## Lazy indexed source for the large Master8 formula -/

/-- A finite CNF presented by a clause-at-index function.  Unlike a material
`CNF`, this representation lets a reduced core evaluate only its selected
clauses. -/
structure IndexedCNFSource (Variable : Type) where
  clauseCount : Nat
  clauseAt : Fin clauseCount → CNF.Clause Variable

namespace IndexedCNFSource

def fullCNF {Variable : Type}
    (source : IndexedCNFSource Variable) : CNF Variable :=
  { clauses := Array.ofFn source.clauseAt }

/-- Materialize a core in exactly the order recorded by its original
zero-based clause indices. -/
def selectCNF {Variable : Type}
    (source : IndexedCNFSource Variable)
    (indices : Array (Fin source.clauseCount)) : CNF Variable :=
  { clauses := indices.map source.clauseAt }

theorem selectCNF_clauseSubset {Variable : Type}
    (source : IndexedCNFSource Variable)
    (indices : Array (Fin source.clauseCount)) :
    ClauseSubset (source.selectCNF indices) source.fullCNF := by
  intro clause hclause
  rw [selectCNF, Array.mem_map] at hclause
  obtain ⟨index, _hindex, rfl⟩ := hclause
  rw [fullCNF, Array.mem_ofFn]
  exact ⟨index, rfl⟩

/-- Compact certificate-facing representation.  A generated module may store
6,152 plain natural numbers and prove this single bounds invariant, instead
of attaching a separate proof term to every `Fin` literal. -/
structure Selection {Variable : Type}
    (source : IndexedCNFSource Variable) where
  zeroBasedIndices : Array Nat
  inBounds : ∀ index, index ∈ zeroBasedIndices → index < source.clauseCount

namespace Selection

def finIndices {Variable : Type} {source : IndexedCNFSource Variable}
    (selection : Selection source) : Array (Fin source.clauseCount) :=
  selection.zeroBasedIndices.attach.map fun index =>
    ⟨index.val, selection.inBounds index.val index.property⟩

def cnf {Variable : Type} {source : IndexedCNFSource Variable}
    (selection : Selection source) : CNF Variable :=
  source.selectCNF selection.finIndices

theorem cnf_clauseSubset {Variable : Type}
    {source : IndexedCNFSource Variable}
    (selection : Selection source) :
    ClauseSubset selection.cnf source.fullCNF :=
  source.selectCNF_clauseSubset selection.finIndices

theorem full_unsat_of_unsat {Variable : Type}
    {source : IndexedCNFSource Variable}
    (selection : Selection source)
    (hcore : selection.cnf.Unsat) :
    source.fullCNF.Unsat :=
  unsat_of_clauseSubset selection.cnf_clauseSubset hcore

end Selection

/-- Final generic endpoint intended for the reduced Master8 LRAT theorem. -/
theorem full_unsat_of_select_unsat {Variable : Type}
    (source : IndexedCNFSource Variable)
    (indices : Array (Fin source.clauseCount))
    (hcore : (source.selectCNF indices).Unsat) :
    source.fullCNF.Unsat :=
  unsat_of_clauseSubset (source.selectCNF_clauseSubset indices) hcore

end IndexedCNFSource

#print axioms unsat_of_clauseSubset
#print axioms IndexedCNFSource.full_unsat_of_select_unsat
#print axioms IndexedCNFSource.Selection.full_unsat_of_unsat

end LRATCatcher.Tests.R44Cover6Master8CoreBridge
