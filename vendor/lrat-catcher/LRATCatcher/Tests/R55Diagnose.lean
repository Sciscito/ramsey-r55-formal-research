import LRATCatcher.Reflect

open Std.Sat
open Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace LRATCatcher.Tests

def actionId : IntAction → Option Nat
  | .addEmpty id _ => some id
  | .addRup id _ _ => some id
  | .addRat id _ _ _ _ => some id
  | .del _ => none

def diagnose (f : DefaultFormula n) (proof : Array IntAction) : Result × Nat × Option Nat :=
  go f proof 0
where
  go {n : Nat} (f : DefaultFormula n) (proof : Array IntAction) (idx : Nat) :
      Result × Nat × Option Nat :=
    if h : idx < proof.size then
      let raw := proof[idx]
      let step := intActionToDefaultClauseAction n raw
      match step with
      | none => go f proof (idx + 1)
      | some (.addEmpty _ rupHints) =>
        let (_, ok) := Formula.performRupAdd f Clause.empty rupHints
        if ok then (.success, idx, actionId raw) else (.rupFailure, idx, actionId raw)
      | some (.addRup _ c rupHints) =>
        let (f, ok) := Formula.performRupAdd f c rupHints
        if ok then go f proof (idx + 1) else (.rupFailure, idx, actionId raw)
      | some (.addRat _ c pivot rupHints ratHints) =>
        if pivot ∈ Clause.toList c then
          let (f, ok) := Formula.performRatAdd f c pivot rupHints ratHints
          if ok then go f proof (idx + 1) else (.rupFailure, idx, actionId raw)
        else
          go f proof (idx + 1)
      | some (.del ids) => go (Formula.delete f ids) proof (idx + 1)
    else
      (.outOfProof, idx, none)

def diagnosticMain : IO Unit := do
  let cnfStr ← IO.FS.readFile "../../r55/hard_d20_c10_t312_reglex_w5.cnf"
  let lratStr ← IO.FS.readFile "../../r55/hard_t312_reglex_w5.lrat"
  match parseLRATProof lratStr.toUTF8 with
  | .error error => IO.println s!"parse error: {error}"
  | .ok proof =>
    let cnf := LRATCatcher.parseDimacs cnfStr
    let result := diagnose (CNF.convertLRAT cnf) proof
    IO.println s!"diagnostic result={result.1}, action_index={result.2.1}, clause_id={result.2.2}"

end LRATCatcher.Tests

def main : IO Unit := LRATCatcher.Tests.diagnosticMain
