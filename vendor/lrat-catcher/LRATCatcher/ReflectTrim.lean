import LRATCatcher.Reflect
import Lean.Elab.Tactic.BVDecide.LRAT.Trim

/-!
  # Trimmed LRAT reflection

  This optional command removes proof actions which do not contribute to the
  final empty clause before embedding a textual LRAT certificate. The trimmed
  proof is still replayed by the same verified checker, so trimming remains an
  elaboration-time optimization and does not enlarge the trust base.
-/

open Lean Elab Command
open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATCatcher

/-- Read, parse, and trim a textual LRAT certificate. -/
def loadLratTrimmed (cmdName : String) (lratFile : TSyntax `str) :
    CommandElabM (Prod String (Array IntAction)) := do
  let (original, proof) <- loadLrat cmdName lratFile
  let trimmed <-
    match Lean.Elab.Tactic.BVDecide.LRAT.trim proof with
    | .ok trimmed => pure trimmed
    | .error e =>
        throwError "{cmdName}: LRAT trim error in '{lratFile.getString}': {e}"
  let trimmedText :=
    Std.Tactic.BVDecide.LRAT.lratProofToString trimmed
  logInfo m!"{cmdName}: trimmed {proof.size} to {trimmed.size} actions; {original.utf8ByteSize} to {trimmedText.utf8ByteSize} UTF-8 bytes"
  return (trimmedText, trimmed)

/-- Import the same theorem as `lrat_reflect`, after discarding LRAT actions
which are unused by the final empty clause. -/
elab "lrat_reflect_trim " n:ident ppSpace cnfFile:str ppSpace lratFile:str : command => do
  let cnfStr <- loadCnf cnfFile
  let (lratStr, _) <- loadLratTrimmed "lrat_reflect_trim" lratFile
  let cnfLit := Syntax.mkStrLit cnfStr
  let lratLit := Syntax.mkStrLit lratStr
  elabCommand (<- `(command|
    theorem $n : (LRATCatcher.parseDimacs $cnfLit).Unsat :=
      LRATCatcher.checkLrat_sound $cnfLit $lratLit (by native_decide)))

/-- `lrat_reflect_trim_cnf name (cnfTerm) "f.lrat"`: certify a Lean-defined
CNF after trimming the textual LRAT certificate at elaboration time. This is
the trimmed counterpart of `lrat_reflect_cnf`; the registered statement is
`name : cnfTerm.Unsat`. -/
elab "lrat_reflect_trim_cnf " n:ident ppSpace "(" cnfTerm:term ")" ppSpace
    lratFile:str : command => do
  let (lratStr, _) <- loadLratTrimmed "lrat_reflect_trim_cnf" lratFile
  let lratLit := Syntax.mkStrLit lratStr
  elabCommand (<- `(command|
    theorem $n : Std.Sat.CNF.Unsat ($cnfTerm : Std.Sat.CNF Nat) :=
      LRATCatcher.checkLratCnf_sound $cnfTerm $lratLit (by native_decide)))

/-- Kernel-checking variant. The trimmed action array is quoted directly. -/
elab "lrat_reflect_trim " "+" noWs &"kernel" ppSpace n:ident ppSpace
    cnfFile:str ppSpace lratFile:str : command => do
  let cnfStr <- loadCnf cnfFile
  let (_, proof) <- loadLratTrimmed "lrat_reflect_trim +kernel" lratFile
  let cnfT : Term :=
    Syntax.mkCApp ``Std.Sat.CNF.mk #[quote (parseDimacs cnfStr).clauses]
  emitKernelTheorem n cnfT proof

end LRATCatcher
