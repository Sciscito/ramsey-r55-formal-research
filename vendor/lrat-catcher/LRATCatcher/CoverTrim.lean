import LRATCatcher.Cover
import LRATCatcher.ReflectTrim

/-!
  # Trimmed LRAT reflection for cube-and-conquer covers

  This module provides the same DIMACS/iCNF interface as
  `lrat_cover_reflect`, but trims every leaf certificate and the final cover
  certificate before embedding their textual forms in the generated theorem.

  Trimming is only an elaboration-time size optimization.  The resulting
  strings are parsed and replayed by `checkCover`, and `checkCover_sound`
  remains the theorem which establishes unsatisfiability.
-/

open Lean Elab Command
open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATCatcher

/-- Turn a dynamically constructed file path into the string syntax expected
by `loadLratTrimmed`. -/
private def loadLratTrimmedAtPath (cmdName path : String) :
    CommandElabM String := do
  let pathSyntax : TSyntax `str := ⟨Syntax.mkStrLit path⟩
  let (trimmed, _) ← loadLratTrimmed cmdName pathSyntax
  return trimmed

/-- `lrat_cover_reflect_trim name "base.cnf" "cubes.icnf"
    "leafs/prefix" "cover.lrat"`:

    certify the same cube-and-conquer composition as `lrat_cover_reflect`,
    after trimming every textual LRAT proof.  Leaf paths are
    `{prefix}{i}.lrat` for the 1-based cube index in iCNF order.  DIMACS and
    iCNF validation are unchanged, and the registered statement is
    `name : (parseDimacs «base contents»).Unsat`. -/
elab "lrat_cover_reflect_trim " n:ident ppSpace baseFile:str ppSpace
    icnfFile:str ppSpace leafPrefix:str ppSpace coverFile:str : command => do
  let baseStr ← readFile' baseFile.getString
  validateDimacs baseFile.getString baseStr
  let icnfStr ← readFile' icnfFile.getString
  validateICnf icnfFile.getString icnfStr
  let cubes := parseICnf icnfStr
  if cubes.isEmpty then
    throwError
      "lrat_cover_reflect_trim: no cubes found in '{icnfFile.getString}'"
  let mut leafLits : Array Term := #[]
  for i in [1:cubes.length + 1] do
    let path := s!"{leafPrefix.getString}{i}.lrat"
    let trimmed ←
      loadLratTrimmedAtPath "lrat_cover_reflect_trim" path
    leafLits := leafLits.push (Syntax.mkStrLit trimmed)
  let (coverStr, _) ←
    loadLratTrimmed "lrat_cover_reflect_trim" coverFile
  let baseLit := Syntax.mkStrLit baseStr
  let icnfLit := Syntax.mkStrLit icnfStr
  let coverLit := Syntax.mkStrLit coverStr
  logInfo m!"lrat_cover_reflect_trim: {cubes.length} cubes"
  elabCommand (← `(command|
    set_option maxHeartbeats 0 in
    theorem $n : (LRATCatcher.parseDimacs $baseLit).Unsat :=
      LRATCatcher.checkCover_sound (LRATCatcher.parseDimacs $baseLit)
        (LRATCatcher.parseICnf $icnfLit) [$leafLits,*] $coverLit
          (by native_decide)))

end LRATCatcher
