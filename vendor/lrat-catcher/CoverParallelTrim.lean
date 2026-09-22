import LRATCatcher.Cover

/-!
# `lratcatch-cover-parallel-trim` — modular trimmed cube-and-conquer proofs

This generator emits one Lean module per cube. Each module invokes
`lrat_reflect_trim_cnf` with the external LRAT path, so the generator never
reads or copies a certificate into generated source. It only checks that every
certificate exists before writing any module.

Usage:
  lratcatch-cover-parallel-trim base.cnf cubes.icnf leafPrefix cover.lrat Name [chunkSize]

Leaf paths are `{leafPrefix}{i}.lrat`, with 1-based indices in iCNF order.
`chunkSize` is accepted for command-line compatibility but must be exactly 1.
Relative certificate paths are preserved verbatim: run both generation and the
later Lake build from the package root so they resolve in the same directory.

Emits `Base.lean`, one `Chunk<i>.lean` per cube, `Cover.lean`, and `Main.lean`
under `LRATCatcher/Generated/<Name>/`. Only the chunk and cover modules read and
trim their corresponding LRAT when they are eventually built.
-/

open Std.Sat LRATCatcher

def trimParallelDie {α} (msg : String) : IO α := do
  IO.eprintln s!"lratcatch-cover-parallel-trim: {msg}"
  IO.Process.exit 1

def trimParallelReadInput (path : String) : IO String := do
  try IO.FS.readFile path
  catch e => trimParallelDie s!"cannot read '{path}': {e}"

/-! Keep the standalone generator on the same strict input subset as the
reflection commands. These checks intentionally leave `parseDimacs` and
`parseICnf` unchanged; they only reject inputs where their documented
leniency could hide malformed source text. -/

def trimParallelValidateDimacs (path s : String) : IO Unit := do
  let mut lineNo : Nat := 0
  let mut lastTok : Option Int := none
  for line in s.splitOn "\n" do
    lineNo := lineNo + 1
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "c" || t.startsWith "p" then
      continue
    unless t.front.isDigit || t.front == '-' do
      trimParallelDie
        s!"{path}:{lineNo}: unrecognized line (not a comment, header, or clause): '{t}'"
    for tok in t.split (fun ch => ch == ' ' || ch == '\t') do
      if tok.isEmpty then
        continue
      match tok.toInt? with
      | some literal => lastTok := some literal
      | none =>
          trimParallelDie
            s!"{path}:{lineNo}: non-integer token '{tok.toString}' in clause line"
  unless lastTok == some 0 do
    trimParallelDie s!"{path}: final clause is not terminated by 0"
  if (parseDimacs s).clauses.any (fun clause => clause.isEmpty) then
    IO.eprintln
      s!"lratcatch-cover-parallel-trim: warning: {path} contains an empty clause"

def trimParallelValidateICnf (path s : String) : IO Unit := do
  let mut lineNo : Nat := 0
  for line in s.splitOn "\n" do
    lineNo := lineNo + 1
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "c" || t.startsWith "p" then
      continue
    unless t == "a" || t.startsWith "a " || t.startsWith "a\t" do
      trimParallelDie
        s!"{path}:{lineNo}: unrecognized line (not a comment, header, or cube): '{t}'"
    let mut values : List Int := []
    for tok in (t.drop 1).split (fun ch => ch == ' ' || ch == '\t') do
      if tok.isEmpty then
        continue
      match tok.toInt? with
      | some literal => values := literal :: values
      | none =>
          trimParallelDie
            s!"{path}:{lineNo}: non-integer token '{tok.toString}' in cube line"
    match values with
    | [] =>
        trimParallelDie s!"{path}:{lineNo}: bare 'a' line without terminating 0"
    | 0 :: rest =>
        if rest.contains 0 then
          trimParallelDie s!"{path}:{lineNo}: more than one 0 in cube line"
        if rest.isEmpty then
          IO.eprintln
            s!"lratcatch-cover-parallel-trim: warning: {path}:{lineNo}: empty cube 'a 0'"
    | _ =>
        trimParallelDie s!"{path}:{lineNo}: cube line does not end with 0"

def trimParallelWriteOut (path content : String) : IO Unit := do
  try IO.FS.writeFile path content
  catch e => trimParallelDie s!"cannot write '{path}': {e}"

/-- Escape a value for a generated Lean string literal. Certificate paths are
preserved exactly apart from the escaping required by Lean syntax. -/
def trimParallelEscLean (s : String) : String :=
  if s.any (fun c => c == '"' || c == '\\') then
    (s.replace "\\" "\\\\").replace "\"" "\\\""
  else s

/-- Render one cube as a Lean `Cube` literal. -/
def trimParallelCubeLit (c : Cube) : String :=
  "[" ++ String.intercalate ", "
    (c.map (fun (v, b) => s!"({v}, {b})")) ++ "]"

def main (args : List String) : IO UInt32 := do
  let (baseFile, icnfFile, leafPrefix, coverFile, name, chunk) ←
    match args with
    | [b, i, lp, cv, n] => pure (b, i, lp, cv, n, 1)
    | [b, i, lp, cv, n, c] => pure (b, i, lp, cv, n, c.toNat?.getD 0)
    | _ =>
      trimParallelDie
        "usage: lratcatch-cover-parallel-trim base.cnf cubes.icnf leafPrefix cover.lrat Name [chunkSize]"
  if chunk != 1 then
    trimParallelDie "chunkSize must be exactly 1 (one independent module per cube)"
  if name.isEmpty || name.front.isDigit ||
      !name.all (fun c => c.isAlpha || c.isDigit || c == '_') then
    trimParallelDie
      s!"Name '{name}' must be a Lean identifier component (letters, digits, '_'; not digit-initial)"

  let baseStr ← trimParallelReadInput baseFile
  let icnfStr ← trimParallelReadInput icnfFile
  trimParallelValidateDimacs baseFile baseStr
  trimParallelValidateICnf icnfFile icnfStr
  let cubesArray := (parseICnf icnfStr).toArray
  let n := cubesArray.size
  if n == 0 then
    trimParallelDie "no cubes found in iCNF file"

  -- LRAT files can be enormous. Deliberately check only their existence here;
  -- the generated reflection commands will read, parse, trim, and verify them.
  unless (← System.FilePath.pathExists coverFile) do
    trimParallelDie s!"cover certificate not found: {coverFile}"
  for i in [1:n + 1] do
    let path := s!"{leafPrefix}{i}.lrat"
    unless (← System.FilePath.pathExists path) do
      trimParallelDie s!"leaf certificate not found: {path}"

  let modPrefix := s!"LRATCatcher.Generated.{name}"
  let dir := s!"LRATCatcher/Generated/{name}"
  try IO.FS.createDirAll dir
  catch e => trimParallelDie s!"cannot create directory '{dir}': {e}"

  -- ---- Base.lean ----
  let mut baseParts : Array String :=
    #[s!"import LRATCatcher.Cover\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n",
      s!"def base : CNF Nat := LRATCatcher.parseDimacs \"{trimParallelEscLean baseStr}\"\n\n"]
  for i in [1:n + 1] do
    baseParts := baseParts.push
      s!"def cube{i} : Cube := {trimParallelCubeLit cubesArray[i - 1]!}\n"
    baseParts := baseParts.push
      s!"def chunkCubes{i} : List Cube := [cube{i}]\n\n"
  let cubesExpr := String.intercalate " ++ "
    ((List.range n).map (fun i => s!"chunkCubes{i + 1}"))
  baseParts := baseParts.push
    s!"def cubes : List Cube := {cubesExpr}\n\nend {modPrefix}\n"
  trimParallelWriteOut s!"{dir}/Base.lean" (String.join baseParts.toList)

  -- ---- Chunk<i>.lean: one external, trimmed LRAT per cube ----
  for i in [1:n + 1] do
    let leafPath := s!"{leafPrefix}{i}.lrat"
    let chunkSource := String.join
      [s!"import LRATCatcher.Generated.{name}.Base\n",
       "import LRATCatcher.ReflectTrim\n\n",
       s!"open Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n",
       "set_option maxHeartbeats 0 in\n",
       "set_option maxRecDepth 1000000 in\n",
       s!"lrat_reflect_trim_cnf leaf{i}_ok\n",
       s!"  (Cube.leafCNF cube{i} base)\n",
       s!"  \"{trimParallelEscLean leafPath}\"\n\n",
       s!"theorem chunk{i}_ok : ∀ c ∈ chunkCubes{i}, (Cube.leafCNF c base).Unsat := by\n",
       "  intro c hc\n",
       s!"  simp [chunkCubes{i}] at hc\n",
       "  subst c\n",
       s!"  exact leaf{i}_ok\n\n",
       s!"end {modPrefix}\n"]
    trimParallelWriteOut s!"{dir}/Chunk{i}.lean" chunkSource

  -- ---- Cover.lean: external trimmed proof of the negated-cube cover ----
  let coverSource := String.join
    [s!"import LRATCatcher.Generated.{name}.Base\n",
     "import LRATCatcher.ReflectTrim\n\n",
     s!"open Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n",
     "set_option maxHeartbeats 0 in\n",
     "set_option maxRecDepth 1000000 in\n",
     "lrat_reflect_trim_cnf coverThm\n",
     "  (negCubesCNF cubes)\n",
     s!"  \"{trimParallelEscLean coverFile}\"\n\n",
     s!"end {modPrefix}\n"]
  trimParallelWriteOut s!"{dir}/Cover.lean" coverSource

  -- ---- Main.lean: pure composition, no certificate parsing or native_decide ----
  let mut mainParts : Array String :=
    #[s!"import LRATCatcher.Generated.{name}.Base\n",
      s!"import LRATCatcher.Generated.{name}.Cover\n"]
  for i in [1:n + 1] do
    mainParts := mainParts.push
      s!"import LRATCatcher.Generated.{name}.Chunk{i}\n"
  mainParts := mainParts.push
    s!"\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
  let openers := String.join ((List.range (n - 1)).map
    (fun i => s!"List.forall_mem_append.mpr ⟨chunk{i + 1}_ok, "))
  let allLeaves := openers ++ s!"chunk{n}_ok" ++
    String.join (List.replicate (n - 1) "⟩")
  mainParts := mainParts.push <| String.join
    ["set_option maxHeartbeats 0 in\n",
     "set_option maxRecDepth 1000000 in\n",
     "theorem base_unsat : base.Unsat :=\n",
     "  LRATCatcher.cover_unsat\n",
     s!"    ({allLeaves})\n",
     "    coverThm\n\n",
     s!"#print axioms base_unsat\n\nend {modPrefix}\n"]
  trimParallelWriteOut s!"{dir}/Main.lean" (String.join mainParts.toList)

  IO.println
    s!"lratcatch-cover-parallel-trim: {n} cubes → {n} independent modules in {dir}/"
  IO.println s!"  build from this same package root: lake build {modPrefix}.Main:olean"
  return 0
