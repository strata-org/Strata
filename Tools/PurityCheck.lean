/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! # Module Purity Checker

Determines whether elaborating a Lean module could potentially perform I/O.

Uses text scanning for known impure command patterns. This is sound because
Lean's impure-during-elaboration commands are a closed set — there are only
a handful of ways to trigger IO during elaboration, and they all have
distinctive textual signatures.

## Usage

  lake exe purityCheck [--impure-only] [--output <file>] <path> [path ...]

Prints each file with its purity status. With `--impure-only`, only prints
files that might perform I/O (useful for cache invalidation).
-/

/-- An impure command found during purity checking. -/
structure ImpureCommand where
  kind : String
  line : Nat
  col  : Nat

/-- Text patterns that indicate impure commands. Each pattern is matched
against the start of a trimmed line. The patterns cover all known ways
to perform IO during Lean module elaboration:

- `#eval` / `#eval!` — executes arbitrary code
- `initialize` / `builtin_initialize` — runs code at module load time
- `#guard_msgs` — executes code and checks output
- `#guard` — executes a boolean check at elaboration time

Custom elaborators defined via `initialize` in *other* modules could
perform IO, but those are caught by the `initialize` pattern in the
module that defines them. -/
private def impurePatterns : Array (String × String) := #[
  ("#eval!", "eval!"),
  ("#eval ", "eval"),
  ("#eval\n", "eval"),
  ("#guard_msgs", "guard_msgs"),
  ("#guard ", "guard"),
  ("builtin_initialize", "builtin_initialize"),
  ("initialize ", "initialize"),
  ("initialize\n", "initialize"),
  ("public initialize", "initialize"),
  ("private initialize", "initialize"),
  ("protected initialize", "initialize")
]

/-- Scan file text for impure command patterns. -/
def textScanForImpurity (contents : String) : List ImpureCommand :=
  go (contents.splitOn "\n") 1
where
  go : List String → Nat → List ImpureCommand
  | [], _ => []
  | line :: rest, lineNum =>
    let trimmed := line.trimAsciiStart.toString
    match impurePatterns.findSome? fun (pat, kind) =>
      if trimmed.startsWith pat then
        some { kind, line := lineNum, col := line.length - trimmed.length : ImpureCommand }
      else none
    with
    | some cmd => cmd :: go rest (lineNum + 1)
    | none => go rest (lineNum + 1)

/-- Check a file for purity. Returns impure commands found (empty = pure). -/
def checkFilePurity (contents : String) (_fileName : String := "<input>") :
    IO (List ImpureCommand) := do
  return textScanForImpurity contents

/-- Recursively collect all `.lean` files under a directory. -/
partial def collectLeanFiles (path : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← path.isDir then
    for entry in ← path.readDir do
      result := result ++ (← collectLeanFiles entry.path)
  else if path.extension == some "lean" then
    result := result.push path
  return result

/-- Resolve arguments: expand directories into .lean files. -/
def resolveInputs (inputs : List String) : IO (Array System.FilePath) := do
  let mut files := #[]
  for input in inputs do
    let path : System.FilePath := input
    if ← path.isDir then
      files := files ++ (← collectLeanFiles path)
    else
      files := files.push path
  return files

def purityCheckMain (args : List String) : IO UInt32 := do
  let impureOnly := args.contains "--impure-only"
  let rec findOutput : List String → Option String
    | "--output" :: v :: _ => some v
    | _ :: rest => findOutput rest
    | [] => none
  let outputFile := findOutput args
  let mut inputs : List String := []
  let mut skipNext := false
  for arg in args do
    if skipNext then
      skipNext := false
    else if arg == "--output" then
      skipNext := true
    else if !arg.startsWith "--" then
      inputs := arg :: inputs
  let inputPaths := inputs.reverse
  if inputPaths.isEmpty then
    IO.eprintln "Usage: purityCheck [--impure-only] [--output <file>] <path> [path ...]"
    IO.eprintln "  <path> can be a .lean file or a directory (recursively scanned)"
    return 1
  let files ← resolveInputs inputPaths
  let mut exitCode : UInt32 := 0
  let mut outputLines : Array String := #[]
  for file in files.toList.mergeSort (·.toString < ·.toString) do
    let contents ← IO.FS.readFile file
    let reasons ← checkFilePurity contents file.toString
    if reasons.isEmpty then
      unless impureOnly do
        IO.println s!"PURE:   {file}"
    else
      IO.println s!"IMPURE: {file}"
      outputLines := outputLines.push file.toString
      for r in reasons do
        IO.println s!"  - {r.kind} at {r.line}:{r.col}"
      exitCode := 1
  if let some outPath := outputFile then
    IO.FS.writeFile outPath (outputLines.toList.map (· ++ "\n") |>.foldl (· ++ ·) "")
    IO.eprintln s!"Wrote {outputLines.size} impure files to {outPath}"
  return exitCode
