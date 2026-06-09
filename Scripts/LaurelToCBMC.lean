/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.Languages.Laurel

/-! # LaurelToCBMC

Script for testing the translation of a Laurel `.lr.st` source file through the
full Strata pipeline to CBMC verification:

1. Parse Laurel source → Laurel AST
2. Translate Laurel → Core
3. Type-check Core program
4. Generate CProver GOTO JSON (symtab + goto-functions)
5. Invoke `symtab2gb` to produce a GOTO binary
6. Invoke `goto-cc` to add C scaffolding
7. Invoke `goto-instrument --dfcc` for contract instrumentation
8. Invoke `cbmc` for bounded model checking

Usage:
  lake exe LaurelToCBMC <file.lr.st>

Environment variables:
  CBMC              - path to cbmc binary (default: cbmc)
  GOTO_CC           - path to goto-cc binary (default: goto-cc)
  GOTO_INSTRUMENT   - path to goto-instrument binary (default: goto-instrument)
-/

open Strata

/-- Strip well-known Strata file suffixes from a file path's basename. -/
private def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  let suffixes := [".lr.st", ".laurel.st", ".st"]
  match suffixes.find? (name.endsWith ·) with
  | some sfx => (name.dropEnd sfx.length).toString
  | none     => name

/-- Read an environment variable, returning a default if unset or empty. -/
private def getEnvOrDefault (var : String) (default : String) : IO String := do
  match ← IO.getEnv var with
  | some v => if v.isEmpty then pure default else pure v
  | none   => pure default

/-- Run an external process. Prints stdout/stderr to the caller's streams and
    returns the exit code. -/
private def runProcess (step : String) (cmd : String) (args : Array String)
    (cwd : Option String := none) : IO UInt32 := do
  let proc ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := cwd
    stdout := .inherit
    stderr := .inherit
    stdin := .inherit
  }
  let exitCode ← proc.wait
  if exitCode != 0 then
    IO.eprintln s!"Error: {step} failed (exit code {exitCode})"
  return exitCode

/-- The Laurel-to-GOTO translation pipeline. Parses a Laurel source file,
    translates to Core, inlines procedures, type-checks, and emits CProver GOTO
    JSON files (`<baseName>.symtab.json` and `<baseName>.goto.json`) in the
    given output directory. -/
private def laurelAnalyzeToGoto (path : System.FilePath) (outputDir : System.FilePath)
    (baseName : String) : IO Unit := do
  let content ← IO.FS.readFile path
  let laurelProgram ← Strata.parseLaurelText path content
  match ← Strata.Laurel.translate {} laurelProgram with
  | (none, diags) =>
    throw (IO.userError s!"Core translation errors: {diags.map (·.message)}")
  | (some coreProgram, _) =>
    -- Use the output directory as a prefix so files land in tmpDir
    let outputBaseName := (outputDir / baseName).toString
    match ← Strata.inlineCoreToGotoFiles coreProgram outputBaseName
              (sourceText := some content) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => throw (IO.userError msg)

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    unless file.endsWith ".lr.st" || file.endsWith ".laurel.st" do
      IO.eprintln s!"Error: expected a .lr.st file, got: {file}"
      return 1
    let path : System.FilePath := file
    unless ← path.pathExists do
      IO.eprintln s!"Error: file not found: {file}"
      return 1
    let baseName := deriveBaseName file

    -- Use a temporary directory for intermediate files (cleaned up automatically)
    IO.FS.withTempDir fun tmpDir => do

    -- Step 1: Laurel → GOTO JSON (in tmp dir)
    let result ← (laurelAnalyzeToGoto path tmpDir baseName).toBaseIO
    match result with
    | .error e =>
      IO.eprintln s!"Error: {e}"
      return 1
    | .ok () => pure ()

    let symTabFile := (tmpDir / s!"{baseName}.symtab.json").toString
    let gotoFile := (tmpDir / s!"{baseName}.goto.json").toString
    let gbFile := (tmpDir / s!"{baseName}.gb").toString
    let ccGbFile := (tmpDir / s!"{baseName}_cc.gb").toString
    let dfccGbFile := (tmpDir / s!"{baseName}_dfcc.gb").toString

    -- Step 2: symtab2gb
    let rc ← runProcess "symtab2gb" "symtab2gb"
      #[symTabFile, "--goto-functions", gotoFile, "--out", gbFile]
    if rc != 0 then return rc

    -- Step 3: goto-cc (add C scaffolding)
    let gotoCC ← getEnvOrDefault "GOTO_CC" "goto-cc"
    let rc ← runProcess "goto-cc" gotoCC
      #["--function", "main", "-o", ccGbFile, gbFile]
    if rc != 0 then return rc

    -- Step 4: goto-instrument --dfcc
    let gotoInstrument ← getEnvOrDefault "GOTO_INSTRUMENT" "goto-instrument"
    let rc ← runProcess "goto-instrument --dfcc" gotoInstrument
      #["--dfcc", "main", ccGbFile, dfccGbFile]
    if rc != 0 then return rc

    -- Step 5: cbmc verification
    let cbmc ← getEnvOrDefault "CBMC" "cbmc"
    runProcess "cbmc" cbmc
      #[dfccGbFile, "--function", "main", "--z3", "--verbosity", "9"]

  | _ =>
    IO.eprintln "Usage: LaurelToCBMC <file.lr.st>"
    return 1
