/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.Backends.CBMC.CollectSymbols
import Strata.Languages.Laurel
import Strata.Util.Json

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

/-- The Laurel-to-GOTO translation pipeline (equivalent to `strata laurelAnalyzeToGoto`).
    Produces `<baseName>.symtab.json` and `<baseName>.goto.json` in the given output directory. -/
private def laurelAnalyzeToGoto (path : System.FilePath) (outputDir : System.FilePath)
    (baseName : String) : IO Unit := do
  let content ← IO.FS.readFile path
  let laurelProgram ← Strata.parseLaurelText path content
  match ← Strata.Laurel.translate {} laurelProgram with
  | (none, diags) =>
    throw (IO.userError s!"Core translation errors: {diags.map (·.message)}")
  | (some coreProgram, _) =>
    let Ctx := { Lambda.LContext.default with
      functions := Core.Factory, knownTypes := Core.KnownTypes }
    let Env := Lambda.TEnv.default
    let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env coreProgram with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{e.format none}")
    let procs := tcPgm.decls.filterMap fun d => d.getProc?
    let funcs := tcPgm.decls.filterMap fun d =>
      match d.getFunc? with
      | some f =>
        let name := Core.CoreIdent.toPretty f.name
        if f.body.isSome && f.typeArgs.isEmpty
          && name != "Int.DivT" && name != "Int.ModT"
        then some f else none
      | none => none
    if procs.isEmpty && funcs.isEmpty then
      throw (IO.userError "No procedures or functions found")
    let typeSyms ← match collectExtraSymbols tcPgm with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"{e}")
    let typeSymsJson := Lean.toJson typeSyms
    let sourceText := some content
    let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
    let distincts := tcPgm.decls.filterMap fun d => match d with
      | .distinct name es _ => some (name, es) | _ => none
    let mut symtabPairs : List (String × Lean.Json) := []
    let mut gotoFns : Array Lean.Json := #[]
    let mut allLiftedFuncs : List Core.Function := []
    for p in procs do
      match procedureToGotoCtx Env p (sourceText := sourceText)
            (axioms := axioms) (distincts := distincts) with
      | .error e => throw (IO.userError s!"{e}")
      | .ok (ctx, liftedFuncs) =>
        allLiftedFuncs := allLiftedFuncs ++ liftedFuncs
        let procName := Core.CoreIdent.toPretty p.header.name
        let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson procName ctx)
        match json.symtab with
        | .obj m => symtabPairs := symtabPairs ++ m.toList
        | _ => pure ()
        match json.goto with
        | .obj m =>
          match m.toList.find? (·.1 == "functions") with
          | some (_, .arr fns) => gotoFns := gotoFns ++ fns
          | _ => pure ()
        | _ => pure ()
    for f in funcs ++ allLiftedFuncs do
      match functionToGotoCtx Env f with
      | .error e => throw (IO.userError s!"{e}")
      | .ok ctx =>
        let funcName := Core.CoreIdent.toPretty f.name
        let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson funcName ctx)
        match json.symtab with
        | .obj m => symtabPairs := symtabPairs ++ m.toList
        | _ => pure ()
        match json.goto with
        | .obj m =>
          match m.toList.find? (·.1 == "functions") with
          | some (_, .arr fns) => gotoFns := gotoFns ++ fns
          | _ => pure ()
        | _ => pure ()
    match typeSymsJson with
    | .obj m => symtabPairs := symtabPairs ++ m.toList
    | _ => pure ()
    -- Deduplicate: keep first occurrence of each symbol name
    let mut seen : Std.HashSet String := {}
    let mut dedupPairs : List (String × Lean.Json) := []
    for (k, v) in symtabPairs do
      if !seen.contains k then
        seen := seen.insert k
        dedupPairs := dedupPairs ++ [(k, v)]
    let symtabObj := dedupPairs.foldl
      (fun (acc : Std.TreeMap.Raw String Lean.Json) (k, v) => acc.insert k v)
      .empty
    let symtab := CProverGOTO.wrapSymtab symtabObj (moduleName := baseName)
    let goto := Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)]
    let symTabFile := (outputDir / s!"{baseName}.symtab.json").toString
    let gotoFile := (outputDir / s!"{baseName}.goto.json").toString
    writeJsonFile symTabFile symtab
    writeJsonFile gotoFile goto

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
