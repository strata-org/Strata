/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Lean.Parser.Extension
public import Strata.Cli.Framework
public import Strata.Cli.VerifyOptions
public import Strata.Cli.CoreCommands
public import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.SarifOutput
public import Strata.Pipeline.Context
public import Strata.Languages.C_Simp.Verify
public import Strata.Languages.B3.Verifier.Program
public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import Strata.Languages.C_Simp.DDMTransform.Parse
public import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator
public import StrataLaurel.Implementation
public import StrataLaurel.Implementation.CliOptions
public import StrataLaurel.Implementation.Interpreter
public import Strata.Languages.Core.EntryPoint
public import Strata.Transform.ProcedureInlining
public import StrataDDM.Util.IO

public import Strata.SimpleAPI
public import Strata.Util.Json
public import StrataDDM.BuiltinDialects
public import StrataDDM.Util.String

public import Strata.Backends.CBMC.CollectSymbols
public import Strata.Languages.Core.ProgramType
public import Strata.Backends.CBMC.GOTO.DefaultSymbols
public import StrataLaurel.Implementation.CoreDefinitionsForLaurel
public import StrataLaurel.Implementation.Grammar.LaurelGrammar
public meta import StrataLaurel.Implementation.Grammar.LaurelGrammar
public meta import Strata.Cli.CoreCommands
public meta import StrataLaurel.Implementation.CliOptions

public section

open Strata
open StrataDDM.Elab (LoadedDialects)

open Core (VerifyOptions VerboseMode VerificationMode CheckLevel EntryPoint)
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

namespace Strata.Cli

def laurelAnalyzeBinaryCommand : Command where
  name := "laurelAnalyzeBinary"
  args := []
  flags := verifyOptionsFlags ++ laurelPassFlags
  help := "Verify Laurel Ion programs read from stdin and print diagnostics. Combines multiple input files."
  callback := fun _ pflags => do
    if ← reportLaurelPasses pflags (withoutInput := false) then return
    let options ← parseLaurelVerifyOptions pflags
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let combinedProgram ← Strata.readLaurelIonProgram stdinBytes
    let diagnostics ← Strata.Laurel.verifyToMessages combinedProgram options

    IO.println s!"==== DIAGNOSTICS ===="
    for diag in diagnostics do
      IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"

/-- Normalize a procedure name for `--entry` matching. JVerify lowers a static
    method `pkg.Class.method` to a procedure named `pkg.Class?static?method`,
    so we drop the `?static` marker and treat the `?` and user-facing `#`
    separators as `_`.
    This lets `--entry pkg.Class#method` resolve regardless of those details. -/
private def normalizeEntryName (s : String) : String :=
  ((s.replace "?static?" "?").replace "#" "_").replace "?" "_"

/-- Flags for the Laurel interpret commands: `--fuel`, `--entry`,
    `--keep-all-files`, and the Laurel phase-selection flags. Shared by `laurelInterpret` (file input) and
    `laurelInterpretBinary` (stdin input). Deliberately excludes the
    solver-oriented flags in `verifyOptionsFlags` — the interpreter never
    invokes a solver, so those would be silently ignored. -/
private def laurelInterpretFlags : List Flag :=
  [{ name := "fuel", help := "Maximum execution steps.", takesArg := .arg "n" },
   { name := "entry",
     help := "Override the entry point to execute, by the name of a static procedure. \
              Defaults to the procedure(s) the producer marked with `entry` \
              in the Laurel source.",
     takesArg := .arg "proc" },
   { name := "keep-all-files",
     help := "Store intermediate programs in <dir>.",
     takesArg := .arg "dir" },
   { name := "interpreter",
     help := "Interpreter to execute with: `core` (default) translates to Core and runs \
              the Core interpreter; `laurel` runs the Laurel interpreter directly on the \
              resolved Laurel program, without translation to Core. `laurel` does \
              not support --keep-all-files.",
     takesArg := .arg "core|laurel" }] ++ laurelPassFlags

private def resolveLaurelEntryByName (prog : Laurel.LaurelProgram) (entry : String)
    : Except String Laurel.Procedure :=
  match prog.staticProcedures.find? (·.name.text == entry) with
  | some p => .ok p
  | none =>
    let target := normalizeEntryName entry
    match prog.staticProcedures.filter (normalizeEntryName ·.name.text == target) with
    | [p] => .ok p
    | [] => .error s!"entry procedure '{entry}' not found"
    | ps => .error s!"entry procedure '{entry}' is ambiguous: {ps.map (·.name.text)}"

private def runLaurelInterpretDirect (ionBytes : ByteArray) (pflags : ParsedFlags)
    : IO Unit := do
  if (pflags.getString "keep-all-files").isSome then
    exitFailure "--keep-all-files is not supported with --interpreter laurel"
  if (pflags.getString "phases").isSome || (pflags.getString "skip-phases").isSome then
    exitFailure "--phases and --skip-phases are not supported with --interpreter laurel"
  let fuel ← match pflags.getString "fuel" with
    | some s => match s.toNat? with
      | .some 0 => exitFailure s!"Invalid fuel: '0' (must be > 0)"
      | .some n => pure n
      | .none => exitFailure s!"Invalid fuel: '{s}'"
    | none => pure 100000
  let parsed ← Strata.readLaurelIonProgram ionBytes
  let dollarErrors := (Laurel.validateNoDollarNames parsed).filter (·.kind != .warning)
  unless dollarErrors.isEmpty do
    exitFailure s!"Laurel resolution failed: {dollarErrors.map (·.message)}"
  let entries ← match pflags.getString "entry" with
    | some name => match resolveLaurelEntryByName parsed name with
      | .ok p => pure [p]
      | .error msg => exitFailure msg
    | none =>
      match parsed.staticProcedures.filter (·.isInterpretEntry) with
      | [] => exitFailure "no entry point found: mark a procedure with `entry` in the \
                           Laurel source, or pass --entry <proc>"
      | ps => pure ps
  let translateOptions : LaurelTranslateOptions := {}
  let resolved := Laurel.resolve
    { parsed with
      staticProcedures := Laurel.coreDefinitionsForLaurel.staticProcedures ++ parsed.staticProcedures,
      types := Laurel.coreDefinitionsForLaurel.types ++ parsed.types }
    (gradualTypes := translateOptions.gradualTypes)
    (realizeCoercion := translateOptions.realizeCoercion) (toBool := translateOptions.toBool)
    (reservedNames := translateOptions.reservedNames)
  let rejected := resolved.errors.filter (·.kind != .warning)
  unless rejected.isEmpty do
    exitFailure s!"Laurel resolution failed: {rejected.map (·.message)}"
  let mut failures : Array Strata.Message := #[]
  let mut seen : Std.HashSet Strata.Message := {}
  let mut errors : Array (String × String) := #[]
  for p in entries do
    try
      let (_, fs, outcome) ← Laurel.Interpreter.evalProgramWithOutcome {}
        { entryProcedure := p.name.text, dumpState := false, printAsserts := false, fuel }
        resolved.program
      for f in fs do
        unless seen.contains f do
          failures := failures.push f
          seen := seen.insert f
      match outcome with
      | .completed => pure ()
      | .escaped v => errors := errors.push (p.name.text, s!"uncaught throw of {v.display}")
      | .outOfFuel => errors := errors.push (p.name.text, "out of fuel")
    catch e =>
      errors := errors.push (p.name.text, toString e)
  IO.println s!"==== DIAGNOSTICS ===="
  for diag in failures do
    IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"
  for (procName, e) in errors do
    IO.eprintln s!"'{procName}': {e}"
  unless errors.isEmpty do
    exitFailuresFound s!"{errors.size} entry procedure(s) ended with an interpreter error"

/-- Concretely execute a Laurel Ion program (already loaded as bytes) and print
    diagnostics. Shared implementation of `laurelInterpret` (file input) and
    `laurelInterpretBinary` (stdin input). `inputFile` is the source path, if
    any — used only to derive the `--keep-all-files` base name (stdin has none,
    which `keepAllFilesBaseName` maps to `program`). -/
private def runLaurelInterpret (ionBytes : ByteArray) (pflags : ParsedFlags)
    (inputFile : Option String := none) : IO Unit := do
  match pflags.getString "interpreter" with
  | none | some "core" => pure ()
  | some "laurel" => return ← runLaurelInterpretDirect ionBytes pflags
  | some other => exitFailure s!"Invalid interpreter: '{other}' (expected 'core' or 'laurel')"
  let options ← parseLaurelVerifyOptions pflags (inputFile := inputFile)
  -- Reject `0` explicitly: `runEntry` would return `OutOfFuel` before executing
  -- anything, which surfaces as exit 2 (failures found) with an empty diagnostics
  -- block — indistinguishable from a run that really did exhaust its budget, or
  -- worse, misread as assertion failures. Negatives are already rejected by
  -- `toNat?`.
  let fuel ← match pflags.getString "fuel" with
    | some s => match s.toNat? with
      | .some 0 => exitFailure s!"Invalid fuel: '0' (must be > 0)"
      | .some n => pure n
      | .none => exitFailure s!"Invalid fuel: '{s}'"
    | none => pure 10000
  let entryOverride := pflags.getString "entry"

  let combinedProgram ← Strata.readLaurelIonProgram ionBytes
  let (combinedProgram, targetName?) ← match entryOverride with
    | none => pure (combinedProgram, none)
    | some name =>
      match resolveLaurelEntryByName combinedProgram name with
      | .error msg => exitFailure msg
      | .ok target => match Laurel.withEntryHarness combinedProgram target.name.text with
        | .ok program => pure (program, some target.name.text)
        | .error msg => exitFailure msg

  -- Laurel → Core, mirroring the verify path's translate step.
  let core ← match ← Strata.Laurel.translate { options.translateOptions with analysisMode := .Execute } combinedProgram with
    | (some core, _diags) => pure core
    | (none, diags) => exitFailure s!"Laurel to Core translation failed: {diags.map (·.message)}"

  -- Type-check with the default Core factory (the Laurel verify path uses
  -- `Lambda.Factory.default`, not the Python `ReFactory`).
  let core ← match Core.typeCheck Core.VerifyOptions.quiet core with
    | .ok prog => pure prog
    | .error e => exitFailure s!"Core type checking failed: {e.message}"

  -- Make bodied functions unfold during concrete execution.
  let core := Core.Program.inlineBodiedFunctions core

  -- Persist the exact program the interpreter executes — the form produced
  -- after the interpret-specific type-check + `inlineBodiedFunctions` steps.
  -- Translation's per-pass intermediates stop before these steps, so under
  -- `--keep-all-files` this is the most useful artifact for debugging an
  -- interpret run. Mirrors the pipeline's `{prefix}.<...>.core.st` naming;
  -- the prefix directory is already created by the translate pipeline above.
  if let some pfx := options.translateOptions.keepAllFilesPrefix then
    IO.FS.writeFile s!"{pfx}.interpret.core.st" (toString (Std.format core))

  -- Run every procedure marked `entry`: with --entry, only the one
  -- `Laurel.withEntryHarness` added.
  let entries ← match Core.Program.entryProcedures core with
    | [] => exitFailure "no entry point found: mark a procedure with `entry` in the \
                         Laurel source, or pass --entry <proc>"
    | ps => pure ps

  -- Run the entries. `interpretEntries` is shared with the Laurel execute
  -- tests, so the evaluator configuration this command depends on — `assume`s
  -- treated as no-ops, and every assertion failure collected rather than
  -- halting on the first — is defined and regression-tested in one place.
  let outcome ← match Core.Program.interpretEntries core entries fuel with
    | .ok outcome => pure outcome
    | .error diag => exitFailure s!"interpreter setup failed: {diag}"

  IO.println s!"==== DIAGNOSTICS ===="
  -- Assertion failures go to stdout, mapped back to source where possible, so
  -- a single diagnostic-parsing contract catches every assertion violation.
  for diag in outcome.diagnostics do
    IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"
  for (procName, label) in outcome.unmapped do
    let procName := targetName?.getD procName
    IO.println s!"<no source>: assertion '{label}' in '{procName}' does not hold"
  -- OutOfFuel, Misc, etc. — these have no source range; surface raw.
  for (procName, e) in outcome.errors do
    let procName := targetName?.getD procName
    IO.eprintln s!"'{procName}': {Imperative.EvalError.toFormat (P := Core.Expression) e}"
  -- Assertion failures are reported as diagnostics above; the caller infers
  -- failure by parsing the `==== DIAGNOSTICS ====` output. Opaque failures
  -- (out of fuel / internal errors) carry no diagnostic, so signal those
  -- through the exit code directly.
  unless outcome.errors.isEmpty do
    IO.Process.exit ExitCode.failuresFound

def laurelInterpretCommand : Command where
  name := "laurelInterpret"
  args := [ "file" ]
  flags := laurelInterpretFlags
  help := "Concretely interpret a Laurel Ion program read from the given file (Laurel → Core → execute) \
           and print diagnostics. The entry point is the procedure marked `entry` by the \
           producer (or, if given, --entry by name); it is run with contracts treated as \
           runtime assertions and `assume`s treated as no-ops. \
           Assertion violations are reported as diagnostics under `==== DIAGNOSTICS ====` on \
           stdout (the caller detects failures by parsing them); the process still exits 0. A \
           non-zero exit code is reserved for errors that carry no diagnostic (out of fuel, \
           internal errors, setup failures)."
  reportFlags := laurelPassReportFlags
  callback := fun v pflags => do
    if ← reportLaurelPasses pflags (withoutInput := false) then return
    let ionBytes ← IO.FS.readBinFile v[0]
    runLaurelInterpret ionBytes pflags (inputFile := some v[0])

def laurelInterpretBinaryCommand : Command where
  name := "laurelInterpretBinary"
  args := []
  flags := laurelInterpretFlags
  help := "Concretely interpret a Laurel Ion program read from stdin (Laurel → Core → execute) \
           and print diagnostics. Combines multiple input files. See `laurelInterpret` for \
           the entry-point selection rules and the diagnostic/exit-code contract."
  callback := fun _ pflags => do
    if ← reportLaurelPasses pflags (withoutInput := false) then return
    let ionBytes ← (← IO.getStdin).readBinToEnd
    runLaurelInterpret ionBytes pflags

def laurelParseCommand : Command where
  name := "laurelParse"
  args := [ "file" ]
  help := "Parse a Laurel source file (no verification)."
  callback := fun v _ => do
    let _ ← Strata.readLaurelTextFile v[0]
    IO.println "Parse successful"

def laurelAnalyzeCommand : Command where
  name := "laurelAnalyze"
  args := [ "file" ]
  flags := verifyOptionsFlags ++ laurelPassFlags
  help := "Analyze a Laurel source file. Write diagnostics to stdout."
  reportFlags := laurelPassReportFlags
  callback := fun v pflags => do
    if ← reportLaurelPasses pflags (withoutInput := false) then return
    let options ← parseLaurelVerifyOptions pflags (inputFile := some v[0])
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (vcResultsOption, errors) ← Strata.Laurel.verifyToVcResults laurelProgram options
    if !errors.isEmpty then
      IO.println s!"==== ERRORS ===="
    for err in errors do
      IO.println s!"{err.message}"
    match vcResultsOption with
    | none => return
    | some vcResults =>
      IO.println s!"==== RESULTS ===="
      for vc in vcResults do
        IO.println s!"{vc.obligation.label}: {match vc.outcome with | .ok o => repr o | .error e => toString e}"

def laurelAnalyzeToGotoCommand : Command where
  name := "laurelAnalyzeToGoto"
  args := [ "file" ]
  flags := laurelPassFlags
  help := "Translate a Laurel source file to CProver GOTO JSON files."
  reportFlags := laurelPassReportFlags
  callback := fun v pflags => do
    if ← reportLaurelPasses pflags (withoutInput := false) then return
    let passes ← parseLaurelPasses pflags
    let path : System.FilePath := v[0]
    let content ← IO.FS.readFile path
    let laurelProgram ← Strata.parseLaurelText path content
    match ← Strata.Laurel.translate { passes } laurelProgram with
      | (none, diags) => exitFailure s!"Core translation errors: {diags.map (·.message)}"
      | (some coreProgram, errors) =>
        let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
        let Env := Lambda.TEnv.default
        let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env coreProgram with
          | .ok r => pure r
          | .error e => exitInternalError s!"{e.format none}"
        let procs := tcPgm.decls.filterMap fun d => d.getProc?
        let funcs := tcPgm.decls.filterMap fun d =>
          match d.getFunc? with
          | some f =>
            let name := Core.CoreIdent.toPretty f.name
            if f.body.isSome && f.typeArgs.isEmpty
              && name != "Int.DivT" && name != "Int.ModT"
            then some f else none
          | none => none
        if procs.isEmpty && funcs.isEmpty then exitInternalError "No procedures or functions found"
        let baseName := Strata.Cli.deriveBaseName [".st"] path.toString
        let typeSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure s
          | .error e => exitInternalError s!"{e}"
        let typeSymsJson := Lean.toJson typeSyms
        let sourceText := some content
        let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
        let distincts := tcPgm.decls.filterMap fun d => match d with
          | .distinct name es _ => some (name, es) | _ => none
        let mut symtabPairs : List (String × Lean.Json) := []
        let mut gotoFns : Array Lean.Json := #[]
        for p in procs do
          let procName := Core.CoreIdent.toPretty p.header.name
          match procedureToGotoCtx Env p (sourceText := sourceText) (axioms := axioms) (distincts := distincts)
                with
          | .error e => exitInternalError s!"{e}"
          | .ok ctx =>
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
        for f in funcs do
          let funcName := Core.CoreIdent.toPretty f.name
          match functionToGotoCtx Env f with
          | .error e => exitInternalError s!"{e}"
          | .ok ctx =>
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
        -- Deduplicate: keep first occurrence of each symbol name (proper function
        -- symbols come before basic symbol references from callers)
        let mut seen : Std.HashSet String := {}
        let mut dedupPairs : List (String × Lean.Json) := []
        for (k, v) in symtabPairs do
          if !seen.contains k then
            seen := seen.insert k
            dedupPairs := dedupPairs ++ [(k, v)]
        -- Add CBMC default symbols (architecture constants, builtins)
        -- and wrap in {"symbolTable": ...} for symtab2gb
        let symtabObj := dedupPairs.foldl
          (fun (acc : Std.TreeMap.Raw String Lean.Json) (k, v) => acc.insert k v)
          .empty
        let symtab := CProverGOTO.wrapSymtab symtabObj (moduleName := baseName)
        let goto := Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)]
        let symTabFile := s!"{baseName}.symtab.json"
        let gotoFile := s!"{baseName}.goto.json"
        writeJsonFile symTabFile symtab
        writeJsonFile gotoFile goto
        IO.println s!"Written {symTabFile} and {gotoFile}"

def laurelPrintCommand : Command where
  name := "laurelPrint"
  args := []
  help := "Read Laurel Ion from stdin and print in concrete syntax to stdout."
  callback := fun _ _ => do
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let program ← Strata.readLaurelIonProgram stdinBytes
    let p := Strata.laurelToStrataProgram program
    let c := p.formatContext {}
    let s := p.formatState
    let fmt := p.commands.foldl (init := f!"") fun f cmd =>
      f ++ (StrataDDM.mformat cmd c s).format
    IO.println (fmt.pretty 100)

def prettyPrintCore (p : Core.Program) : String :=
  let decls := p.decls.map fun d =>
    let s := toString (Std.format d)
    -- Add newlines after major sections in procedures
    s.replace "preconditions:" "\n  preconditions:"
     |>.replace "postconditions:" "\n  postconditions:"
     |>.replace "body:" "\n  body:\n    "
     |>.replace "assert [" "\n    assert ["
     |>.replace "init (" "\n    init ("
     |>.replace "while (" "\n    while ("
     |>.replace "if (" "\n      if ("
     |>.replace "call [" "\n    call ["
     |>.replace "else{" "\n      else {"
     |>.replace "}}" "}\n    }"
  String.intercalate "\n" decls

def laurelToCoreCommand : Command where
  name := "laurelToCore"
  args := [ "file" ]
  flags := laurelPassFlags
  help := "Translate a Laurel source file to Core and print to stdout."
  reportFlags := laurelPassReportFlags
  callback := fun v pflags => do
    if ← reportLaurelPasses pflags (withoutInput := false) then return
    let passes ← parseLaurelPasses pflags
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (coreProgramOption, errors) ← Strata.Laurel.translate { passes } laurelProgram
      if !errors.isEmpty then
        IO.println s!"Core translation errors: {errors.map (·.message)}"
      match coreProgramOption with
      | none => return
      | some coreProgram => IO.println (prettyPrintCore coreProgram)

end Strata.Cli

namespace StrataLaurel.Cli

open Strata.Cli

def laurelFrontend : Strata.Cli.CliFrontend where
  dialects := [Strata.Laurel.Laurel]
  group := fun _ =>
    { name := "Laurel"
      commands := [laurelAnalyzeCommand, laurelAnalyzeBinaryCommand,
                   laurelInterpretCommand, laurelInterpretBinaryCommand,
                   laurelAnalyzeToGotoCommand, laurelParseCommand,
                   laurelPrintCommand, laurelToCoreCommand] }

private def expectedCommandNames : List String :=
  ["check", "diff",
   "laurelAnalyze", "laurelAnalyzeBinary", "laurelAnalyzeToGoto",
   "laurelInterpret", "laurelInterpretBinary", "laurelParse",
   "laurelPrint", "laurelToCore", "print",
   "toIon", "transform", "verify"]

def commandGroups : List CommandGroup := Strata.Cli.buildCommandGroups [] {} [laurelFrontend]
def commandList : List Command := Strata.Cli.buildCommandList [] {} [laurelFrontend]
def commandMap : Std.HashMap String Command := Strata.Cli.buildCommandMap [] {} [laurelFrontend]

#guard (commandList.map (·.name) |>.mergeSort (· < ·)) == expectedCommandNames
#guard commandMap.size == commandList.length
#guard commandGroups.map (·.name) == ["Core", "Laurel"]

private def displayIgnoresInput (cmd : Command) (flag : String) : IO Bool := do
  let pflags := ({} : ParsedFlags).insert flag none
  let some (_, report) := cmd.reportFlags.find? (·.1 == flag) | return false
  let (withoutInput, _) ← IO.FS.withIsolatedStreams (report pflags)
  let (withInput, _) ← IO.FS.withIsolatedStreams
    (cmd.callback (Vector.replicate _ "/nonexistent/input.lr.st") pflags)
  return !withoutInput.isEmpty && withInput == withoutInput

/-- info: [true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval do
  let cmds := [laurelAnalyzeCommand, laurelToCoreCommand, laurelAnalyzeToGotoCommand, laurelInterpretCommand]
  IO.println (← (cmds.flatMap fun c => ["display-phases", "display-phase-contracts"].map (c, ·)).mapM
    fun (c, f) => displayIgnoresInput c f)

end StrataLaurel.Cli

end -- public section
