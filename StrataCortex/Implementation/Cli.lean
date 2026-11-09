/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.Cli
public import StrataCortex.Implementation.Pipeline
public import StrataCortex.Implementation.Interpret

namespace Cortex.Cli

open Strata Strata.Cli

public section

def normalizeEntryName (s : String) : String :=
  ((s.replace "?static?" "?").replace "#" "_").replace "?" "_"

def resolveEntryByName (prog : Laurel.LaurelProgram) (entry : String) : Except String Laurel.Procedure :=
  match prog.staticProcedures.find? (·.name.text == entry) with
  | some p => .ok p
  | none =>
    let target := normalizeEntryName entry
    match prog.staticProcedures.filter (normalizeEntryName ·.name.text == target) with
    | [p] => .ok p
    | [] => .error s!"entry procedure '{entry}' not found"
    | ps => .error s!"entry procedure '{entry}' is ambiguous: {ps.map (·.name.text)}"

def interpretFlags : List Flag :=
  [{ name := "fuel", help := "Maximum execution steps.", takesArg := .arg "n" },
   { name := "entry", help := "Override the entry point to execute, by the name of a static procedure.",
     takesArg := .arg "proc" },
   { name := "keep-all-files", help := "Store intermediate programs in <dir>.", takesArg := .arg "dir" },
   { name := "interpreter", help := "Only `core` is supported: the Core interpreter runs the lowered program.",
     takesArg := .arg "core" }]

def printDiagnostics (diagnostics : Array Message) : IO Unit := do
  IO.println s!"==== DIAGNOSTICS ===="
  for diag in diagnostics do
    IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"

def runInterpret (ionBytes : ByteArray) (pflags : ParsedFlags) : IO Unit := do
  match pflags.getString "interpreter" with
  | none | some "core" => pure ()
  | some other => exitFailure s!"Invalid interpreter: '{other}' (Cortex supports only 'core')"
  let options ← parseLaurelVerifyOptions pflags
  let fuel ← match pflags.getString "fuel" with
    | some s => match s.toNat? with
      | .some 0 => exitFailure s!"Invalid fuel: '0' (must be > 0)"
      | .some n => pure n
      | .none => exitFailure s!"Invalid fuel: '{s}'"
    | none => pure 10000
  let combinedProgram ← Strata.readLaurelIonProgram ionBytes
  let (combinedProgram, targetName?) ← match pflags.getString "entry" with
    | none => pure (combinedProgram, none)
    | some name =>
      match resolveEntryByName combinedProgram name with
      | .error msg => exitFailure msg
      | .ok target => match Laurel.withEntryHarness combinedProgram target.name.text with
        | .ok program => pure (program, some target.name.text)
        | .error msg => exitFailure msg
  let core ← match Cortex.toInterpretableCore options.translateOptions combinedProgram with
    | .ok core => pure core
    | .error msg => exitFailure msg
  let entries ← match _root_.Core.Program.entryProcedures core with
    | [] => exitFailure "no entry point found: mark a procedure with `entry` in the Laurel source, or pass --entry <proc>"
    | ps => pure ps
  let outcome ← match _root_.Core.Program.interpretEntries core entries fuel with
    | .ok outcome => pure outcome
    | .error diag => exitFailure s!"interpreter setup failed: {diag}"
  printDiagnostics outcome.diagnostics
  for (procName, label) in outcome.unmapped do
    IO.println s!"<no source>: assertion '{label}' in '{targetName?.getD procName}' does not hold"
  for (procName, e) in outcome.errors do
    IO.eprintln s!"'{targetName?.getD procName}': {Imperative.EvalError.toFormat (P := _root_.Core.Expression) e}"
  unless outcome.errors.isEmpty do
    IO.Process.exit ExitCode.failuresFound

def cortexAnalyzeCommand : Command where
  name := "cortexAnalyze"
  args := [ "file" ]
  flags := verifyOptionsFlags
  help := "Analyze a Laurel source file through the Cortex pipeline. Write results to stdout."
  callback := fun v pflags => do
    let options ← parseLaurelVerifyOptions pflags (inputFile := some v[0])
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (vcResultsOption, errors) ← Cortex.verifyToVcResults laurelProgram options
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

def cortexAnalyzeBinaryCommand : Command where
  name := "cortexAnalyzeBinary"
  args := []
  flags := verifyOptionsFlags
  help := "Verify Laurel Ion programs read from stdin through the Cortex pipeline and print diagnostics."
  callback := fun _ pflags => do
    let options ← parseLaurelVerifyOptions pflags
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let combinedProgram ← Strata.readLaurelIonProgram stdinBytes
    printDiagnostics (← Cortex.verifyToMessages combinedProgram options)

def cortexInterpretBinaryCommand : Command where
  name := "cortexInterpretBinary"
  args := []
  flags := interpretFlags
  help := "Concretely interpret a Laurel Ion program read from stdin (Laurel → Cortex → Core → execute) \
           and print diagnostics."
  callback := fun _ pflags => do
    let ionBytes ← (← IO.getStdin).readBinToEnd
    runInterpret ionBytes pflags

def cortexToCoreCommand : Command where
  name := "cortexToCore"
  args := [ "file" ]
  help := "Translate a Laurel source file to Core through the Cortex pipeline and print it."
  callback := fun v _ => do
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (coreProgramOption, errors) := Cortex.translate {} laurelProgram
    if !errors.isEmpty then
      IO.println s!"Core translation errors: {errors.map (·.message)}"
    match coreProgramOption with
    | none => return
    | some coreProgram => IO.println (prettyPrintCore coreProgram)

def cortexFrontend : CliFrontend where
  dialects := []
  group := fun _ =>
    { name := "Cortex"
      commands := [cortexAnalyzeCommand, cortexAnalyzeBinaryCommand, cortexInterpretBinaryCommand,
                   cortexToCoreCommand] }

end

end Cortex.Cli
