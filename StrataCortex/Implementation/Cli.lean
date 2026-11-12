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

def wireInterpretFlags : List Flag :=
  [{ name := "fuel", help := "Maximum execution steps per entry procedure.", takesArg := .arg "n" },
   { name := "entry", help := "Run this parameterless procedure instead of the marked entries.",
     takesArg := .arg "proc" },
   { name := "interpreter", help := "Only `cortex` is supported: the Cortex interpreter runs the program.",
     takesArg := .arg "cortex" }]

def printDiagnostics (diagnostics : Array Message) : IO Unit := do
  IO.println s!"==== DIAGNOSTICS ===="
  for diag in diagnostics do
    IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"

def parseInterpretFlags (pflags : ParsedFlags) : IO (Laurel.LaurelVerifyOptions × Nat) := do
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
  return (options, fuel)

def runCoreEntries (core : _root_.Core.Program) (fuel : Nat) (targetName? : Option String) : IO Unit := do
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

def runInterpret (ionBytes : ByteArray) (pflags : ParsedFlags) : IO Unit := do
  let (options, fuel) ← parseInterpretFlags pflags
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
  runCoreEntries core fuel targetName?

def readWireProgram (bytes : ByteArray) : IO Wire.Program :=
  match Wire.readProgram bytes with
  | .ok p => pure p
  | .error e => exitFailure e

def selectWireEntry (program : Wire.Program) (entry : String) : Except String Wire.Program :=
  match program.procedures.filter (·.name == entry) with
  | [p] =>
    if !p.inputs.isEmpty then .error s!"entry procedure '{entry}' takes arguments"
    else if p.body.isNone then .error s!"entry procedure '{entry}' has no body"
    else .ok { program with procedures := program.procedures.map fun q => { q with entry := q.name == entry } }
  | [] => .error s!"entry procedure '{entry}' not found"
  | _ => .error s!"entry procedure '{entry}' is ambiguous"

def runWireInterpret (ionBytes : ByteArray) (pflags : ParsedFlags) : IO Unit := do
  match pflags.getString "interpreter" with
  | none | some "cortex" => pure ()
  | some other => exitFailure s!"Invalid interpreter: '{other}' (a Cortex program runs only on 'cortex')"
  let fuel ← match pflags.getString "fuel" with
    | some s => match s.toNat? with
      | .some 0 => exitFailure s!"Invalid fuel: '0' (must be > 0)"
      | .some n => pure n
      | .none => exitFailure s!"Invalid fuel: '{s}'"
    | none => pure 10000
  let program ← readWireProgram ionBytes
  let program ← match pflags.getString "entry" with
    | none => pure program
    | some name => match selectWireEntry program name with
      | .ok p => pure p
      | .error msg => exitFailure msg
  unless program.procedures.any (·.entry) do
    exitFailure "no entry point found: mark a procedure as an entry, or pass --entry <proc>"
  let (diagnostics, errors) ← match Cortex.interpretWire program fuel with
    | .ok r => pure r
    | .error msg => exitFailure msg
  printDiagnostics diagnostics
  for e in errors do
    IO.eprintln e
  unless errors.isEmpty do
    IO.Process.exit ExitCode.failuresFound

def inlineFlag : Flag :=
  { name := "inline-procedures",
    help := "Comma-separated names of procedures whose calls are replaced by their bodies, \
             so that a caller can rely on what they do. A procedure that can reach itself \
             through calls is not inlined.",
    takesArg := .arg "names" }

def inlineNames (pflags : ParsedFlags) : List String :=
  match pflags.getString "inline-procedures" with
  | some s => (s.splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")
  | none => []

def cortexAnalyzeCommand : Command where
  name := "cortexAnalyze"
  args := [ "file" ]
  flags := verifyOptionsFlags ++ [inlineFlag]
  help := "Analyze a Laurel source file through the Cortex pipeline. Write results to stdout."
  callback := fun v pflags => do
    let options ← parseLaurelVerifyOptions pflags (inputFile := some v[0])
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (vcResultsOption, errors) ← Cortex.verifyToVcResults laurelProgram options (inlineNames pflags)
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
  flags := verifyOptionsFlags ++ [inlineFlag]
  help := "Verify Laurel Ion programs read from stdin through the Cortex pipeline and print diagnostics."
  callback := fun _ pflags => do
    let options ← parseLaurelVerifyOptions pflags
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let combinedProgram ← Strata.readLaurelIonProgram stdinBytes
    printDiagnostics (← Cortex.verifyToMessages combinedProgram options (inlineNames pflags))

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
  flags := [{ name := "cfg",
              help := "Emit procedure bodies as Core CFG bodies and type-check the result; \
                       exit with an error on a type error." }]
  help := "Translate a Laurel source file to Core through the Cortex pipeline and print it."
  callback := fun v pflags => do
    let cfg := pflags.getBool "cfg"
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (coreProgramOption, errors) := Cortex.translate {} laurelProgram (cfg := cfg)
    if !errors.isEmpty then
      IO.println s!"Core translation errors: {errors.map (·.message)}"
    match coreProgramOption with
    | none => return
    | some coreProgram =>
      IO.println (prettyPrintCore coreProgram)
      if cfg then
        match _root_.Core.typeCheck .quiet coreProgram with
        | .ok _ => IO.println "Core type checking succeeded."
        | .error e => exitFailure s!"Core type checking failed: {e}"

def cortexWireAnalyzeBinaryCommand : Command where
  name := "cortexWireAnalyzeBinary"
  args := []
  flags := verifyOptionsFlags ++ [inlineFlag]
  help := "Verify a Cortex program in the Cortex wire format, read as Ion from stdin, and print diagnostics."
  callback := fun _ pflags => do
    let options ← parseLaurelVerifyOptions pflags
    let program ← readWireProgram (← (← IO.getStdin).readBinToEnd)
    printDiagnostics (← Cortex.verifyWireToMessages program options (inlineNames pflags))

def cortexWireInterpretBinaryCommand : Command where
  name := "cortexWireInterpretBinary"
  args := []
  flags := wireInterpretFlags
  help := "Concretely interpret a Cortex program in the Cortex wire format, read as Ion from stdin, \
           on the Cortex interpreter, and print diagnostics."
  callback := fun _ pflags => do
    runWireInterpret (← (← IO.getStdin).readBinToEnd) pflags

def cortexFrontend : CliFrontend where
  dialects := []
  group := fun _ =>
    { name := "Cortex"
      commands := [cortexAnalyzeCommand, cortexAnalyzeBinaryCommand, cortexInterpretBinaryCommand,
                   cortexToCoreCommand, cortexWireAnalyzeBinaryCommand, cortexWireInterpretBinaryCommand] }

end

end Cortex.Cli
