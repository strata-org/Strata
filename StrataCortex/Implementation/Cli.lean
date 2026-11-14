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

/-- `program` with a new entry procedure that calls the `--entry` target, and the target's name.
    A target without a body is rejected: a call to it returns default results, so the run
    would report nothing. -/
def selectLaurelEntry (program : Laurel.LaurelProgram) (entry : String)
    : Except String (Laurel.LaurelProgram × String) := do
  let name := (← resolveEntryByName program entry).name.text
  -- The harness calls the procedure of this name that takes no inputs.
  let callee? := program.staticProcedures.find? fun p => p.name.text == name && p.inputs.isEmpty
  if callee?.any (·.body.implementation.isNone) then
    throw s!"entry procedure '{name}' has no body"
  return (← Laurel.withEntryHarness program name, name)

def interpretFlags : List Flag :=
  [{ name := "fuel", help := "Maximum execution steps.", takesArg := .arg "n" },
   { name := "entry", help := "Override the entry point to execute, by the name of a static procedure.",
     takesArg := .arg "proc" },
   { name := "keep-all-files", help := "Store intermediate programs in <dir>.", takesArg := .arg "dir" },
   { name := "interpreter", help := "Only `cortex`, the default, is supported: the Cortex interpreter runs the program.",
     takesArg := .arg "cortex" }]

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
  | none | some "cortex" => pure ()
  | some other => exitFailure s!"Invalid interpreter: '{other}' (Cortex supports only 'cortex')"
  let options ← parseLaurelVerifyOptions pflags
  let fuel ← match pflags.getString "fuel" with
    | some s => match s.toNat? with
      | .some 0 => exitFailure s!"Invalid fuel: '0' (must be > 0)"
      | .some n => pure n
      | .none => exitFailure s!"Invalid fuel: '{s}'"
    | none => pure 10000
  return (options, fuel)

def runInterpret (ionBytes : ByteArray) (pflags : ParsedFlags) : IO Unit := do
  let (options, fuel) ← parseInterpretFlags pflags
  let combinedProgram ← Strata.readLaurelIonProgram ionBytes
  let (combinedProgram, targetName?) ← match pflags.getString "entry" with
    | none => pure (combinedProgram, none)
    | some name =>
      match selectLaurelEntry combinedProgram name with
      | .ok (program, target) => pure (program, some target)
      | .error msg => exitFailure msg
  let outcome ← match Cortex.interpretEntries combinedProgram fuel options.translateOptions with
    | .ok outcome => pure outcome
    | .error msg => exitFailure msg
  printDiagnostics outcome.diagnostics
  for (procName, reason) in outcome.errors do
    IO.eprintln s!"'{targetName?.getD procName}': {reason}"
  unless outcome.errors.isEmpty do
    IO.Process.exit ExitCode.failuresFound

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
  let outcome ← match Cortex.interpretWire program fuel with
    | .ok outcome => pure outcome
    | .error msg => exitFailure msg
  printDiagnostics outcome.diagnostics
  for (procName, reason) in outcome.errors do
    IO.eprintln s!"'{procName}': {reason}"
  unless outcome.errors.isEmpty do
    IO.Process.exit ExitCode.failuresFound

def cortexInterpretBinaryCommand : Command where
  name := "cortexInterpretBinary"
  args := []
  flags := interpretFlags
  help := "Concretely interpret a Laurel Ion program read from stdin on the Cortex interpreter \
           (Laurel → Cortex → execute) and print diagnostics."
  callback := fun _ pflags => do
    let ionBytes ← (← IO.getStdin).readBinToEnd
    runInterpret ionBytes pflags

def cortexToCoreCommand : Command where
  name := "cortexToCore"
  args := [ "file" ]
  help := "Translate a Laurel source file to Core through the Cortex pipeline, print it and \
           type-check it. Procedure bodies are Core CFG bodies. Exit with an error on a type error."
  callback := fun v _ => do
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (coreProgramOption, errors) := Cortex.translate {} laurelProgram
    if !errors.isEmpty then
      IO.println s!"Core translation errors: {errors.map (·.message)}"
    match coreProgramOption with
    | none => return
    | some coreProgram =>
      IO.println (prettyPrintCore coreProgram)
      match _root_.Core.typeCheck .quiet coreProgram with
      | .ok _ => IO.println "Core type checking succeeded."
      | .error e => exitFailure s!"Core type checking failed: {e}"

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
      commands := [cortexInterpretBinaryCommand, cortexToCoreCommand, cortexWireInterpretBinaryCommand] }

end

end Cortex.Cli
