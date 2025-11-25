/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable with utilities for working with Strata files.
import Strata.DDM.Elab
import Strata.DDM.Ion

import Strata.Languages.Python.Python

def exitFailure {α} (message : String) : IO α := do
  IO.eprintln (message  ++ "\n\nRun strata --help for additional help.")
  IO.Process.exit 1

namespace Strata

def asText {m} [Monad m] [MonadExcept String m] (path : System.FilePath) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s =>
    pure s
  | none =>
    throw s!"{path} is not an Ion file and contains non UTF-8 data"

def mkErrorReport (path : System.FilePath) (errors : Array Lean.Message) : BaseIO String := do
  let msg : String := s!"{errors.size} error(s) reading {path}:\n"
  let msg ← errors.foldlM (init := msg) fun msg e =>
    return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
  return toString msg

inductive DialectOrProgram
| dialect (d : Dialect)
| program (pgm : Program)

end Strata

def readStrataText (fm : Strata.DialectFileMap) (input : System.FilePath) (bytes : ByteArray)
    : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let contents ←
    match Strata.asText input bytes with
    | Except.ok c => pure c
    | Except.error msg => exitFailure msg
  let inputContext := Strata.Parser.stringInputContext input contents
  let (header, errors, startPos) := Strata.Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    exitFailure  (← Strata.mkErrorReport input errors)
  match header with
  | .program stx dialect =>
    let dialects ←
      match ← Strata.Elab.loadDialect fm .builtin dialect with
      | (dialects, .ok _) => pure dialects
      | (_, .error msg) => exitFailure msg
    match Strata.Elab.elabProgramRest dialects leanEnv inputContext stx dialect startPos with
    | .ok program => pure (dialects, .program program)
    | .error errors =>     exitFailure  (← Strata.mkErrorReport input errors)
  | .dialect stx dialect =>
    let (loaded, d, s) ←
      Strata.Elab.elabDialectRest fm .builtin #[] inputContext stx dialect startPos
    if s.errors.size > 0 then
      exitFailure (← Strata.mkErrorReport input s.errors)
    pure (loaded.addDialect! d, .dialect d)

def fileReadError {α} (path : System.FilePath) (msg : String) : IO α := do
  IO.eprintln s!"Error reading {path}:"
  IO.eprintln s!"  {msg}\n"
  IO.eprintln s!"Either the file is invalid or there is a bug in Strata."
  IO.Process.exit 1

def readStrataIon (fm : Strata.DialectFileMap) (path : System.FilePath) (bytes : ByteArray) : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let (hdr, frag) ←
    match Strata.Ion.Header.parse bytes with
    | .error msg =>
      exitFailure msg
    | .ok p =>
      pure p
  match hdr with
  | .dialect dialect =>
    match ← Strata.Elab.loadDialectFromIonFragment fm .builtin #[] dialect frag with
    | (_, .error msg) =>
      fileReadError path msg
    | (dialects, .ok d) =>
      pure (dialects, .dialect d)
  | .program dialect => do
    let dialects ←
      match ← Strata.Elab.loadDialect fm .builtin dialect with
      | (loaded, .ok _) => pure loaded
      | (_, .error msg) => exitFailure msg
    match Strata.Program.fromIonFragment frag dialects.dialects dialect with
    | .ok pgm =>
      pure (dialects, .program pgm)
    | .error msg =>
      fileReadError path msg

def readFile (fm : Strata.DialectFileMap) (path : System.FilePath) : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let bytes ←
    match ← IO.FS.readBinFile path |>.toBaseIO with
    | .error _ =>
      exitFailure s!"Error reading {path}."
    | .ok c => pure c
  if bytes.startsWith Ion.binaryVersionMarker then
    readStrataIon fm path bytes
  else
    readStrataText fm path bytes

structure Command where
  name : String
  args : List String
  help : String
  callback : Strata.DialectFileMap → Vector String args.length → IO Unit

def checkCommand : Command where
  name := "check"
  args := [ "file" ]
  help := "Check a dialect or program file."
  callback := fun fm v => do
    let _ ← readFile fm v[0]
    pure ()

def toIonCommand : Command where
  name := "toIon"
  args := [ "input", "output" ]
  help := "Read a Strata text file and translate into Ion."
  callback := fun searchPath v => do
    let (_, pd) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.FS.writeBinFile v[1] d.toIon
    | .program pgm =>
      IO.FS.writeBinFile v[1] pgm.toIon

def printCommand : Command where
  name := "print"
  args := [ "file" ]
  help := "Write a Strata text or Ion file to standard output."
  callback := fun searchPath v => do
    let (ld, pd) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.print <| d.format ld.dialects
    | .program pgm =>
      IO.print <| toString pgm

def diffCommand : Command where
  name := "diff"
  args := [ "file1", "file2" ]
  help := "Check if two program files are syntactically equal."
  callback := fun fm v => do
    let ⟨_, p1⟩ ← readFile fm v[0]
    let ⟨_, p2⟩ ← readFile fm v[1]
    match p1, p2 with
    | .program p1, .program p2 =>
      if p1.dialect != p2.dialect then
        exitFailure s!"Dialects differ: {p1.dialect} and {p2.dialect}"
        let Decidable.isTrue eq := inferInstanceAs (Decidable (p1.commands.size = p2.commands.size))
          | exitFailure s!"Number of commands differ {p1.commands.size} and {p2.commands.size}"
        for (c1, c2) in Array.zip p1.commands p2.commands do
          if c1 != c2 then
            exitFailure s!"Commands differ: {repr c1} and {repr c2}"
    | _, _ =>
      exitFailure "Cannot compare dialect def with another dialect/program."

def pyTranslateCommand : Command where
  name := "pyTranslate"
  args := [ "file" ]
  help := "Tranlate a Strata Python Ion file to Strata.Boogie. Write results to stdout."
  callback := fun searchPath v => do
    let (ld, pd) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.print <| d.format ld.dialects
    | .program pgm =>
    let preludePgm := Strata.Python.Internal.Boogie.prelude
    let bpgm := Strata.pythonToBoogie pgm
    let newPgm : Boogie.Program := { decls := preludePgm.decls ++ bpgm.decls }
    IO.print newPgm

def pyAnalyzeCommand : Command where
  name := "pyAnalyze"
  args := [ "file", "verbose" ]
  help := "Analyze a Strata Python Ion file. Write results to stdout."
  callback := fun searchPath v => do
    let verbose := v[1] == "1"
    let (ld, pd) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.print <| d.format ld.dialects
    | .program pgm =>
    if verbose then
      IO.print pgm
    let preludePgm := Strata.Python.Internal.Boogie.prelude
    let bpgm := Strata.pythonToBoogie pgm
    let newPgm : Boogie.Program := { decls := preludePgm.decls ++ bpgm.decls }
    if verbose then
      IO.print newPgm
    let vcResults ← EIO.toIO (fun f => IO.Error.userError (toString f))
                        (Boogie.verify "z3" newPgm { Options.default with stopOnFirstError := false, verbose })
    let mut s := ""
    for vcResult in vcResults do
      s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
    IO.println s

def commandList : List Command := [
      checkCommand,
      toIonCommand,
      printCommand,
      diffCommand,
      pyAnalyzeCommand,
      pyTranslateCommand,
    ]

def commandMap : Std.HashMap String Command :=
  commandList.foldl (init := {}) fun m c => m.insert c.name c

def main (args : List String) : IO Unit := do
  match args with
  | ["--help"] => do
    IO.println "Usage: strata <command> [flags]...\n"
    for cmd in commandList do
      let args := cmd.args.foldl (init := s!"  {cmd.name}") fun s a => s!"{s} <{a}>"
      IO.println s!"  {args}: {cmd.help}"
    IO.println "\nFlags:"
    IO.println "  --include path: Adds a path to Strata for searching for dialects."
  | cmd :: args =>
    match commandMap[cmd]? with
    | none => exitFailure s!"Unknown command {cmd}"
    | some cmd =>
      let expectedArgs := cmd.args.length
      let rec process (sp : Strata.DialectFileMap) args (cmdArgs : List String) : IO _ := do
            match cmdArgs with
            | cmd :: cmdArgs =>
              match cmd with
              | "--include" =>
                let path :: cmdArgs := cmdArgs
                  | exitFailure s!"Expected path after --path."
                match ← sp.add path |>.toBaseIO with
                | .error msg => exitFailure msg
                | .ok sp => process sp args cmdArgs
              | _ =>
                if cmd.startsWith "--" then
                  exitFailure s!"Unknown option {cmd}."
                process sp (args.push cmd) cmdArgs
            | [] =>
              pure (sp, args)
      let (sp, args) ← process {} #[] args
      if p : args.size = cmd.args.length then
        cmd.callback sp ⟨args, p⟩
      else
        exitFailure s!"{cmd.name} expects {expectedArgs} argument(s)."
  | [] => do
    exitFailure "Expected subcommand."
