/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable with utilities for working with Strata files.
import Strata.DDM.Elab
import Strata.DDM.Ion
import Strata.DDM.Util.ByteArray
import Strata.Util.IO

import Strata.DDM.Integration.Java.Gen
import Strata.Languages.Python.Python
import Strata.Transform.CoreTransform
import Strata.Transform.ProcedureInlining

import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator

def exitFailure {α} (message : String) : IO α := do
  IO.eprintln ("Exception: " ++ message  ++ "\n\nRun strata --help for additional help.")
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
  | .program _ dialect =>
    let dialects ←
      match ← Strata.Elab.loadDialect fm .builtin dialect with
      | (dialects, .ok _) => pure dialects
      | (_, .error msg) => exitFailure msg
    let .isTrue mem := inferInstanceAs (Decidable (dialect ∈ dialects.dialects))
      | panic! "internal: loadDialect failed"
    match Strata.Elab.elabProgramRest dialects leanEnv inputContext dialect mem startPos with
    | .ok program => pure (dialects, .program program)
    | .error errors => exitFailure (← Strata.mkErrorReport input errors)
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
    let .isTrue mem := inferInstanceAs (Decidable (dialect ∈ dialects.dialects))
      | panic! "loadDialect failed"
    let dm := dialects.dialects.importedDialects dialect mem
    match Strata.Program.fromIonFragment frag dm dialect with
    | .ok pgm =>
      pure (dialects, .program pgm)
    | .error msg =>
      fileReadError path msg

def readFile (fm : Strata.DialectFileMap) (path : System.FilePath) : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let bytes ← Strata.Util.readBinInputSource path.toString
  let displayPath : System.FilePath := Strata.Util.displayName path.toString
  if Ion.isIonFile bytes then
    readStrataIon fm displayPath bytes
  else
    readStrataText fm displayPath bytes

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
      let .isTrue mem := inferInstanceAs (Decidable (d.name ∈ ld.dialects))
        | IO.eprintln s!"Internal error reading file."
          return
      IO.print <| ld.dialects.format d.name mem
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

def readPythonStrata (path : String) : IO Strata.Program := do
  let bytes ← Strata.Util.readBinInputSource path
  if ! Ion.isIonFile bytes then
    exitFailure s!"pyAnalyze expected Ion file"
  match Strata.Program.fileFromIon Strata.Python.Python_map Strata.Python.Python.name bytes with
  | .ok p => pure p
  | .error msg => exitFailure msg

def pyTranslateCommand : Command where
  name := "pyTranslate"
  args := [ "file" ]
  help := "Translate a Strata Python Ion file to Strata Core. Write results to stdout."
  callback := fun _ v => do
    let pgm ← readPythonStrata v[0]
    let preludePgm := Strata.Python.Core.prelude
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures pgm
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    IO.print newPgm

/-- Derive Python source file path from Ion file path.
    E.g., "tests/test_foo.python.st.ion" -> "tests/test_foo.py" -/
def ionPathToPythonPath (ionPath : String) : Option String :=
  if ionPath.endsWith ".python.st.ion" then
    let basePath := ionPath.dropRight ".python.st.ion".length
    some (basePath ++ ".py")
  else
    none

/-- Try to read Python source file and create a FileMap for line/column conversion -/
def tryReadPythonSource (ionPath : String) : IO (Option (String × Lean.FileMap)) := do
  match ionPathToPythonPath ionPath with
  | none => return none
  | some pyPath =>
    try
      let content ← IO.FS.readFile pyPath
      let fileMap := Lean.FileMap.ofString content
      return some (pyPath, fileMap)
    catch _ =>
      return none

def pyAnalyzeCommand : Command where
  name := "pyAnalyze"
  args := [ "file", "verbose" ]
  help := "Analyze a Strata Python Ion file. Write results to stdout."
  callback := fun _ v => do
    let verbose := v[1] == "1"
    let filePath := v[0]
    let pgm ← readPythonStrata filePath
    -- Try to read the Python source for line number conversion
    let pySourceOpt ← tryReadPythonSource filePath
    if verbose then
      IO.print pgm
    let preludePgm := Strata.Python.Core.prelude
    -- Use the Python source path if available, otherwise fall back to Ion path
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures pgm sourcePathForMetadata
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    if verbose then
      IO.print newPgm
    match Core.Transform.runProgram
          (Core.ProcedureInlining.inlineCallCmd (excluded_calls := ["main"]))
          newPgm .emp with
    | ⟨.error e, _⟩ => panic! e
    | ⟨.ok newPgm, _⟩ =>
      if verbose then
        IO.println "Inlined: "
        IO.print newPgm
      let solverName : String := "Strata/Languages/Python/z3_parallel.py"
      let verboseMode := VerboseMode.ofBool verbose
      let vcResults ← IO.FS.withTempDir (fun tempDir =>
          EIO.toIO
            (fun f => IO.Error.userError (toString f))
            (Core.verify solverName newPgm tempDir .none
              { Options.default with stopOnFirstError := false, verbose := verboseMode, removeIrrelevantAxioms := true }
                                      (moreFns := Strata.Python.ReFactory)))
      let mut s := ""
      for vcResult in vcResults do
        -- Build location string based on available metadata
        let (locationPrefix, locationSuffix) := match Imperative.getFileRange vcResult.obligation.metadata with
          | some fr =>
            if fr.range.isNone then ("", "")
            else
              -- Convert byte offset to line/column if we have the source
              match pySourceOpt with
              | some (pyPath, fileMap) =>
                -- Check if this metadata is from the Python source (not CorePrelude)
                match fr.file with
                | .file path =>
                  if path == pyPath then
                    let pos := fileMap.toPosition fr.range.start
                    -- For failures, show at beginning; for passes, show at end
                    match vcResult.result with
                    | .fail => (s!"Assertion failed at line {pos.line}, col {pos.column}: ", "")
                    | _ => ("", s!" (at line {pos.line}, col {pos.column})")
                  else
                    -- From CorePrelude or other source, show byte offsets
                    match vcResult.result with
                    | .fail => (s!"Assertion failed at byte {fr.range.start}: ", "")
                    | _ => ("", s!" (at byte {fr.range.start})")
              | none =>
                match vcResult.result with
                | .fail => (s!"Assertion failed at byte {fr.range.start}: ", "")
                | _ => ("", s!" (at byte {fr.range.start})")
          | none => ("", "")
        s := s ++ s!"\n{locationPrefix}{vcResult.obligation.label}: {Std.format vcResult.result}{locationSuffix}\n"
      IO.println s

def javaGenCommand : Command where
  name := "javaGen"
  args := [ "dialect-file", "package", "output-dir" ]
  help := "Generate Java classes from a DDM dialect file."
  callback := fun fm v => do
    let (ld, pd) ← readFile fm v[0]
    match pd with
    | .dialect d =>
      match Strata.Java.generateDialect d v[1] with
      | .ok files =>
        Strata.Java.writeJavaFiles v[2] v[1] files
        IO.println s!"Generated Java files for {d.name} in {v[2]}/{Strata.Java.packageToPath v[1]}"
      | .error msg =>
        exitFailure s!"Error generating Java: {msg}"
    | .program _ =>
      exitFailure "Expected a dialect file, not a program file."

def deserializeIonToLaurelFiles (bytes : ByteArray) : IO (List Strata.StrataFile) := do
  match Strata.Program.filesFromIon Strata.Laurel.Laurel_map bytes with
  | .ok files => pure files
  | .error msg => exitFailure msg

def laurelAnalyzeCommand : Command where
  name := "laurelAnalyze"
  args := []
  help := "Analyze a Laurel Ion program from stdin. Write diagnostics to stdout."
  callback := fun _ _ => do
    -- Read bytes from stdin
    let stdinBytes ← (← IO.getStdin).readBinToEnd

    let strataFiles ← deserializeIonToLaurelFiles stdinBytes

    let mut combinedProgram : Strata.Laurel.Program := {
      staticProcedures := []
      staticFields := []
      types := []
    }

    for strataFile in strataFiles do

      let transResult := Strata.Laurel.TransM.run (Strata.Uri.file strataFile.filePath) (Strata.Laurel.parseProgram strataFile.program)
      match transResult with
      | .error transErrors => exitFailure s!"Translation errors in {strataFile.filePath}: {transErrors}"
      | .ok laurelProgram =>

        combinedProgram := {
          staticProcedures := combinedProgram.staticProcedures ++ laurelProgram.staticProcedures
          staticFields := combinedProgram.staticFields ++ laurelProgram.staticFields
          types := combinedProgram.types ++ laurelProgram.types
        }

    let diagnostics ← Strata.Laurel.verifyToDiagnosticModels "z3" combinedProgram

    IO.println s!"==== DIAGNOSTICS ===="
    for diag in diagnostics do
      IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"

def commandList : List Command := [
      javaGenCommand,
      checkCommand,
      toIonCommand,
      printCommand,
      diffCommand,
      pyAnalyzeCommand,
      pyTranslateCommand,
      laurelAnalyzeCommand,
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
