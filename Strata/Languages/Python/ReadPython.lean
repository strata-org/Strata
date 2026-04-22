/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Ion
public import Strata.Languages.Python.PythonDialect

public section
namespace Strata.Python

def readPythonStrataBytes (strataPath : String) (bytes : ByteArray) : Except String (Array (Strata.Python.stmt Strata.SourceRange)) := do
  if ! Ion.isIonFile bytes then
    throw <| s!"{strataPath} is not an Ion file."
  match Strata.Program.fromIon Strata.Python.Python_map Strata.Python.Python.name bytes with
  | .ok pgm =>
    let pyCmds ← pgm.commands.mapM fun cmd =>
      match Strata.Python.Command.ofAst cmd with
      | .error msg =>
        throw s!"Error reading {strataPath}: {msg}"
      | .ok r => pure r
    let isTrue p := (inferInstance : Decidable (pyCmds.size = 1))
      | throw s!"Error reading {strataPath}: Expected Python module"
    let .Module _ ⟨_, stmts⟩ _ := pyCmds[0]
      | throw s!"Error reading {strataPath}: Expected Python module"
    pure stmts
  | .error msg =>
    throw s!"Error reading {strataPath}: {msg}"

private def formatParseFailureStderr (stderr : String) : Option String := do
  match stderr.find? "Parse failure:\n" with
  | some idx =>
    match idx.find? "\n" with
    | some newLinePos =>
      let subs : Substring.Raw := {
        str := stderr
        startPos := newLinePos.offset
        stopPos := stderr.rawEndPos
      }
      some subs.trimLeft.toString
    | none => none
  | none => none


structure PythonToStrataOptions where
  logPerf : Bool := false
  extraPythonArgs : Array String := #[]

/-- Runs an action, logging its elapsed time to stderr if `options.logPerf` is set. -/
private def runWithOptions {α} (options : PythonToStrataOptions) (label : String)
    (action : EIO String α) : EIO String α := do
  if !options.logPerf then
    return ← action
  let start ← IO.monoNanosNow
  let result ← action
  let stop ← IO.monoNanosNow
  let elapsedMs := (stop - start) / 1000000
  let _ ← IO.eprintln s!"[perf] {label}: {elapsedMs}ms" |>.toBaseIO
  pure result

/-- Runs `python -m strata.gen py_to_strata` to convert a Python file into a Strata file. -/
private def runPyToStrata (pythonCmd : String) (extraPythonArgs : Array String)
    (dialectFile pythonFile strataFile : System.FilePath)
    : EIO String Unit := do
  let spawnArgs : IO.Process.SpawnArgs := {
      cmd := pythonCmd
      args := extraPythonArgs ++ #["-m", "strata.gen", "py_to_strata",
          "--dialect", dialectFile.toString,
          pythonFile.toString,
          strataFile.toString
        ]
      cwd := none
      inheritEnv := true
      stdin := .null
      stdout := .piped
      stderr := .piped
  }
  let child ←
          match ← IO.Process.spawn spawnArgs |>.toBaseIO with
          | .ok c => pure c
          | .error msg => throw s!"Could not run Python: {msg}"
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ←
        match ← child.stderr.readToEnd |>.toBaseIO with
        | .ok c => pure c
        | .error msg => throw s!"Could not read stderr from Python: {msg}"
  let exitCode ←
        match ← child.wait |>.toBaseIO with
        | .ok c => pure c
        | .error msg => throw s!"Could not wait for process exit code: {msg}"
  let stdout ←
        match stdout.get with
        | .ok c => pure c
        | .error msg => throw s!"Could not read stdout: {msg}"
  if exitCode = 100 then
    if let some msg := formatParseFailureStderr stderr then
      throw <| s!"{pythonFile} parse error:\n  {msg}"
  if exitCode ≠ 0 then
    let msg := s!"Internal: Python strata.gen failed (exitCode = {exitCode})\n"
    let msg := s!"{msg}Standard output:\n"
    let msg := stdout.splitOn.foldl (init := msg) fun msg ln => s!"{msg}  {ln}\n"
    let msg := s!"{msg}Standard error:\n"
    let msg := stderr.splitOn.foldl (init := msg) fun msg ln => s!"{msg}  {ln}\n"
    throw <| msg

/-- Reads a pre-compiled Strata file (Ion format) containing Python AST statements. -/
def readPythonStrata (strataPath : String) : EIO String (Array (Strata.Python.stmt Strata.SourceRange)) := do
  let bytes ←
    match ← IO.FS.readBinFile strataPath |>.toBaseIO with
    | .ok b =>
      pure b
    | .error msg =>
      throw <| s!"Error reading {strataPath}: {msg}"
  match readPythonStrataBytes strataPath bytes with
  | .ok r => pure r
  | .error msg => throw msg

/--
This runs `python -m strata.gen py_to_strata` to convert a
Python file into a Strata file, and then reads it in.

This function fails if the environment isn't configured correctly
or the Python file cannot be parsed.

-/
def pythonToStrata (dialectFile pythonFile : System.FilePath)
    (pythonCmd : String := "python")
    (options : PythonToStrataOptions := {})
    : EIO String (Array (Strata.Python.stmt Strata.SourceRange)) := do
  let (_handle, strataFile) ←
    match ← IO.FS.createTempFile |>.toBaseIO with
    | .ok p => pure p
    | .error msg =>
      throw s!"Cannot create temporary file: {msg}"
  try
    runWithOptions options s!"parsing {pythonFile}"
      (runPyToStrata pythonCmd options.extraPythonArgs
        dialectFile pythonFile strataFile)
    runWithOptions options s!"reading {pythonFile}" (readPythonStrata strataFile.toString)
  finally
    match ← IO.FS.removeFile strataFile |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => throw s!"Internal: Error deleting temp file {strataFile}: {msg}"


end Strata.Python
end
