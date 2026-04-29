/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Elab
import Strata.DDM.Ion
import Strata.DDM.BuiltinDialects
public import Strata.DDM.Elab.LoadedDialects
import Strata.DDM.Util.Ion.Serialize
import Strata.DDM.Util.ByteArray
import Strata.DDM.Util.Lean

open Lean (Message)

public section
namespace Strata.Util

/-- Read from stdin if path is "-", otherwise read from file -/
def readInputSource (path : String) : IO String := do
  if path == "-" then
    let stdin ← IO.getStdin
    stdin.readToEnd
  else
    IO.FS.readFile path

/-- Read binary from stdin if path is "-", otherwise read from file -/
def readBinInputSource (path : String) : IO ByteArray := do
  if path == "-" then
    let stdin ← IO.getStdin
    stdin.readBinToEnd
  else
    IO.FS.readBinFile path

/-- Get display name for error messages: "<stdin>" if reading from stdin, otherwise the path -/
def displayName (path : String) : String :=
  if path == "-" then "<stdin>" else path

private def bytesToText {m} [Monad m] [MonadExcept String m] (path : System.FilePath) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s =>
    pure s
  | none =>
    throw s!"{path} is not an Ion file and contains non UTF-8 data"

private def fileReadErrorMsg (path : System.FilePath) (msg : String) : String :=
  s!"Error reading {path}:\n  {msg}\n" ++
  s!"Either the file is invalid or there is a bug in Strata."

private def mkErrorReport (path : System.FilePath) (errors : Array Lean.Message) : BaseIO String := do
  let msg : String := s!"{errors.size} error(s) reading {path}:\n"
  let msg ← errors.foldlM (init := msg) fun msg e =>
    return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
  return msg

/-- A `Dialect` or `Program`, used to represent the results of reading from a
Strata text or Ion file. Such a file can define either a dialect or a program.
-/
inductive DialectOrProgram
| dialect (d : Dialect)
| program (pgm : Program)

/-- Parse the textual representation of a Strata artifact from the given
`bytes`. The `DialectFileMap` is used to lazily load dialect definitions as
needed, when used by the artifact being parsed. The `path` argument specifies
the location of the file that `bytes` came from, but is used only for error
messages and metadata. -/
def readStrataText (fm : Strata.DialectFileMap) (path : System.FilePath) (bytes : ByteArray)
    : IO DialectOrProgram := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let contents ← match bytesToText path bytes with
    | Except.ok c => pure c
    | Except.error msg => throw (IO.userError (fileReadErrorMsg path msg))
  let inputContext := Strata.Parser.stringInputContext path contents
  let (header, errors, startPos) := Strata.Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    throw (IO.userError (← mkErrorReport path errors))
  match header with
  | .program _ dialect =>
    match ← Strata.Elab.loadDialect fm dialect with
    | .ok _ => pure ()
    | .error msg => throw (IO.userError msg)
    let dialects ← fm.getLoaded
    let .isTrue mem := (inferInstance : Decidable (dialect ∈ dialects.dialects))
      | panic! "internal: loadDialect failed"
    match Strata.Elab.elabProgramRest dialects leanEnv inputContext dialect mem startPos with
    | .ok program => pure (.program program)
    | .error errors => throw (IO.userError (← mkErrorReport path errors))
  | .dialect stx dialect =>
    if dialect ∈ (←fm.loaded.get).dialects then
      throw <| IO.userError s!"{dialect} already loaded"
    let (d, s) ←
      Strata.Elab.elabDialectRest fm inputContext stx dialect (startPos := startPos)
    if s.errors.size > 0 then
      throw (IO.userError (← mkErrorReport path s.errors))
    fm.modifyLoaded (·.addDialect! d)
    pure (.dialect d)

/-- Parse the Ion representation of a Strata artifact from the given `bytes`.
The `DialectFileMap` is used to lazily load dialect definitions as needed, when
used by the artifact being parsed. The `path` argument specifies the location of
the file that `bytes` came from, but is used only for error messages and
metadata. -/
def readStrataIon (fm : Strata.DialectFileMap)
    (path : System.FilePath) (bytes : ByteArray)
    : IO DialectOrProgram := do
  let (hdr, frag) ←
    match Strata.Ion.Header.parse bytes with
    | .error msg =>
      throw (IO.userError (fileReadErrorMsg path msg))
    | .ok p =>
      pure p
  match hdr with
  | .dialect dialect =>
    if dialect ∈ (←fm.loaded.get).dialects then
      throw <| IO.userError s!"{dialect} already loaded"
    match ← Strata.Elab.loadDialectFromIonFragment fm #[] dialect frag with
    | .error msg =>
      throw (IO.userError (fileReadErrorMsg path msg))
    | .ok d =>
      pure (.dialect d)
  | .program dialect => do
    match ← Strata.Elab.loadDialect fm dialect with
    | .ok _ => pure ()
    | .error msg => throw (IO.userError (fileReadErrorMsg path msg))
    let dialects ← fm.getLoaded
    let .isTrue mem := (inferInstance : Decidable (dialect ∈ dialects.dialects))
      | panic! "loadDialect failed"
    let dm := dialects.dialects.importedDialects dialect mem
    match Strata.Program.fromIonFragment frag dm dialect with
    | .ok pgm =>
      pure (.program pgm)
    | .error msg =>
      throw (IO.userError (fileReadErrorMsg path msg))

/-- Parse a Strata artifact from the file at the given `path`.  The
`DialectFileMap` is used to lazily load dialect definitions as needed, when used
by the artifact being parsed. -/
def readFile (fm : Strata.DialectFileMap) (path : System.FilePath) : IO DialectOrProgram := do
  let bytes ← readBinInputSource path.toString
  let displayPath : System.FilePath := displayName path.toString
  if Ion.isIonFile bytes then
    readStrataIon fm displayPath bytes
  else
    readStrataText fm displayPath bytes

end Strata.Util
end
