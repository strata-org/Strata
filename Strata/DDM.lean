/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.IO
public import StrataDDM.Elab.LoadedDialects
public import StrataDDM.Ion
import StrataDDM.Elab
import StrataDDM.Util.Ion
import StrataDDM.BuiltinDialects
import StrataDDM.AST.Lemmas -- shake: keep
import StrataDDM.Integration.Java -- shake: keep

/-! ## Strata DDM API

File I/O for reading and writing Strata programs in textual or Ion format.
-/

open Lean (Message)

public section

namespace Strata

/-! ### DialectFileMap construction -/

/--
Build a `DialectFileMap` preloaded with the given dialects (plus the built-in
DDM dialects: `init`, `header`, and `StrataDDL`). Use this to construct a
`DialectFileMap` opaquely without touching DDM internals.
-/
def mkDialectFileMap (dialects : Array Strata.Dialect := #[])
    : IO Strata.DialectFileMap := do
  let mut loaded := Strata.Elab.LoadedDialects.builtin
  for d in dialects do
    loaded := loaded.addDialect! d
  Strata.DialectFileMap.new loaded

/--
Register a directory to search for dialect definition files
(`.dialect.st` / `.dialect.st.ion`). Returns an updated `DialectFileMap`.
-/
def DialectFileMap.addSearchPath (fm : Strata.DialectFileMap)
    (dir : System.FilePath) : EIO String Strata.DialectFileMap :=
  fm.add dir

/-! ### File I/O -/

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

/--
Parse a Strata dialect or program in textual format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
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

/--
Parse a Strata dialect or program in Ion format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
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

/--
Parse a Strata dialect or program in either textual or Ion format, possibly
loading other dialects as needed along the way. The `DialectFileMap` indicates
where to find the definitions of other dialects. The `FilePath` indicates the name
of the file to be loaded.
-/
def readStrataFile (fm : Strata.DialectFileMap) (path : System.FilePath)
    : IO DialectOrProgram := do
  let bytes ← Strata.Util.readBinInputSource path.toString
  let displayPath : System.FilePath := Strata.Util.displayName path.toString
  if Ion.isIonFile bytes then
    readStrataIon fm displayPath bytes
  else
    readStrataText fm displayPath bytes

/--
Read a Strata file (text or Ion) and require it to be a program. Fails if the
file defines a dialect.
-/
def readStrataProgramFile (fm : Strata.DialectFileMap) (path : System.FilePath)
    : IO Strata.Program := do
  match ← readStrataFile fm path with
  | .program pgm => pure pgm
  | .dialect _ => throw (IO.userError s!"Expected a program file, got a dialect: {path}")

/--
Read a Strata file (text or Ion) and require it to be a dialect. Fails if the
file defines a program.
-/
def readStrataDialectFile (fm : Strata.DialectFileMap) (path : System.FilePath)
    : IO Strata.Dialect := do
  match ← readStrataFile fm path with
  | .dialect d => pure d
  | .program _ => throw (IO.userError s!"Expected a dialect file, got a program: {path}")

/--
Serialize a Strata program in textual format. Returns a byte array rather than
writing directly to a file.
-/
def writeStrataText : Strata.Program → ByteArray
| pgm => String.toByteArray pgm.toString

/--
Serialize a Strata program in Ion format. Returns a byte array rather than
writing directly to a file.
-/
def writeStrataIon : Strata.Program → ByteArray
| pgm => pgm.toIon

end Strata

end -- public section
