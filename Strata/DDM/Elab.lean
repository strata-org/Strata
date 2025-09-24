/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab.DialectM
import Strata.DDM.BuiltinDialects.StrataDDL
import Strata.DDM.BuiltinDialects.StrataHeader
import Strata.DDM.Util.ByteArray
import Strata.DDM.Ion

open Lean (
    Message
    Name
    Syntax
    SyntaxNodeKind
    TSyntax
    TSyntaxArray
    MacroM
    quote
    nullKind
  )

open Strata.Parser (DeclParser InputContext ParsingContext ParserState)

namespace Strata

open Lean

namespace Elab

namespace LoadedDialects

def builtin : LoadedDialects := .ofDialects! #[initDialect, headerDialect, StrataDDL]

end LoadedDialects

namespace DeclState

def initDeclState : DeclState :=
  let s : DeclState := {
    openDialects := #[]
    openDialectSet := {}
  }
  s.openLoadedDialect! .builtin initDialect

end DeclState

inductive Header where
| dialect (stx : Syntax) (name : DialectName)
| program (stx : Syntax) (name : DialectName)
deriving Inhabited

/- Elaborate a Strata program -/
partial def elabHeader
    (leanEnv : Lean.Environment)
    (inputContext : InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos)
     : Header × Array (Syntax × Message) × String.Pos :=
  let s : DeclState := .initDeclState
  let s := s.openLoadedDialect! .builtin headerDialect
  let s := { s with pos := startPos }
  let ctx := { inputContext := inputContext, stopPos := stopPos, loader := .builtin }
  let (mtree, s) := elabCommand leanEnv ctx s
  if s.errors.isEmpty then
    match mtree with
    | none => panic! "Missing tree"
    | some tree =>
      let cmd := tree.info.asOp!
      assert! tree.children.size = 1
      let name := tree[0]!.info.asIdent!
      let header :=
        match cmd.op.name.name with
        | "dialectCommand" => .dialect cmd.stx name.val
        | "programCommand" => .program cmd.stx name.val
        | _ => panic! s!"Unknown command {cmd.op.name}"
      (header, #[], s.pos)
  else
    (default, s.errors, 0)

partial def runCommand (leanEnv : Lean.Environment) (commands : Array Operation) (stopPos : String.Pos) : DeclM (Array Operation) := do
  let iniPos := (←get).pos
  if iniPos >= stopPos then
    return commands
  let (some tree, true) ← runChecked <| elabCommand leanEnv
    | return commands
  let cmd := tree.info.asOp!.op
  let dialects := (← read).loader.dialects
  modify fun s => { s with
    globalContext := s.globalContext.addCommand dialects cmd
  }
  runCommand leanEnv (commands.push cmd) stopPos

def elabProgramRest
    (loader : LoadedDialects)
    (leanEnv : Lean.Environment)
    (inputContext : InputContext)
    (stx : Lean.Syntax)
    (dialect : DialectName)
    (startPos : String.Pos)
    (stopPos : String.Pos := inputContext.input.endPos)
    : Except (Array (Syntax × Message)) Program := do
  let some d := loader.dialects[dialect]?
    | let pos := stx.getPos? |>.getD 0
      .error #[(stx, Lean.mkStringMessage inputContext pos s!"Unknown dialect {dialect}.")]
  let s := DeclState.initDeclState
  let s := { s with pos := startPos }
  let s := s.openLoadedDialect! loader d
  let ctx : DeclContext := { inputContext, stopPos, loader := loader }
  let (cmds, s) := runCommand leanEnv #[] stopPos ctx s
  if s.errors.isEmpty then
    let openDialects := loader.dialects.importedDialects! dialect
    .ok <| .create openDialects dialect cmds
  else
    .error s.errors

/- Elaborate a Strata program -/
partial def elabProgram
    (loader : LoadedDialects)
    (leanEnv : Lean.Environment)
    (inputContext : InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos) : Except (Array (Syntax × Message)) Program :=
  assert! "Init" ∈ loader.dialects
  let (header, errors, startPos) := elabHeader leanEnv inputContext startPos stopPos
  if errors.size > 0 then
    .error errors
  else
    match header with
    | .dialect stx _ =>
      let pos := stx.getPos? |>.getD 0
      .error #[(stx, Lean.mkStringMessage inputContext pos "Expected program name")]
    | .program stx dialect => do
      elabProgramRest loader leanEnv inputContext stx dialect startPos stopPos

private def asText{m} [Monad m] [MonadExcept String m] (path : System.FilePath) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s =>
    pure s
  | none =>
    throw s!"{path} is not an Ion file and contains non UTF-8 data"

private def mkErrorReport (path : System.FilePath) (errors : Array (Lean.Syntax × Lean.Message)) : BaseIO String := do
  let msg : String := s!"{errors.size} error(s) reading {path}:\n"
  let msg ← errors.foldlM (init := msg) fun msg (_, e) =>
    return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
  return toString msg

private def checkDialectName (ld : LoadedDialects) (actual : DialectName) (expected : Option DialectName) : Except String Unit :=
  match expected with
  | .none =>
    if actual ∈ ld.dialects then
      .error s!"Dialect {actual} already loaded."
    else
      .ok ()
  | some expected =>
    if actual = expected then
      assert! expected ∉ ld.dialects
      .ok ()
    else
      .error s!"Dialect header name of {actual} does not match expected name {expected}."

mutual

partial def loadDialectFromIonFragment
    (fm : DialectFileMap)
    (ld : LoadedDialects)
    (stk : Array DialectName)
    (dialect : DialectName)
    (frag : Ion.Fragment)
  : BaseIO (LoadedDialects × Except String Dialect) := do
  -- Read dialect from Ion fragment
  let d ←
    match Dialect.fromIonFragment dialect frag with
    | .error msg =>
      return (ld, .error msg)
    | .ok d =>
      pure d
  -- Push dialect name to stack to catch recursive imports
  let stk := stk.push dialect
  -- Iteratre through imports and ensure they are loaded.
  let mut ld := ld
  for i in d.imports do
    let (ld', r) ← loadDialectRec fm ld stk i
    ld := ld'
    match r with
    | .error msg =>
      return (ld, .error msg)
    | .ok _ =>
      pure ()
  -- Add this dialect to loaded dialects and return it.
  ld := ld.addDialect! d
  return (ld, .ok d)

/--
Loads a dialect from a file path.

The expected name of the dialect can be provided if the file is expected
to contain a particular dialect.

An actual path can be provided if we want to use one path for reading from disk and another
for error reporting.
-/
partial def loadDialectFromPath
  (fm : DialectFileMap)
  (ld : LoadedDialects)
  (stk : Array DialectName)
  (path : System.FilePath)
  (actualPath : System.FilePath := path)
  (expected : Option { d : DialectName // d ∉ ld.dialects } := none) :
  BaseIO (LoadedDialects × Except String Strata.Dialect) := do
  let bytes ←
    match ← IO.FS.readBinFile actualPath |>.toBaseIO with
    | .error _ =>
      return (ld, .error s!"Error reading {path}.")
    | .ok c =>
      pure c
  if bytes.startsWith Ion.binaryVersionMarker then
    match Ion.Header.parse bytes with
    | .error msg =>
      return (ld, .error msg)
    | .ok (hdr, frag) =>
      let dialect ←
        match hdr with
        | .program _ =>
          return (ld, .error s!"Expected dialect")
        | .dialect dialect =>
          pure dialect
      if let .error msg := checkDialectName ld dialect expected then
        return (ld, .error msg)
      loadDialectFromIonFragment fm ld stk dialect frag
  else do
    let contents ←
      match String.fromUTF8? bytes with
      | none =>
        return (ld, .error s!"{path} is not an Ion file and contains non UTF-8 data")
      | some contents =>
        pure contents
    readDialectTextfile fm ld stk path contents (expected := expected)

partial def loadDialectRec
  (fm : DialectFileMap)
  (ld : LoadedDialects)
  (stk : Array DialectName)
  (name : DialectName) :
  BaseIO (Elab.LoadedDialects × Except String Dialect) := do
  if p : name ∈ ld.dialects then
    return (ld, .ok ld.dialects[name])
  else
    let path ←
          match fm.findPath name with
          | none => return (ld, .error s!"Unknown dialect {name}")
          | some path => pure path
    loadDialectFromPath fm ld stk path (expected := some ⟨name, p⟩)

private partial
def readDialectTextfile
    (fm : DialectFileMap)
    (ld : LoadedDialects)
    (stk : Array DialectName := #[])
    (input : System.FilePath)
    (contents : String)
    (expected : Option DialectName := none) : BaseIO (LoadedDialects × Except String Dialect) := do
  let inputContext := Strata.Parser.stringInputContext contents
  let leanEnv ←
    match ← (Lean.mkEmptyEnvironment 0) |>.toBaseIO with
    | .ok e => pure e
    | .error _ => return (ld, .error "Internal error: Failed to create Lean environment")
  let (header, errors, startPos) := Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    return (ld, .error (← mkErrorReport input errors))
  match header with
  | .program stx _ =>
    let pos := stx.getPos? |>.getD 0
    return (ld, .error s!"{pos}: Expected dialect.")
  | .dialect stx dialect =>
    if let .error msg := checkDialectName ld dialect expected then
      return (ld, .error msg)
    let stk := stk.push dialect
    let (ld, d, s) ← Elab.elabDialectRest fm ld stk inputContext stx dialect startPos
    if s.errors.size > 0 then
      let msg ← mkErrorReport input s.errors
      pure (ld, .error (toString msg))
    else
      pure (ld.addDialect! d, .ok d)

/--
Elaborate a dialect after the initial header with the name of dialect
has been processed.
-/
partial def elabDialectRest
      (fm : DialectFileMap)
      (dialects : LoadedDialects)
      (stk : Array DialectName)
      (inputContext : Parser.InputContext)
      (stx : Syntax)
      (dialect : DialectName)
      (startPos : String.Pos := 0)
      (stopPos : String.Pos := inputContext.input.endPos)
      : BaseIO (LoadedDialects × Dialect × DeclState) := do
  let leanEnv ←
    match ← mkEmptyEnvironment 0 |>.toBaseIO with
    | .ok env => pure env
    | .error _ =>
      let m : Message := mkStringMessage inputContext 0 "Failed to create Lean environment."
      return (dialects, default, { errors := #[(.missing, m)] })

  assert! "StrataDDL" ∈ dialects.dialects.map
  let rec run : DialectM Unit := do
        let iniPos := (←getDeclState).pos
        if iniPos >= stopPos then
          return
        let c ← runDialectCommand leanEnv
        if c then
          run
  let s := DeclState.initDeclState
  let s := s.openParserDialect! dialects StrataDDL
  let s := { s with
    pos := startPos
    openDialectSet := s.openDialectSet.insert dialect
  }
  let act : DialectM Unit := do
        if dialect ∈ (← get).loaded.dialects then
          logError stx[1] s!"Dialect {dialect} already declared."
        else
          run
  let dctx : DialectContext := {
    loadDialect := fun ld name =>
      loadDialectRec fm ld stk name
    inputContext := inputContext
    stopPos := stopPos
  }
  let ds : DialectState := {
    declState := s
    dialect := {
        name := dialect,
        imports := #[initDialect.name]
    },
    loaded := dialects
  }
  let ((), ds) ← act dctx |>.run ds
  pure (ds.loaded, ds.dialect, ds.declState)

end

/--
Use `fm` to ensure `dialect` and all of its imports are loaded into `ld`.

This always returns a new loaded dialect map as some imports may be loaded
successfully before a failure.  It returns either an error message as a
string or a dialect.

N.B.  We may need to amend the error message in the future to provide
more structure (such as error location information).
-/
partial def loadDialect
  (fm : DialectFileMap)
  (ld : LoadedDialects)
  (dialect : Strata.DialectName) :
  BaseIO (Elab.LoadedDialects × Except String Strata.Dialect) := do

  loadDialectRec fm ld #[] dialect

/- Elaborate a Strata dialect definition. -/
def elabDialect
    (fm : DialectFileMap)
    (dialects : LoadedDialects)
    (inputContext : Parser.InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos)
     : BaseIO (LoadedDialects × Dialect × DeclState) := do
  let leanEnv ←
    match ← mkEmptyEnvironment 0 |>.toBaseIO with
    | .ok env => pure env
    | .error _ =>
      let m : Message := Lean.mkStringMessage inputContext 0 "Failed to create Lean environment."
      return (dialects, default, { errors := #[(.missing, m)] })
  let (header, errors, startPos) := elabHeader leanEnv inputContext startPos stopPos
  if errors.size > 0 then
    return (dialects, default, { errors := errors })
  match header with
  | .program stx _ =>
    let pos := stx.getPos? |>.getD 0
    let msg := Lean.mkStringMessage inputContext pos "Expected dialect name"
    return (dialects, default, { errors := #[(stx, msg)] })
  | .dialect stx dialect =>
    elabDialectRest fm dialects #[] inputContext stx dialect startPos stopPos

end Strata.Elab
