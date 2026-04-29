/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DDM.Elab.DeclM
public import Strata.DDM.Ion

import Strata.DDM.Elab.DialectM
import Strata.DDM.BuiltinDialects
import Strata.DDM.Util.Ion.Serialize

import all Strata.DDM.Util.ByteArray
import all Strata.DDM.Util.Lean

open Lean (Message)
open Strata.Parser (InputContext)

public section
namespace Strata.Elab

namespace DeclState

private def initDeclState : DeclState :=
  let s : DeclState := {
    openDialects := #[]
    openDialectSet := {}
  }
  s.openLoadedDialect! .builtin initDialect

end DeclState

inductive Header where
| dialect (loc : SourceRange) (name : DialectName)
| program (loc : SourceRange) (name : DialectName)
deriving Inhabited

private inductive QuantifierSepState where
| outside
| inBinder
| sawColon

/--
Canonicalize the legacy dotted Unicode quantifier separator to `::` before DDM
parsing. This keeps `#strata` generic while accepting both `∀ x . P` and
`∀ x :: P`.
-/
private def normalizeUnicodeQuantifierSeparators (src : String) : String :=
  (src.foldl
    (init := ("", QuantifierSepState.outside))
    (fun (st : String × QuantifierSepState) (ch : Char) =>
      let (acc, qstate) := st
      match qstate with
      | .outside =>
        if ch == '∀' || ch == '∃' then
          (acc.push ch, .inBinder)
        else
          (acc.push ch, .outside)
      | .inBinder =>
        if ch == '.' then
          (acc ++ "::", .outside)
        else if ch == ':' then
          (acc.push ch, .sawColon)
        else
          (acc.push ch, .inBinder)
      | .sawColon =>
        if ch == ':' then
          (acc.push ch, .outside)
        else
          (acc.push ch, .inBinder))).fst

private def normalizeInputContext (inputContext : InputContext) : InputContext :=
  let inputString := normalizeUnicodeQuantifierSeparators inputContext.inputString
  Strata.Parser.stringInputContext (System.FilePath.mk inputContext.fileName) inputString

private def normalizedQuantifierSepStep (state : QuantifierSepState) (ch : Char) : Nat × QuantifierSepState :=
  match state with
  | .outside =>
    if ch == '∀' || ch == '∃' then
      (ch.utf8Size, .inBinder)
    else
      (ch.utf8Size, .outside)
  | .inBinder =>
    if ch == '.' then
      ("::".utf8ByteSize, .outside)
    else if ch == ':' then
      (ch.utf8Size, .sawColon)
    else
      (ch.utf8Size, .inBinder)
  | .sawColon =>
    if ch == ':' then
      (ch.utf8Size, .outside)
    else
      (ch.utf8Size, .inBinder)

/--
Translate a byte position in the original input to the corresponding byte
position in the normalized input after quantifier-separator canonicalization.

This matters for interior positions as well as `endPos`, because replacing `.`
with `::` inside binders lengthens the input by one byte at each rewrite site.
-/
private def normalizePos (src : String) (targetPos : String.Pos.Raw) : String.Pos.Raw := Id.run do
  let mut origPos : String.Pos.Raw := 0
  let mut normPos : String.Pos.Raw := 0
  let mut state := QuantifierSepState.outside
  while targetPos > origPos && origPos < src.rawEndPos do
    let ch := origPos.get src
    let origNext := origPos.next src
    let (normWidth, nextState) := normalizedQuantifierSepStep state ch
    origPos := origNext
    normPos := ⟨normPos.byteIdx + normWidth⟩
    state := nextState
  return normPos

/- Elaborate a Strata program -/
partial def elabHeader
    (leanEnv : Lean.Environment)
    (inputContext : InputContext)
    (startPos : String.Pos.Raw := 0)
    (stopPos : String.Pos.Raw := inputContext.endPos)
     : Header × Array Message × String.Pos.Raw :=
  let s : DeclState := .initDeclState
  let s := s.openLoadedDialect! .builtin headerDialect
  let s := { s with pos := startPos }
  let ctx := { inputContext := inputContext, stopPos := stopPos, loader := .builtin, missingImport := false }
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
        | "dialectCommand" => .dialect cmd.loc name.val
        | "programCommand" => .program cmd.loc name.val
        | _ => panic! s!"Unknown command {cmd.op.name}"
      (header, #[], s.pos)
  else
    (default, s.errors, 0)

private partial def runCommand (leanEnv : Lean.Environment) (commands : Array Operation) (stopPos : String.Pos.Raw) : DeclM (Array Operation) := do
  let iniPos := (←get).pos
  if iniPos >= stopPos then
    return commands
  let (some tree, true) ← runChecked <| elabCommand leanEnv
    | return commands
  -- Prevent infinite loop if parser makes no progress
  let newPos := (←get).pos
  if newPos <= iniPos then
    logError { start := iniPos, stop := iniPos } "Syntax error: unrecognized syntax or unexpected token"
    return commands
  let opInfo := tree.info.asOp!
  let cmd := opInfo.op
  let dialects := (← read).loader.dialects
  let s ← get
  match s.globalContext.addCommand dialects cmd with
  | .ok newGctx =>
    modify fun s => { s with globalContext := newGctx }
    runCommand leanEnv (commands.push cmd) stopPos
  | .error e =>
    logError opInfo.loc e
    runCommand leanEnv commands stopPos

def elabProgramRest
    (loader : LoadedDialects)
    (leanEnv : Lean.Environment)
    (inputContext : InputContext)
    (dialect : DialectName)
    (known : dialect ∈ loader.dialects)
    (startPos : String.Pos.Raw)
    (stopPos : String.Pos.Raw := inputContext.endPos)
    : Except (Array Message) Program := do
  let d := loader.dialects[dialect]
  let s := DeclState.initDeclState
  let s := { s with pos := startPos }
  let s := s.openLoadedDialect! loader d
  let ctx : DeclContext := { inputContext, stopPos, loader := loader, missingImport := false }
  let (cmds, s) := runCommand leanEnv #[] stopPos ctx s
  if s.errors.isEmpty then
    let openDialects := loader.dialects.importedDialects dialect known
    .ok <| .create openDialects dialect cmds
  else
    .error s.errors

/- Elaborate a Strata program -/
def elabProgram
    (loader : LoadedDialects)
    (leanEnv : Lean.Environment)
    (inputContext : InputContext)
    (startPos : String.Pos.Raw := 0)
    (stopPos : String.Pos.Raw := inputContext.endPos) : Except (Array Message) Program :=
  let originalInputContext := inputContext
  let inputContext := normalizeInputContext inputContext
  let startPos := normalizePos originalInputContext.inputString startPos
  let stopPos := normalizePos originalInputContext.inputString stopPos
  assert! "Init" ∈ loader.dialects
  let (header, errors, startPos) := elabHeader leanEnv inputContext startPos stopPos
  if errors.size > 0 then
    .error errors
  else
    match header with
    | .dialect loc _ =>
      .error #[Lean.mkStringMessage inputContext loc.start "Expected program name"]
    | .program loc dialect => do
      if p : dialect ∈ loader.dialects then
        elabProgramRest loader leanEnv inputContext dialect p startPos stopPos
      else
        .error #[Lean.mkStringMessage inputContext loc.start s!"Unknown dialect {dialect}."]

private def asText{m} [Monad m] [MonadExcept String m] (path : System.FilePath) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s =>
    pure s
  | none =>
    throw s!"{path} is not an Ion file and contains non UTF-8 data"

def mkErrorReport (errors : Array Lean.Message) : BaseIO String :=
  -- Build map from filenames to errors:
  let m : Std.HashMap String (Array Lean.Message) := errors.foldl (init := {}) fun m e =>
    if e.isSilent then
      m
    else
      m.alter e.fileName fun o => o.getD #[] |>.push e
  m.foldM (init := "") fun msg path a =>
    let msg : String := s!"{msg}{a.size} error(s) in {path}:\n"
    a.foldlM (init := msg) fun msg e =>
      return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"

private def checkDialectName (ld : LoadedDialects) (actual : DialectName) (expected : Option DialectName) : Except String Unit :=
  match expected with
  | .none =>
    if actual ∈ ld.dialects then
      .error s!"Dialect {actual} already loaded."
    else
      .ok ()
  | some expected =>
    if actual = expected then
      .ok ()
    else
      .error s!"Dialect header name of {actual} does not match expected name {expected}."

/--
Create a Lean.Message without position information from parsing a binary.
-/
private def mkBinaryMessage (fileName : System.FilePath) (msg : Lean.MessageData) : Lean.Message :=
  {
    fileName := fileName.toString
    pos := { line := 0, column := 0 }
    data := msg
  }

/--
Parse the header of a text dialect file. Returns the input context,
dialect name location, dialect name, and the position after the header
on success.
-/
private def readDialectTextfileHeader
    (input : System.FilePath)
    (contents : String)
    : BaseIO (Except (Array Message)
        (Parser.InputContext × SourceRange × DialectName
          × String.Pos.Raw)) := do
  let inputContext := Strata.Parser.stringInputContext input contents
  let leanEnv ←
    match ← (Lean.mkEmptyEnvironment 0) |>.toBaseIO with
    | .ok e => pure e
    | .error _ =>
      return .error #[Lean.mkStringMessage inputContext 0
        "Internal error: Failed to create Lean environment"]
  let (header, errors, startPos) := Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    return .error errors
  match header with
  | .program loc _ =>
    let msg := Lean.mkStringMessage inputContext loc.start
      s!"Expected dialect."
    return .error #[msg]
  | .dialect loc dialect =>
    return .ok (inputContext, loc, dialect, startPos)

mutual

partial def loadDialectFromIonFragment
    (fm : DialectFileMap)
    (stk : Array DialectName)
    (dialect : DialectName)
    (frag : Ion.Fragment)

  : BaseIO (Except String Dialect) := do
  if dialect ∈ (←fm.loaded.get).dialects then
    return .error s!"{dialect} already loaded"
  -- Read dialect from Ion fragment
  let d ←
    match Dialect.fromIonFragment dialect frag with
    | .error msg =>
      return .error msg
    | .ok d =>
      pure d
  -- Push dialect name to stack to catch recursive imports
  let stk := stk.push dialect
  -- Iterate through imports and ensure they are loaded.
  for i in d.imports do
    match ← loadDialectRec fm stk i with
    | .error msg =>
      return .error msg
    | .ok _ =>
      pure ()
  -- Add this dialect to loaded dialects and return it.
  fm.modifyLoaded (·.addDialect! d)
  return .ok d

/--
Loads a dialect from a file path.

The expected name of the dialect can be provided if the file is expected
to contain a particular dialect.

An actual path can be provided if we want to use one path for reading from disk and another
for error reporting.
-/
private partial def loadDialectFromPath
  (fm : DialectFileMap)
  (stk : Array DialectName)
  (path : System.FilePath)
  (actualPath : System.FilePath := path)
  (expected : Option DialectName := none) :
  BaseIO (Except (Array Message) Strata.Dialect) := do
  let bytes ←
    match ← IO.FS.readBinFile actualPath |>.toBaseIO with
    | .error _ =>
      return .error #[mkBinaryMessage path s!"Error reading {path}."]
    | .ok c =>
      pure c
  let ld ← fm.getLoaded
  if bytes.startsWith Ion.binaryVersionMarker then
    match Ion.Header.parse bytes with
    | .error msg =>
      return .error #[mkBinaryMessage path msg]
    | .ok (hdr, frag) =>
      let dialect ←
        match hdr with
        | .program _ =>
          return .error #[mkBinaryMessage path s!"Expected dialect"]
        | .dialect dialect =>
          pure dialect
      if let .error msg := checkDialectName ld dialect expected then
        return .error #[mkBinaryMessage path msg]
      match ← loadDialectFromIonFragment fm stk dialect frag with
      | .error msg =>
        pure (.error #[mkBinaryMessage path msg])
      | .ok r =>
        pure (.ok r)
  else do
    let contents ←
      match String.fromUTF8? bytes with
      | none =>
        return .error #[mkBinaryMessage path s!"Not an Ion file and contains non UTF-8 data"]
      | some contents =>
        pure contents
    let (inputContext, loc, dialect, startPos) ←
      match ← readDialectTextfileHeader path contents with
      | .error msgs => return .error msgs
      | .ok result => pure result
    let ld ← fm.getLoaded
    if let .error msg := checkDialectName ld dialect expected then
      return .error #[Lean.mkStringMessage inputContext loc.start msg]
    -- Elaborate the dialect body and add it to loaded dialects.
    let stk := stk.push dialect
    let (d, s) ← Elab.elabDialectRest fm inputContext loc dialect (stk := stk) (startPos := startPos)
    if s.errors.size > 0 then
      pure <| .error s.errors
    else
      fm.modifyLoaded (·.addDialect! d)
      pure <| .ok d

private partial def loadDialectRec
  (fm : DialectFileMap)
  (stk : Array DialectName)
  (name : DialectName) :
  BaseIO (Except String Dialect) := do
  let ld ← fm.getLoaded
  if p : name ∈ ld.dialects then
    pure (.ok ld.dialects[name])
  else
    let path ←
          match fm.findPath name with
          | none => return .error s!"Unknown dialect {name}"
          | some path => pure path
    match ← loadDialectFromPath fm stk path (expected := some name) with
    | .ok d => return .ok d
    | .error a =>
      return .error (← mkErrorReport a)

/--
Elaborate a dialect after the initial header with the name of dialect
has been processed.
-/
partial def elabDialectRest
      (fm : DialectFileMap)
      (inputContext : Parser.InputContext)
      (loc : SourceRange)
      (dialect : DialectName)
      (stk : Array DialectName := #[])
      (startPos : String.Pos.Raw := 0)
      (stopPos : String.Pos.Raw := inputContext.endPos)
      : BaseIO (Dialect × DeclState) := do
  let dialects ← fm.getLoaded
  let leanEnv ←
    match ← Lean.mkEmptyEnvironment 0 |>.toBaseIO with
    | .ok env => pure env
    | .error _ =>
      let m : Message := Lean.mkStringMessage inputContext 0 "Failed to create Lean environment."
      return (default, { errors := #[m] })

  assert! "StrataDDL" ∈ dialects.dialects
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
        if dialect ∈ (← getLoadedDialects).dialects then
          logError loc s!"Dialect {dialect} already declared."
        else
          run
  let dctx : DialectContext := {
    loadDialect := fun name =>
      loadDialectRec fm stk name
    loadedRef := fm.loaded
    inputContext := inputContext
    stopPos := stopPos
  }
  let ds : DialectState := {
    declState := s
    dialect := {
        name := dialect,
        imports := #[initDialect.name]
    },
    missingImport := false
  }
  let ((), ds) ← act dctx |>.run ds
  pure (ds.dialect, ds.declState)

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
  (dialect : Strata.DialectName) :
  BaseIO (Except String Strata.Dialect) := do
  loadDialectRec fm #[] dialect

/--
Load a dialect from a file, using `actualPath` for reading and `path`
for error reporting. Returns the loaded dialect or an array of error
messages.
-/
partial def loadDialectFromFile
  (fm : DialectFileMap)
  (path : System.FilePath)
  (actualPath : System.FilePath := path) :
  BaseIO (Except (Array Message) Strata.Dialect) :=
  loadDialectFromPath fm #[] path (actualPath := actualPath)

/- Elaborate a Strata dialect definition. -/
def elabDialect
    (fm : DialectFileMap)
    (inputContext : Parser.InputContext)
    (startPos : String.Pos.Raw := 0)
    (stopPos : String.Pos.Raw := inputContext.endPos)
     : BaseIO (Dialect × DeclState) := do
  let leanEnv ←
    match ← Lean.mkEmptyEnvironment 0 |>.toBaseIO with
    | .ok env => pure env
    | .error _ =>
      let m : Message := Lean.mkStringMessage inputContext 0 "Failed to create Lean environment."
      return (default, { errors := #[m] })
  let (header, errors, startPos) := elabHeader leanEnv inputContext startPos stopPos
  if errors.size > 0 then
    return (default, { errors := errors })
  match header with
  | .program loc _ =>
    let msg := Lean.mkStringMessage inputContext loc.start "Expected dialect name"
    return (default, { errors := #[msg] })
  | .dialect loc dialect =>
    elabDialectRest fm inputContext loc dialect (startPos := startPos) (stopPos := stopPos)

def parseStrataProgramFromDialect (dialects : LoadedDialects) (dialect : DialectName) (input : InputContext) : IO Strata.Program := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let originalInput := input
  let input := normalizeInputContext input

  let isTrue mem := (inferInstance : Decidable (dialect ∈ dialects.dialects))
    | throw <| IO.userError "Internal {dialect} missing from loaded dialects."

  let strataProgram ←
    match elabProgramRest dialects leanEnv input dialect mem 0 (normalizePos originalInput.inputString input.endPos) with
    | .ok program =>
      pure program
    | .error errors =>
      let errMsg ← errors.foldlM (init := "Parse errors:\n") fun msg e =>
        return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
      throw (IO.userError errMsg)

/--
Parse a single syntax category from a loaded dialect set.

Unlike `parseStrataProgramFromDialect`, this targets a specific syntax
category (e.g. `q\`SMTResponse.GetValueResponse`) rather than parsing a
full program of `Command`s. This avoids ambiguity issues that arise when
multiple categories share the same surface syntax.

Returns the elaborated `Operation` on success.
-/
def parseCategoryFromDialect
    (dialects : LoadedDialects) (cat : QualifiedIdent) (input : InputContext)
    (startPos : String.Pos.Raw := 0)
    (stopPos : String.Pos.Raw := input.endPos)
    : IO Strata.Operation := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let originalInput := input
  let input := normalizeInputContext input
  let startPos := normalizePos originalInput.inputString startPos
  let stopPos := normalizePos originalInput.inputString stopPos
  -- Open dialects using the same pattern as elabProgramRest: start from
  -- initDeclState (which has Init open) and open each dialect via
  -- ensureLoaded! to avoid panics from HashMap iteration order.
  let s := DeclState.initDeclState
  let s := dialects.dialects.toList.foldl (init := s) fun s d =>
    DeclState.ensureLoaded! s dialects d.name
  -- Run the category-level parser
  let ps := Parser.runCatParser s.tokenTable s.parserMap leanEnv input startPos stopPos cat
  if ps.hasError then
    let errMsg ← ps.allErrors.foldlM (init := "Parse errors:\n") fun msg (pos, stk, err) =>
      let m := Lean.mkErrorMessage input pos stk err
      return s!"{msg}  {m.pos.line}:{m.pos.column}: {← m.data.toString}\n"
    throw (IO.userError errMsg)
  if ps.stxStack.size == 0 then
    throw (IO.userError "Parser returned no syntax")
  let stx := ps.stxStack.back
  -- Elaborate the parsed syntax into an Operation
  let ctx : ElabContext := {
    dialects := dialects.dialects
    syntaxElabs := dialects.syntaxElabMap
    openDialectSet := s.openDialectSet
    typeOrCatDeclMap := s.typeOrCatDeclMap
    metadataDeclMap := s.metadataDeclMap
    globalContext := s.globalContext
    inputContext := input
    missingImport := false
  }
  let es : ElabState := {}
  let (tree, es) := elabOperation (.empty s.globalContext) stx ctx es
  if es.errors.size > 0 then
    let errMsg ← es.errors.foldlM (init := "Elaboration errors:\n") fun msg e =>
      return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
    throw (IO.userError errMsg)
  let op := tree.info.asOp!.op
  return op

end Strata.Elab
end
