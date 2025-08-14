/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab.DialectM
import Strata.DDM.BuiltinDialects.StrataDDL
import Strata.DDM.BuiltinDialects.StrataHeader

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

def elabProgramRest (loader : LoadedDialects) (leanEnv : Lean.Environment)
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

/--
Elaborate a dialect after the initial header with the name of dialect
has been processed.
-/
partial def elabDialectRest
      (leanEnv : Lean.Environment)
      (loadCallback : LoadDialectCallback)
      (dialects : LoadedDialects)
      (inputContext : Parser.InputContext)
      (stx : Syntax)
      (dialect : DialectName)
      (startPos : String.Pos := 0)
      (stopPos : String.Pos := inputContext.input.endPos)
      : BaseIO (Dialect × DeclState × LoadedDialects) := do
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
    loadDialect := loadCallback
    inputContext := inputContext,
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
  pure (ds.dialect, ds.declState, ds.loaded)

/- Elaborate a Strata dialect definition. -/
def elabDialect
    (leanEnv : Lean.Environment)
    (loadCallback : LoadDialectCallback)
    (dialects : LoadedDialects)
    (inputContext : Parser.InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos)
     : BaseIO (Dialect × DeclState × LoadedDialects) := do
  let (header, errors, startPos) := elabHeader leanEnv inputContext startPos stopPos
  if errors.size > 0 then
    return (default, { errors := errors }, dialects)
  match header with
  | .program stx _ =>
    let pos := stx.getPos? |>.getD 0
    return (default, {
      errors := #[(stx, Lean.mkStringMessage inputContext pos "Expected dialect name")]
    },
    dialects)
  | .dialect stx dialect =>
    elabDialectRest leanEnv loadCallback dialects inputContext stx dialect startPos stopPos

end Strata.Elab
