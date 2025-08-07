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
    loader := .builtin
    openDialects := #[]
    openDialectSet := {}
  }
  s.openLoadedDialect! initDialect

end DeclState

inductive Header where
| dialect (stx : Syntax) (name : DialectName)
| program (stx : Syntax) (name : DialectName)
deriving Inhabited

/- Elaborate a Strata program -/
partial def elabHeader
    (leanEnv : Lean.Environment)
    (ctx : DeclContext)
    (startPos : String.Pos := 0) : Header × Array (Syntax × Message) × String.Pos :=
  let s : DeclState := .initDeclState
  let s := s.openLoadedDialect! headerDialect
  let s := { s with pos := startPos }
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
  modify fun s => { s with
    globalContext := s.globalContext.addCommand s.loader.dialects cmd
  }
  runCommand leanEnv (commands.push cmd) stopPos

structure Program where

def mkEnv (s : DeclState) (commands : Array Operation) : Environment := {
      dialects := s.loader.dialects -- FIXME.  Compute only reachable dialects.
      openDialects := s.openDialects
      commands := commands
      globalContext := s.globalContext
    }

/- Elaborate a Strata program -/
partial def elabProgram
    (leanEnv : Lean.Environment)
    (loader : LoadedDialects)
    (inputContext : InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos) : Environment × Array (Syntax × Message) :=
  let ctx : DeclContext := { inputContext, stopPos }
  let (header, errors, startPos) := elabHeader leanEnv ctx startPos
  if errors.size > 0 then
    (default, errors)
  else
    match header with
    | .dialect stx _ =>
      let pos := stx.getPos? |>.getD 0
      (default, #[(stx, Lean.mkStringMessage inputContext pos "Expected program name")])
    | .program stx dialect =>
      let s := DeclState.initDeclState
      let s := { s with loader := loader, pos := startPos }
      let act : DeclM (Array Operation) := do
            let some d := loader.dialects[dialect]?
              | logError stx s!"Unknown dialect {dialect}."
                return #[]
            modify fun s => s.openLoadedDialect! d
            runCommand leanEnv #[] stopPos
      let (cmds, s) := act ctx s
      (s.mkEnv cmds, s.errors)

/- Elaborate a Strata dialect definition. -/
partial def elabDialect
    (leanEnv : Lean.Environment)
    (dialects : LoadedDialects)
    (inputContext : Parser.InputContext)
    (startPos stopPos : String.Pos)
     : IO (Dialect × DeclState) := do
  let ctx : DeclContext := { inputContext, stopPos }
  let (header, errors, startPos) := elabHeader leanEnv ctx startPos
  if errors.size > 0 then
    return (default, { loader := dialects, errors := errors })

  match header with
  | .program stx _ =>
    let pos := stx.getPos? |>.getD 0
    return (default, {
      loader := dialects,
      errors := #[(stx, Lean.mkStringMessage inputContext pos "Expected dialect name")]
    })
  | .dialect stx dialect =>
    let rec run : DialectM IO.RealWorld Unit := do
          let iniPos := (←getDeclState).pos
          if iniPos >= stopPos then
            return
          let c ← runDialectCommand leanEnv
          if c then
            run
    let s := DeclState.initDeclState
    let s := s.openParserDialect! StrataDDL
    let s := { s with
      loader := dialects,
      pos := startPos
      openDialectSet := s.openDialectSet.insert dialect
    }
    let act : DialectM IO.RealWorld Unit := do
          if dialect ∈ (← getDeclState).loader.dialects then
            logError stx[1] s!"Dialect {dialect} already declared."
            return
          run
    let dctx : DialectContext IO.RealWorld := {
      loadDialect := fun dialect => throw s!"Unknown dialect {dialect}.",
      declContext := ctx
    }
    let ds : DialectState := {
      declState := s
      dialect := {
          name := dialect,
          imports := #[initDialect.name]
      }
    }
    let ((), ds) ← act dctx ds
    pure (ds.dialect, ds.declState)

end Strata.Elab
