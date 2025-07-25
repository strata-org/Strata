/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DDM.Elab.Core
import Strata.DDM.BuiltinDialects.StrataDD
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

namespace DialectLoader

def builtinLoader : DialectLoader := .ofDialects #[initDialect, headerDialect, strataDialect]

end DialectLoader

namespace DeclState

def initDeclState : DeclState :=
  let s : DeclState := {
    loader := .builtinLoader
    openDialects := #[]
    openDialectSet := {}
  }
  openDialect! initDialect.name s

end DeclState

/--
Opens the dialect definition dialect in the parser so it is visible to parser, but not
part of environment.  This is used for dialect definitions.
-/
def openParserDialect (s : DeclState) (d : Dialect) : DeclState :=
  let s := { s with metadataDeclMap := s.metadataDeclMap.addDialect d }
  openParserDialectImpl s d.name d.syncats

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
  let s := openDialect! headerDialect.name s
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

/- Elaborate a Strata program -/
partial def elabProgram
    (leanEnv : Lean.Environment)
    (dialects : DialectLoader)
    (inputContext : InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos) : DeclState :=
  let ctx : DeclContext := { inputContext, stopPos }
  let (header, errors, startPos) := elabHeader leanEnv ctx startPos
  if errors.size > 0 then
    { errors := errors }
  else
    match header with
    | .dialect stx _ =>
      let pos := stx.getPos? |>.getD 0
      { errors := #[(stx, Lean.mkStringMessage inputContext pos "Expected program name")] }
    | .program stx dialect =>
      let rec run : DeclM Unit := do
            let iniPos := (←get).pos
            if iniPos >= stopPos then
              pure ()
            else
              let c ← runCommand leanEnv
              if c then
                run
      let s := DeclState.initDeclState
      let s := { s with loader := dialects, pos := startPos }
      let act : DeclM Unit := do
            if dialect ∉ dialects.dialects then
              logError stx s!"Unknown dialect {dialect}."
              return
            modify <| openDialect! dialect
            run
      let ((), s) := act ctx s
      s

/- Elaborate a Strata dialect definition. -/
partial def elabDialect
    (leanEnv : Lean.Environment)
    (dialects : DialectLoader)
    (inputContext : Parser.InputContext)
    (startPos stopPos : String.Pos)
     : Dialect × DeclState :=
  let ctx : DeclContext := { inputContext, stopPos }
  let (header, errors, startPos) := elabHeader leanEnv ctx startPos
  if errors.size > 0 then
    (default, { errors := errors })
  else
    match header with
    | .program stx _ =>
      let pos := stx.getPos? |>.getD 0
      (default, { errors := #[(stx, Lean.mkStringMessage inputContext pos "Expected dialect name")] })
    | .dialect stx dialect =>
      let rec run : DialectM Unit := do
            let iniPos := (←getDeclState).pos
            if iniPos >= stopPos then
              return
            let c ← runDialectCommand leanEnv
            if c then
              run
      let s := openParserDialect .initDeclState strataDialect
      let s := { s with
        loader := dialects,
        pos := startPos
        openDialectSet := s.openDialectSet.insert dialect
      }
      let act : DialectM Unit := do
            if dialect ∈ (← getDeclState).dialects then
              logError stx[1] <| s!"Dialect {dialect} already declared."
              return
            run
      let d := { name := dialect }
      let (((), d), s) := act d ctx s
      (d, s)

end Strata.Elab
