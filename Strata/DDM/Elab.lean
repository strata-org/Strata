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

def initial := dialectProgramState.loader

instance : Inhabited DialectLoader where
  default := initial

def freshDeclState (loader : DialectLoader) : DeclState where
  loader := loader
  parserMap := initDeclState.parserMap
  tokenTable := initDeclState.tokenTable

end DialectLoader

/- Elaborate a Strata program -/
partial def elabProgram
    (env : Lean.Environment)
    (dialects : DialectLoader)
    (inputContext : InputContext)
    (startPos : String.Pos := 0)
    (stopPos : String.Pos := inputContext.input.endPos) : DeclState := Id.run do
  let ctx : DeclContext := { inputContext, stopPos }
  let rec run : DeclM Unit := do
        let iniPos := (←get).pos
        if iniPos >= stopPos then
          checkDialectClosed
        else
          let c ← runCommand env programElabs
          if c then
            run
  let s := { dialects.freshDeclState with pos := startPos }
  let ((), s) := run ctx s
  pure s

/- Elaborate a Strata dialect definition. -/
partial def elabDialect
    (env : Lean.Environment)
    (dialects : DialectLoader)
    (inputContext : Parser.InputContext)
    (startPos stopPos : String.Pos)
     : DeclState := Id.run do
  let ctx : DeclContext := { inputContext, stopPos }
  let rec run : DeclM Unit := do
        let iniPos := (←get).pos
        if iniPos >= stopPos then
          if (←get).currentDialect.isNone then
            logError .missing s!"Missing dialect name."
        else
          let c ← runCommand env dialectElabs
          if c then
            run
  let s := {  dialects.freshDeclState with pos := startPos }
  let s := Elab.openParserDialect s
  let ((), s) := run ctx s
  pure s

end Strata.Elab
