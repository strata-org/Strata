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

import Strata.DDM.Elab.SyntaxElab

open Strata.Parser (DeclParser ParsingContext)

namespace Strata.Elab

abbrev DialectParsers := Std.HashMap DialectName (Array DeclParser)

namespace DialectParsers

def addDialect! (pm : DialectParsers) (pctx : ParsingContext) (dialect : Dialect) : DialectParsers :=
  match pctx.mkDialectParsers dialect with
  | .error msg =>
    @panic _ ⟨pm⟩ s!"Could not add open dialect: {eformat msg |>.pretty}"
  | .ok parsers => pm.insert dialect.name parsers

end DialectParsers

/--
Information about dialects.
-/
structure LoadedDialects where
  /--- Map from dialect names to the dialect definition. -/
  dialects : DialectMap := {}
  /-- Parsers for dialects in map. -/
  dialectParsers : DialectParsers := {}
  /--/ Map for elaborating operations and functions. -/
  syntaxElabMap : SyntaxElabMap := {}
  deriving Inhabited

def initParsers : Parser.ParsingContext where
  fixedParsers := .ofList [
    (q`Init.Ident, Parser.identifier),
    (q`Init.Num, Parser.numLit),
    (q`Init.Decimal, Parser.decimalLit),
    (q`Init.Str, Parser.strLit)
  ]

namespace LoadedDialects

def addDialect! (loader : LoadedDialects) (d : Dialect) : LoadedDialects :=
  assert! d.name ∉ loader.dialects
  {
    dialects := loader.dialects.insert! d
    dialectParsers := loader.dialectParsers.addDialect! initParsers d
    syntaxElabMap := loader.syntaxElabMap.addDialect d
  }

def ofDialects! (ds : Array Dialect) : LoadedDialects :=
  ds.foldl (init := {}) (·.addDialect! ·)

end LoadedDialects
