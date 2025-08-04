/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
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
