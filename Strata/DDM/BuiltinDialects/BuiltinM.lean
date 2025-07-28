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

import Strata.DDM.Elab.DeclM

namespace Strata

namespace Elab

def initParsers : Parser.ParsingContext where
  fixedParsers := .ofList [
    (q`Init.Ident, Parser.identifier),
    (q`Init.Num, Parser.numLit),
    (q`Init.Decimal, Parser.decimalLit),
    (q`Init.Str, Parser.strLit)
  ]

def initTokenTable : Lean.Parser.TokenTable :=
  initParsers.fixedParsers.fold (init := {}) fun tt _ p => tt.addTokens p

namespace DialectLoader

def addDialect! (ctx : DialectLoader) (d : Dialect) : DialectLoader :=
  assert! d.name ∉ ctx.dialects
  {
    dialects := ctx.dialects.insert d
    dialectParsers := ctx.dialectParsers.addDialect! initParsers d
    syntaxElabMap := ctx.syntaxElabMap.addDialect d
  }

def ofDialects (ds : Array Dialect) : DialectLoader :=
  ds.foldl (init := {}) (·.addDialect! ·)

end DialectLoader

namespace DeclState

def ofDialects (ds : Array Dialect) : DeclState :=
  let s : DeclState := {
    loader := .ofDialects ds
    openDialects := #[]
    openDialectSet := {}
    tokenTable := initTokenTable
  }
  ds.foldl (init := s) (fun s d => openDialect! d.name s)

end DeclState

abbrev BuiltinM := StateT Dialect DeclM

namespace BuiltinM

def create! (name : DialectName) (dialects : Array Dialect) (act : BuiltinM Unit) : Dialect :=
  let d : Dialect :=  { name }
  let s : DeclState := .ofDialects dialects
  let (((), d), s) := act d .empty s
  if s.errors.size > 0 then
    panic! "Initial program state initialization failed"
  else
    d


def addDeclToDialect (decl : Decl) : BuiltinM Unit := do
  modify fun d => d.addDecl decl

end BuiltinM

def declareCat (cat : QualifiedIdent) (argNames : Array String := #[]): BuiltinM Unit := do
  assert! cat.dialect = (←get).name
  if cat.name ∈ (← get).cache then
    panic! s!"declareCat Category {eformat cat} already declared"
  let decl := { name := cat.name, argNames }
  addTypeOrCatDecl cat.dialect (.syncat decl)
  .addDeclToDialect  (.syncat decl)

def declareAtomicCat (cat : QualifiedIdent) : BuiltinM Unit := do
  let decl := { name := cat.name }
  assert! cat.dialect = (←get).name
  addTypeOrCatDecl cat.dialect (.syncat decl)
  .addDeclToDialect (.syncat decl)

def declareOp (decl : OpDecl) : BuiltinM Unit := do
  let dialect := (←get).name
  match initParsers.opDeclParser dialect decl with
  | .error msg =>
    panic! (eformat msg).pretty
  | .ok _dp =>
    .addDeclToDialect (.op decl)

def declareMetadata (decl : MetadataDecl) : BuiltinM Unit := do
  .addDeclToDialect (.metadata decl)
