/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab.DeclM

namespace Strata

namespace Elab

def initTokenTable : Lean.Parser.TokenTable :=
  initParsers.fixedParsers.fold (init := {}) fun tt _ p => tt.addTokens p

namespace DeclState

def ofDialects (ds : LoadedDialects) : DeclState :=
  let s : DeclState := {
    loader := ds
    openDialects := #[]
    openDialectSet := {}
    tokenTable := initTokenTable
  }
  ds.dialects.toList.foldl (init := s) (·.openLoadedDialect! ·)

end DeclState

abbrev BuiltinM := StateT Dialect DeclM

namespace BuiltinM

def create! (name : DialectName) (dialects : Array Dialect) (act : BuiltinM Unit) : Dialect :=
  let d : Dialect :=  { name }
  let s : DeclState := .ofDialects (.ofDialects! dialects)
  let (((), d), s) := act d .empty s
  if s.errors.size > 0 then
    panic! "Initial program state initialization failed"
  else
    d


def addDecl (decl : Decl) : BuiltinM Unit := do
  modify fun d => d.addDecl decl

end BuiltinM

def declareCat (cat : QualifiedIdent) (argNames : Array String := #[]): BuiltinM Unit := do
  assert! cat.dialect = (←get).name
  if cat.name ∈ (← get).cache then
    panic! s!"declareCat Category {eformat cat} already declared"
  let decl := { name := cat.name, argNames }
  addTypeOrCatDecl cat.dialect (.syncat decl)
  .addDecl  (.syncat decl)

def declareAtomicCat (cat : QualifiedIdent) : BuiltinM Unit := do
  let decl := { name := cat.name }
  assert! cat.dialect = (←get).name
  addTypeOrCatDecl cat.dialect (.syncat decl)
  .addDecl (.syncat decl)

def declareOp (decl : OpDecl) : BuiltinM Unit := do
  let dialect := (←get).name
  match initParsers.opDeclParser dialect decl with
  | .error msg =>
    panic! (eformat msg).pretty
  | .ok _dp =>
    .addDecl (.op decl)

def declareMetadata (decl : MetadataDecl) : BuiltinM Unit := do
  .addDecl (.metadata decl)
