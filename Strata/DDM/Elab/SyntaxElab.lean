/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Parser
import Strata.DDM.Util.Lean

namespace Strata.Elab

/--
Describes an elaboration relationship between a argument in the bindings and
the syntax node.
-/
structure ArgElaborator where
  -- Index of this argument to elaborator in syntax tree.
  syntaxLevel : Nat
  -- Level of argument in bindings.
  argLevel : Nat
  -- Index of argument to use for typing context (if specified, must be less than argIndex)
  contextLevel : Option (Fin argLevel) := .none
deriving Inhabited, Repr

def mkArgElab (argDecls : ArgDecls) (syntaxLevel : Nat) (argLevel : Fin argDecls.size) : ArgElaborator :=
  let contextLevel : Option (Fin argLevel) := argDecls.argScopeLevel argLevel
  { argLevel := argLevel.val, syntaxLevel, contextLevel }

def addElaborators (argDecls : ArgDecls) (p : Nat × Array ArgElaborator) (a : SyntaxDefAtom) : Nat × Array ArgElaborator :=
  match a with
  | .ident level _prec =>
    let (si, es) := p
    if h : level < argDecls.size then
      let argElab := mkArgElab argDecls si ⟨level, h⟩
      (si + 1, es.push argElab)
    else
      panic! "Invalid index"
  | .str _ =>
    let (si, es) := p
    (si + 1, es)
  | .indent _ as =>
    as.attach.foldl (init := p) (fun p ⟨a, _⟩ => addElaborators argDecls p a)

/-- Information needed to elaborator operations or functions. -/
structure SyntaxElaborator where
  argElaborators : Array ArgElaborator
  resultScope : Option Nat
deriving Inhabited, Repr

def mkElaborators (argDecls : ArgDecls) (as : Array SyntaxDefAtom) : Array ArgElaborator :=
  let init : Array ArgElaborator := Array.mkEmpty argDecls.size
  let (_, es) := as.foldl (init := (0, init)) (addElaborators argDecls)
  es.qsort (fun x y => x.argLevel < y.argLevel)

def mkSyntaxElab (argDecls : ArgDecls) (stx : SyntaxDef) (opMd : Metadata) : SyntaxElaborator := {
    argElaborators := mkElaborators argDecls stx.atoms,
    resultScope := opMd.resultLevel argDecls.size,
  }

def opDeclElaborator (decl : OpDecl) : SyntaxElaborator :=
  mkSyntaxElab decl.argDecls decl.syntaxDef decl.metadata

def fnDeclElaborator (decl : FunctionDecl) : SyntaxElaborator :=
  mkSyntaxElab decl.argDecls decl.syntaxDef decl.metadata

abbrev SyntaxElabMap := Std.HashMap QualifiedIdent SyntaxElaborator

namespace SyntaxElabMap

def add (m : SyntaxElabMap) (dialect : String) (name : String) (se : SyntaxElaborator) : SyntaxElabMap :=
  m.insert { dialect, name := name } se

def addDecl (m : SyntaxElabMap) (dialect : String) (d : Decl) : SyntaxElabMap :=
  match d with
  | .op d => m.add dialect d.name (opDeclElaborator d)
  | .function d => m.add dialect d.name (fnDeclElaborator d)
  | _ => m

def addDialect (m : SyntaxElabMap) (d : Dialect) : SyntaxElabMap :=
  d.declarations.foldl (·.addDecl d.name) m

end SyntaxElabMap
