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

def mkArgElab (bindings : DeclBindings) (syntaxLevel : Nat) (argLevel : Fin bindings.size) : ArgElaborator :=
  let contextLevel : Option (Fin argLevel) := bindings.argScopeLevel argLevel
  { argLevel := argLevel.val, syntaxLevel, contextLevel }

def addElaborators (bindings : DeclBindings) (p : Nat × Array ArgElaborator) (a : SyntaxDefAtom) : Nat × Array ArgElaborator :=
  match a with
  | .ident level _prec =>
    let (si, es) := p
    if h : level < bindings.size then
      let argElab := mkArgElab bindings si ⟨level, h⟩
      (si + 1, es.push argElab)
    else
      panic! "Invalid index"
  | .str _ =>
    let (si, es) := p
    (si + 1, es)
  | .indent _ as =>
    as.attach.foldl (init := p) (fun p ⟨a, _⟩ => addElaborators bindings p a)

/-- Information needed to elaborator operations or functions. -/
structure SyntaxElaborator where
  argElaborators : Array ArgElaborator
  resultScope : Option Nat
deriving Inhabited, Repr

def mkElaborators (bindings : DeclBindings) (as : Array SyntaxDefAtom) : Array ArgElaborator :=
  let init : Array ArgElaborator := Array.mkEmpty bindings.size
  let (_, es) := as.foldl (init := (0, init)) (addElaborators bindings)
  es.qsort (fun x y => x.argLevel < y.argLevel)

def mkSyntaxElab (bindings : DeclBindings) (stx : SyntaxDef) (opMd : Metadata) : SyntaxElaborator := {
    argElaborators := mkElaborators bindings stx.atoms,
    resultScope := opMd.resultLevel bindings.size,
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
