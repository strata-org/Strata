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

abbrev ArgElaboratorArray (sc : Nat) :=
  Array { a : ArgElaborator // a.syntaxLevel < sc }

/-- Information needed to elaborator arguments to operations or functions. -/
structure ArgElaborators where
  /-- Expected number of arguments elaborator will process. -/
  syntaxCount : Nat
  argElaborators : ArgElaboratorArray syntaxCount
deriving Inhabited, Repr

namespace ArgElaborators

def inc (as : ArgElaborators) : ArgElaborators :=
  let sc := as.syntaxCount
  let elabs := as.argElaborators.unattach
  have ext (e : ArgElaborator) (mem : e ∈ elabs) : e.syntaxLevel < sc + 1 := by
          simp [elabs] at mem
          grind
  let elabs' := elabs.attachWith (·.syntaxLevel < sc + 1) ext
  have scp : sc < sc + 1 := by grind
  { syntaxCount := sc + 1
    argElaborators := elabs'
  }

def push (as : ArgElaborators)
         (argDecls : ArgDecls)
         (argLevel : Fin argDecls.size) : ArgElaborators :=
  let sc := as.syntaxCount
  let as := as.inc
  let newElab : ArgElaborator := {
    syntaxLevel := sc
    argLevel := argLevel.val
    contextLevel := argDecls.argScopeLevel argLevel
  }
  have scp : sc < sc + 1 := by grind
  { as with argElaborators := as.argElaborators.push ⟨newElab, scp⟩ }

end ArgElaborators

def addElaborators (argDecls : ArgDecls) (p : ArgElaborators) (a : SyntaxDefAtom) : ArgElaborators :=
  match a with
  | .ident level _prec =>
    if h : level < argDecls.size then
      p.push argDecls ⟨level, h⟩
    else
      panic! "Invalid index"
  | .str s =>
    if s.trim.isEmpty then
      p
    else
      p.inc
  | .indent _ as =>
    as.attach.foldl (init := p) (fun p ⟨a, _⟩ => addElaborators argDecls p a)

/-- Information needed to elaborate operations or functions. -/
structure SyntaxElaborator where
  /-- Expected number of arguments elaborator will process. -/
  syntaxCount : Nat
  argElaborators : ArgElaboratorArray syntaxCount
  resultScope : Option Nat
deriving Inhabited, Repr

def mkSyntaxElab (argDecls : ArgDecls) (stx : SyntaxDef) (opMd : Metadata) : SyntaxElaborator :=
  let init : ArgElaborators := {
    syntaxCount := 0
    argElaborators := Array.mkEmpty argDecls.size
  }
  let as := stx.atoms.foldl (init := init) (addElaborators argDecls)
  -- In the case with no syntax there is still a single expected
  -- syntax argument with the empty string.
  let as := if as.syntaxCount = 0 then as.inc else as
  let elabs := as.argElaborators.qsort (·.val.argLevel < ·.val.argLevel)
  {
    syntaxCount := as.syntaxCount
    argElaborators := elabs
    resultScope := opMd.resultLevel argDecls.size
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
