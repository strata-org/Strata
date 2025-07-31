/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Procedure
import Strata.Languages.Boogie.Function
import Strata.Languages.Boogie.TypeDecl
import Strata.Languages.Boogie.Axiom

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)
open Imperative

inductive DeclKind : Type where
  | var | type | ax | proc | func
  deriving DecidableEq, Repr

/--
A Boogie declaration.
Note: constants are 0-ary functions.
 -/
inductive Decl where
  | var (name : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr) (md : MetaData Boogie.Expression := .empty)
  | type (t : TypeDecl) (md : MetaData Boogie.Expression := .empty)
  | ax   (a : Axiom) (md : MetaData Boogie.Expression := .empty)
  | proc (d : Procedure) (md : MetaData Boogie.Expression := .empty)
  | func (f : Function) (md : MetaData Boogie.Expression := .empty)
  deriving Inhabited

def Decl.kind (d : Decl) : DeclKind :=
  match d with
  | .var _ _ _ _ => .var
  | .type _ _   => .type
  | .ax _ _     => .ax
  | .proc _ _   => .proc
  | .func _ _   => .func

def Decl.name (d : Decl) : Expression.Ident :=
  match d with
  | .var name _ _ _ => name
  | .type t _       => t.name
  | .ax a _         => a.name
  | .proc p _       => p.header.name
  | .func f _       => f.name

def Decl.getVar? (d : Decl) :
  Option (Expression.Ident × Expression.Ty × Expression.Expr) :=
  match d with
  | .var name ty e _ => some (name, ty, e)
  | _ => none

def Decl.getTypeDecl? (d : Decl) : Option TypeDecl :=
  match d with
  | .type t _ => some t
  | _ => none

def Decl.getAxiom? (d : Decl) : Option Axiom :=
  match d with
  | .ax a _ => some a
  | _ => none

def Decl.getProc? (d : Decl) : Option Procedure :=
  match d with
  | .proc p _ => some p
  | _ => none

def Decl.getFunc? (d : Decl) : Option Function :=
  match d with
  | .func f _ => some f
  | _ => none

instance : ToFormat Decl where
  format d := match d with
    | .var name ty e md => f!"{md}var ({name} : {ty}) := {e}"
    | .type t md => f!"{md}{t}"
    | .ax a md  => f!"{md}{a}"
    | .proc p md => f!"{md}{p}"
    | .func f md => f!"{md}{f}"

abbrev Decls := List Decl

/-- A Boogie Program -/
structure Program where
  { decls : Decls }

def Program.init : Program :=
  { decls := [] }

instance : ToFormat Program where
  format p := Std.Format.joinSep (List.map format p.decls) Format.line

instance : Inhabited Program where
  default := .init

---------------------------------------------------------------------

def Program.find? (P : Program) (k : DeclKind) (x : Expression.Ident) : Option Decl :=
  go x P.decls
  where go x decls :=
  match decls with
  | [] => none
  | d :: drest =>
    if d.kind == k && d.name == x then d
    else go x drest

def Program.getVar? (P: Program) (x : Expression.Ident)
  : Option (Expression.Ident × Expression.Ty × Expression.Expr) := do
  let decl ← P.find? .var x
  let var ← decl.getVar?
  return var

def Program.getTy? (P: Program) (x : Expression.Ident) : Option Expression.Ty := do
  let var ← P.getVar? x
  let ty ← var.snd.fst
  return ty

def Program.getAxiom? (P: Program) (n : Expression.Ident) : Option Axiom := do
  let decl ← P.find? .ax n
  let ax ← decl.getAxiom?
  return ax

def Program.getInit? (P: Program) (x : Expression.Ident) : Option Expression.Expr := do
  let var ← P.getVar? x
  let init ← var.snd.snd
  return init

def Program.getNames (P : Program) (k : DeclKind) : List Expression.Ident :=
  go k P.decls
  where go k decls :=
  match decls with
  | [] => []
  | d :: drest =>
    let rest := go k drest
    if d.kind == k then d.name :: rest else rest

def Program.Type.find? (P : Program) (x : Expression.Ident) : Option TypeDecl :=
  match P.find? .type x with
  | none => none
  | some d => d.getTypeDecl?

def Program.Procedure.find? (P : Program) (x : Expression.Ident) : Option Procedure :=
  match P.find? .proc x with
  | none => none
  | some d => d.getProc?

def Program.Function.find? (P : Program) (x : Expression.Ident)
  : Option Function := do (← P.find? .func x).getFunc?

def Program.Procedure.findP? (P : Program) (x : Expression.Ident)
  : Option (Procedure ×' (find? P x).isSome = true) :=
  match Heq1 : (P.find? .proc x) with
  | some prog =>
    match Heq2 : prog.getProc? with
    | some proc =>
      let p : (find? P x).isSome = true := by
        simp [find?] at *; simp_all
      some ⟨proc, p⟩
    | none => none
  | none => none

def Program.find (P : Program) (k : DeclKind) (x : Expression.Ident) (H : (find? P k x).isSome = true)
  : Decl := (Program.find? P k x).get H

def Program.Procedure.find (P : Program) (x : Expression.Ident) (H : (find? P x).isSome = true)
  : Procedure := (Program.Procedure.find? P x).get H

---------------------------------------------------------------------

end Boogie
