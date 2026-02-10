/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Function
import Strata.Languages.Core.TypeDecl
import Strata.Languages.Core.Axiom

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Imperative

-- Type class instances needed for deriving and formatting
instance : Inhabited TypeDecl where
  default := .con { name := "DefaultType", numargs := 0 }

-- ToFormat instance for Function (which is LFunc CoreLParams)
-- Note: ToFormat CoreLParams.Identifier is now defined in Identifiers.lean

inductive DeclKind : Type where
  | var | type | ax | distinct | proc | func
  deriving DecidableEq, Repr

instance : ToFormat DeclKind where
  format k := match k with
    | .var => "variable"
    | .type => "type"
    | .ax => "axiom"
    | .distinct => "distinct"
    | .proc => "procedure"
    | .func => "function"

/--
A Strata Core declaration.
Note: constants are 0-ary functions.
 -/
inductive Decl where
  | var (name : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr) (md : MetaData Core.Expression := .empty)
  | type (t : TypeDecl) (md : MetaData Core.Expression := .empty)
  | ax   (a : Axiom) (md : MetaData Core.Expression := .empty)
  -- The following is temporary, until we have lists and can encode `distinct` in Lambda.
  | distinct (name : Expression.Ident) (es : List Expression.Expr) (md : MetaData Core.Expression := .empty)
  | proc (d : Procedure) (md : MetaData Core.Expression := .empty)
  | func (f : Function) (md : MetaData Core.Expression := .empty)
  deriving Inhabited

def Decl.metadata (d : Decl) : MetaData Expression :=
  match d with
  | .var _ _ _ md    => md
  | .type _ md       => md
  | .ax _ md         => md
  | .distinct _ _ md => md
  | .proc _ md       => md
  | .func _ md       => md

def Decl.kind (d : Decl) : DeclKind :=
  match d with
  | .var _ _ _ _ => .var
  | .type _ _   => .type
  | .ax _ _     => .ax
  | .distinct _ _ _ => .distinct
  | .proc _ _   => .proc
  | .func _ _   => .func

def Decl.name (d : Decl) : Expression.Ident :=
  match d with
  | .var name _ _ _ => name
  | .type t _       => t.name
  | .ax a _         => a.name
  | .distinct n _ _ => n
  | .proc p _       => p.header.name
  | .func f _       => f.name

/-- Get all names from a declaration. For mutual datatypes, returns all datatype names. -/
def Decl.names (d : Decl) : List Expression.Ident :=
  match d with
  | .type t _ => t.names
  | _ => [d.name]

def Decl.getVar? (d : Decl) :
  Option (Expression.Ident × Expression.Ty × Expression.Expr) :=
  match d with
  | .var name ty e _ => some (name, ty, e)
  | _ => none

def Decl.getVar (d : Decl) (H: d.kind = .var):
  Expression.Ident × Expression.Ty × Expression.Expr :=
  match d with | .var name ty e _ => (name, ty, e)

def Decl.getTypeDecl? (d : Decl) : Option TypeDecl :=
  match d with
  | .type t _ => some t
  | _ => none

def Decl.getAxiom? (d : Decl) : Option Axiom :=
  match d with
  | .ax a _ => some a
  | _ => none

def Decl.getTypeDecl (d : Decl) (H: d.kind = .type): TypeDecl :=
  match d with | .type t _ => t

def Decl.getProc? (d : Decl) : Option Procedure :=
  match d with
  | .proc p _ => some p
  | _ => none

def Decl.getProc (d : Decl) (H: d.kind = .proc): Procedure :=
  match d with | .proc p _ => p

def Decl.getFunc? (d : Decl) : Option Function :=
  match d with
  | .func f _ => some f
  | _ => none

def Decl.getFunc (d : Decl) (H: d.kind = .func): Function :=
  let .func f _ := d; f

def Decl.eraseTypes (d : Decl) : Decl :=
  match d with
  | .ax a md     => .ax a.eraseTypes md
  | .proc p md   => .proc p.eraseTypes md
  | .func f md   => .func f.eraseTypes md
  | .var _ _ _ _ | .type _ _ | .distinct _ _ _ => d

-- Metadata not included.
instance : ToFormat Decl where
  format d := match d with
    | .var name ty e _md => f!"var ({name} : {ty}) := {e}"
    | .type t _md => f!"{t}"
    | .ax a _md  => f!"{a}"
    | .distinct l es _md  => f!"distinct [{l}] {es}"
    | .proc p _md => f!"{p}"
    | .func f _md => f!"{f}"

def Decl.formatWithMetaData (decl : Decl) : Format :=
  f!"{decl.metadata}{decl}"

abbrev Decls := List Decl

/-- A Core.Program -/
structure Program where
  { decls : Decls }

def Program.init : Program :=
  { decls := [] }

instance : ToFormat Program where
  format p := Std.Format.joinSep (List.map format p.decls) Format.line

instance : Inhabited Program where
  default := .init

def Program.eraseTypes (p : Program) : Program :=
  { p with decls := p.decls.map Decl.eraseTypes }

def Program.formatWithMetaData  (p : Program) : Format :=
  Std.Format.joinSep (List.map Decl.formatWithMetaData p.decls) Format.line

---------------------------------------------------------------------

def Program.find? (P : Program) (k : DeclKind) (x : Expression.Ident) : Option Decl :=
  go x P.decls
  where go x decls :=
  match decls with
  | [] => none
  | d :: drest =>
    if d.kind == k && d.name == x then d
    else go x drest

theorem Program.find?_kind : ∀ {p : Program}, (p.find? k x) = some d → d.kind = k := by
  intros p Hfind
  simp [Program.find?] at Hfind
  generalize Hdecls : p.decls = decls at Hfind
  induction decls generalizing p
  case nil =>
    unfold Program.find?.go at Hfind
    simp at Hfind
  case cons head tail ih =>
    unfold Program.find?.go at Hfind
    split at Hfind <;> simp_all
    next h =>
    apply ih (by rfl)

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

def Program.getNames (P: Program) : List Expression.Ident :=
  go P.decls
  where go decls := decls.flatMap Decl.names

def Program.Type.find? (P : Program) (x : Expression.Ident) : Option TypeDecl :=
  match P.find? .type x with
  | none => none
  | some d => d.getTypeDecl?

def Program.Procedure.find? (P : Program) (x : Expression.Ident) : Option Procedure :=
  match H: (P.find? .proc x) with
  | none => none
  | some d => some $ d.getProc $ Program.find?_kind H

def Program.Function.find? (P : Program) (x : Expression.Ident)
  : Option Function := do (← P.find? .func x).getFunc?

-- accessor methods based on find?

def Program.getVarTy? (P: Program) (x : Expression.Ident) : Option Expression.Ty := do
  match H: (P.find? .var x) with
  | none => none
  | some decl => some $ (decl.getVar $ Program.find?_kind H).2.1

def Program.getVarInit? (P: Program) (x : Expression.Ident) : Option Expression.Expr := do
  match H: (P.find? .var x) with
  | none => none
  | some decl => some $ (decl.getVar $ Program.find?_kind H).2.2

theorem Program.findproc_some : (P.find? .proc x).isSome = (Procedure.find? P x).isSome := by
  simp [Procedure.find?, Option.isSome, Program.find?]
  split <;> simp
  . next x val heq =>
    split <;> simp
    next x' val' heq' =>
    split at heq' <;> simp_all
  . next od Heq =>
    split <;> simp
    next x' val' heq' =>
    split at heq' <;> simp_all

----------------------------------------------------------------

-- A deterministic version of find? that always returns the desired result.
def Program.find (P : Program) (k : DeclKind) (x : Expression.Ident) (H : (find? P k x).isSome = true)
  : Decl := (Program.find? P k x).get H

theorem Program.find_kind : ∀ (p : Program) {H: (p.find? k x).isSome = true}, (p.find k x H).kind = k := by
  intros p H
  simp [Program.find, Option.get]
  simp [Option.isSome] at H
  split
  next d' Hsome d Hsome' Heq Heq' =>
  split at H <;> try contradiction
  next x' val heq =>
  simp_all
  simp [Heq] at *
  expose_names
  apply find?_kind
  apply heq

theorem Program.find?find : ∀ P : Program,
    (P.find? k x) = some v ↔
    (exists H : (P.find? k x).isSome = true, (P.find k x H) = v) := by
  intros P
  exact Option.eq_some_iff_get_eq

def Program.Type.find (P: Program) (x : Expression.Ident) (H : (P.find? .type x).isSome = true)
  : TypeDecl
  := (P.find .type x H).getTypeDecl (find_kind P)

def Program.Procedure.find (P: Program) (x : Expression.Ident) (H : (P.find? .proc x).isSome = true)
  : Procedure
  := (P.find .proc x H).getProc (find_kind P)

def Program.Function.find (P: Program) (x : Expression.Ident) (H : (P.find? .func x).isSome = true)
  : Function :=
  (P.find .func x H).getFunc (find_kind P)

def Program.getVar (P: Program) (x : Expression.Ident) (H : (P.find? .var x).isSome = true)
  : Expression.Ident × Expression.Ty × Expression.Expr :=
  (P.find .var x H).getVar (find_kind P)

def Program.getVarTy (P: Program) (x : Expression.Ident) (H : (P.find? .var x).isSome = true)
  : Expression.Ty :=
  ((P.find .var x H).getVar (find_kind P)).2.1

def Program.getVarInit (P: Program) (x : Expression.Ident) (H : (P.find? .var x).isSome = true)
  : Expression.Expr :=
  ((P.find .var x H).getVar (find_kind P)).2.2
def Program.Procedure.findP? (P : Program) (x : Expression.Ident)
  : Option (Procedure ×' (find? P x).isSome = true) :=
  match Heq1 : (P.find? .proc x) with
  | some prog =>
    match Heq2 : prog.getProc? with
    | some proc =>
      let p : (find? P x).isSome = true := by
        simp [find?] at *
        split <;> simp_all
      some ⟨proc, p⟩
    | none => none
  | none => none

---------------------------------------------------------------------

end Core
