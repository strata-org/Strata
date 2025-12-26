/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.PureExpr
import Strata.DL.Imperative.MetaData
import Strata.DL.Imperative.HasVars
import Strata.DL.Lambda.LExpr

---------------------------------------------------------------------

namespace Imperative


/-! # Imperative Dialect

This dialect defines basic constructs for capturing the semantics of imperative
programs. These constructs are parameterized by `PureExpr`, which can be
instantiated with any language construct that does not have side-effects.
-/

/-! ## Commands

Commands form the core of the Imperative dialect. They include constructs for
variable declaration and assignment, and assertions and assumptions.
-/

/--
A an atomic command in the `Imperative` dialect.

Commands don't create local control flow, and are typically used as a parameter
to `Imperative.Stmt` or other similar types.
-/
inductive Cmd (P : PureExpr) : Type where
  /-- Define a variable called `name` with type `ty` and initial value `e`.
  Note: we may make the initial value optional. -/
  | init     (name : P.Ident) (ty : P.Ty) (e : P.Expr) (md : (MetaData P) := .empty)
  /-- Assign `e` to a pre-existing variable `name`. -/
  | set      (name : P.Ident) (e : P.Expr) (md : (MetaData P) := .empty)
  /-- Assigns an arbitrary value to an existing variable `name`. -/
  | havoc    (name : P.Ident) (md : (MetaData P) := .empty)
  /-- Check whether condition `b` is true, failing if not. -/
  | assert   (label : String) (b : P.Expr) (md : (MetaData P) := .empty)
  /-- Ignore any execution state in which `b` is not true. -/
  | assume   (label : String) (b : P.Expr) (md : (MetaData P) := .empty)

abbrev Cmds (P : PureExpr) := List (Cmd P)

instance [Inhabited P.Ident]: Inhabited (Cmd P) where
  default := .havoc default default

---------------------------------------------------------------------

def Cmd.getMetaData (c : Cmd P) : MetaData P :=
  match c with
  | .init _ _ _ md | .set _ _ md
  | .havoc _ md  | .assert _ _ md | .assume _ _ md =>
   md

instance : SizeOf String where
  sizeOf s := s.length

@[simp]
def Cmd.sizeOf (c : Imperative.Cmd P) : Nat :=
  match c with
  | .init   n t e _ => 1 + SizeOf.sizeOf n + SizeOf.sizeOf t + SizeOf.sizeOf e
  | .set    n e _ => 1 + SizeOf.sizeOf n + SizeOf.sizeOf e
  | .havoc  n _ => 1 + SizeOf.sizeOf n
  | .assert l b _ => 1 + SizeOf.sizeOf l + SizeOf.sizeOf b
  | .assume l b _ => 1 + SizeOf.sizeOf l + SizeOf.sizeOf b

instance (P : PureExpr) : SizeOf (Imperative.Cmd P) where
  sizeOf := Cmd.sizeOf

---------------------------------------------------------------------

class HasPassiveCmds (P : PureExpr) (CmdT : Type) where
  assume : String → P.Expr → MetaData P → CmdT
  assert : String → P.Expr → MetaData P → CmdT

instance : HasPassiveCmds P (Cmd P) where
  assume l e (md := MetaData.empty):= .assume l e md
  assert l e (md := MetaData.empty):= .assert l e md

class HasHavoc (P : PureExpr) (CmdT : Type) where
  havoc : P.Ident → CmdT

instance : HasHavoc P (Cmd P) where
  havoc x := .havoc x
---------------------------------------------------------------------

mutual
/-- Get all variables accessed by `c`. -/
def Cmd.getVars [HasVarsPure P P.Expr] (c : Cmd P) : List P.Ident :=
  match c with
  | .init _ _ e _ => HasVarsPure.getVars e
  | .set _ e _ => HasVarsPure.getVars e
  | .havoc _ _ => []
  | .assert _ e _ => HasVarsPure.getVars e
  | .assume _ e _ => HasVarsPure.getVars e

def Cmds.getVars [HasVarsPure P P.Expr] (cs : Cmds P) : List P.Ident :=
  match cs with
  | [] => []
  | c :: crest => Cmd.getVars c ++ Cmds.getVars crest
  termination_by (sizeOf cs)
end

instance (P : PureExpr) [HasVarsPure P P.Expr]
  : HasVarsPure P (Cmd P) where
  getVars := Cmd.getVars

instance (P : PureExpr) [HasVarsPure P P.Expr]
  : HasVarsPure P (Cmds P) where
  getVars := Cmds.getVars


/-- Get all variables defined by the command `c`. -/
def Cmd.definedVars (c : Cmd P) : List P.Ident :=
  match c with
  | .init name _ _ _ => [name]
  | _ => []

/-- Get all variables defined by commands `cs`. -/
def Cmds.definedVars (cs : Cmds P) : List P.Ident :=
  match cs with
  | [] => []
  | c :: crest => Cmd.definedVars c ++ Cmds.definedVars crest
  termination_by (sizeOf cs)

/-- Get all variables modified by the command `c`. -/
def Cmd.modifiedVars (c : Cmd P) : List P.Ident :=
  match c with
  | .init _ _ _ _ => []
  | .set name _ _ => [name]
  | .havoc name _ => [name]
  | .assert _ _ _ => []
  | .assume _ _ _ => []

/-- Get all variables modified by commands `cs`. -/
def Cmds.modifiedVars (cs : Cmds P) : List P.Ident :=
  match cs with
  | [] => []
  | c :: crest => Cmd.modifiedVars c ++ Cmds.modifiedVars crest
  termination_by (sizeOf cs)

instance (P : PureExpr) : HasVarsImp P (Cmd P) where
  definedVars := Cmd.definedVars
  modifiedVars := Cmd.modifiedVars

instance (P : PureExpr) : HasVarsImp P (Cmds P) where
  definedVars := Cmds.definedVars
  modifiedVars := Cmds.modifiedVars
  -- order matters for Havoc, so needs to override the default
  touchedVars := List.flatMap HasVarsImp.touchedVars

---------------------------------------------------------------------

open Std (ToFormat Format format)

def formatCmd (P : PureExpr) (c : Cmd P)
    [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match c with
  | .init name ty e _md => f!"init ({name} : {ty}) := {e}"
  | .set name e _md => f!"{name} := {e}"
  | .havoc name _md => f!"havoc {name}"
  | .assert label b _md => f!"assert [{label}] {b}"
  | .assume label b _md => f!"assume [{label}] {b}"

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
        : ToFormat (Cmd P) where
  format c := formatCmd P c

def formatCmds (P : PureExpr) (cs : Cmds P)
    [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match cs with
  | [] => f!""
  | c :: crest => f!"{formatCmd P c}{Format.line}{formatCmds P crest}"

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
        : ToFormat (Cmds P) where
  format cs := formatCmds P cs

---------------------------------------------------------------------

end Imperative
