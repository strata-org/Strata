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
A command in the Imperative dialect
-/
inductive Cmd (P : PureExpr) : Type where
  /-- `init` defines a variable called `name` with type `ty` and
    initial value `e`. -/
  | init     (name : P.Ident) (ty : P.Ty) (e : P.Expr) (md : (MetaData P) := .empty)
  /-- `set` assigns `e` to a pre-existing variable `name`. -/
  | set      (name : P.Ident) (e : P.Expr) (md : (MetaData P) := .empty)
  /-- `havoc` assigns a pre-existing variable `name` a random value. -/
  | havoc    (name : P.Ident) (md : (MetaData P) := .empty)
  /-- `assert` checks whether condition `b` is true. -/
  | assert   (label : String) (b : P.Expr) (md : (MetaData P) := .empty)
  /-- `assume` constrains execution by adding assumption `b`. -/
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
  | .init name _ _ _ => [name]
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
  | .init name ty e md => f!"{md}init ({name} : {ty}) := {e}"
  | .set name e md => f!"{md}{name} := {e}"
  | .havoc name md => f!"{md}havoc {name}"
  | .assert label b md => f!"{md}assert [{label}] {b}"
  | .assume label b md => f!"{md}assume [{label}] {b}"

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
