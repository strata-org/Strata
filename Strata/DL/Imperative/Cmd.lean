/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.MetaData
public import Strata.DL.Imperative.HasVars

---------------------------------------------------------------------

namespace Imperative

public section


/-! # Imperative Dialect

This dialect defines basic constructs for capturing the semantics of imperative
programs. These constructs are parameterized by `PureExpr`, which can be
instantiated with any language construct that does not have side-effects.
-/

/-! ## Deterministic or Non-deterministic Expressions

`ExprOrNondet` represents a value that is either a deterministic expression or
a non-deterministic (arbitrary) choice. This is used in commands where the
right-hand side can be either a concrete expression or a havoc.
-/

/-- A value that is either a deterministic expression or a non-deterministic choice. -/
inductive ExprOrNondet (P : PureExpr) where
  /-- A deterministic expression. -/
  | det (e : P.Expr)
  /-- A non-deterministic (arbitrary) value. -/
  | nondet
  deriving Inhabited

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
  /-- Define a variable called `name` with type `ty` and value `e`.
      When `e` is `.nondet`, the variable is initialized with an arbitrary value. -/
  | init     (name : P.Ident) (ty : P.Ty) (e : ExprOrNondet P) (md : (MetaData P))
  /-- Assign `e` to a pre-existing variable `name`.
      When `e` is `.nondet`, assigns an arbitrary value (havoc semantics). -/
  | set      (name : P.Ident) (e : ExprOrNondet P) (md : (MetaData P))
  /-- Checks if condition `b` is true on _all_ paths on which this command is
    encountered. Reports an error if `b` does not hold on _any_ of these paths.
  -/
  | assert   (label : String) (b : P.Expr) (md : (MetaData P))
  /-- Ignore any execution state in which `b` is not true. -/
  | assume   (label : String) (b : P.Expr) (md : (MetaData P))
  /--
  Checks if there _exists_ a path that reaches this command and condition `b` is
  true. Reports an error otherwise. This is the dual of `assert`, and can be
  used for coverage analysis.
  -/
  | cover    (label : String) (b : P.Expr) (md : (MetaData P))

@[expose] abbrev Cmds (P : PureExpr) := List (Cmd P)

instance [Inhabited P.Ident]: Inhabited (Cmd P) where
  default := .set default .nondet default

---------------------------------------------------------------------

def Cmd.getMetaData (c : Cmd P) : MetaData P :=
  match c with
  | .init _ _ _ md | .set _ _ md
  | .assert _ _ md | .assume _ _ md | .cover _ _ md =>
   md

---------------------------------------------------------------------

class HasPassiveCmds (P : PureExpr) (CmdT : Type) where
  assume : String → P.Expr → MetaData P → CmdT
  assert : String → P.Expr → MetaData P → CmdT

instance : HasPassiveCmds P (Cmd P) where
  assume l e (md := MetaData.empty):= .assume l e md
  assert l e (md := MetaData.empty):= .assert l e md

class HasHavoc (P : PureExpr) (CmdT : Type) where
  havoc : P.Ident → MetaData P → CmdT

instance : HasHavoc P (Cmd P) where
  havoc x md := .set x .nondet md

/-- Declare a variable with a given type and value (deterministic or non-deterministic). -/
class HasInit (P : PureExpr) (CmdT : Type) where
  init : P.Ident → P.Ty → ExprOrNondet P → MetaData P → CmdT

instance : HasInit P (Cmd P) where
  init x ty e md := .init x ty e md

---------------------------------------------------------------------

/-- Get all variables accessed by an `ExprOrNondet`. -/
def ExprOrNondet.getVars [HasVarsPure P P.Expr] (e : ExprOrNondet P) : List P.Ident :=
  match e with
  | .det e => HasVarsPure.getVars e
  | .nondet => []

/-- Map a function over the expression in an `ExprOrNondet`. -/
def ExprOrNondet.map {P Q : PureExpr} (f : P.Expr → Q.Expr) : ExprOrNondet P → ExprOrNondet Q
  | .det e => .det (f e)
  | .nondet => .nondet

mutual
/-- Get all variables accessed by `c`. -/
def Cmd.getVars [HasVarsPure P P.Expr] (c : Cmd P) : List P.Ident :=
  match c with
  | .init _ _ e _ => e.getVars
  | .set _ e _ => e.getVars
  | .assert _ e _ => HasVarsPure.getVars e
  | .assume _ e _ => HasVarsPure.getVars e
  | .cover _ e _ => HasVarsPure.getVars e

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
  | .assert _ _ _ => []
  | .assume _ _ _ => []
  | .cover _ _ _ => []

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

def formatExprOrNondet (P : PureExpr) (e : ExprOrNondet P)
    [ToFormat P.Expr] : Format :=
  match e with
  | .det e => format e
  | .nondet => f!"*"

instance [ToFormat P.Expr] : ToFormat (ExprOrNondet P) where
  format e := formatExprOrNondet P e

def formatCmd (P : PureExpr) (c : Cmd P)
    [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match c with
  | .init name ty (.det e) _md => f!"init ({name} : {ty}) := {e}"
  | .init name ty .nondet _md => f!"init ({name} : {ty})"
  | .set name (.det e) _md => f!"{name} := {e}"
  | .set name .nondet _md => f!"havoc {name}"
  | .assert label b _md => f!"assert [{label}] {b}"
  | .assume label b _md => f!"assume [{label}] {b}"
  | .cover label b _md => f!"cover [{label}] {b}"

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

end -- public section
end Imperative
