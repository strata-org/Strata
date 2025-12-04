/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.MetaData
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.HasVars

---------------------------------------------------------------------

namespace Imperative

/-! # Imperative dialect: non-deterministic statements

These statements use assumptions to encode conditional branches and guarded
loops. This is roughly the structure used by most formalizations of [Guarded
Comamnds](https://en.wikipedia.org/wiki/Guarded_Command_Language), and in
[Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf).
-/

/--
A non-deterministic statement, parameterized by a type of pure expressions (`P`)
and a type of commands (`Cmd`).

This encodes the same types of control flow as `Stmt`, but using only
non-deterministic choices: arbitrarily choosing one of two sub-statements to
execute or executing a sub-statement an arbitrary number of times. Conditions
can be encoded if the command type includes assumptions.
-/
inductive NondetStmt (P : PureExpr) (Cmd : Type) : Type where
  /-- An atomic command, of an arbitrary type. -/
  | cmd      (cmd : Cmd)
  /-- Execute `s1` followed by `s2`. -/
  | seq      (s1 s2 : NondetStmt P Cmd)
  /-- Execute either `s1` or `s2`, arbitrarily. -/
  | choice   (s1 s2 : NondetStmt P Cmd)
  /-- Execute `s` an arbitrary number of times (possibly zero). -/
  | loop     (s : NondetStmt P Cmd)
  deriving Inhabited

abbrev NondetStmt.init {P : PureExpr} (name : P.Ident) (ty : P.Ty) (expr : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.init name ty expr md)
abbrev NondetStmt.set {P : PureExpr} (name : P.Ident) (expr : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.set name expr md)
abbrev NondetStmt.havoc {P : PureExpr} (name : P.Ident) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.havoc name md)
abbrev NondetStmt.assert {P : PureExpr} (label : String) (b : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.assert label b md)
abbrev NondetStmt.assume {P : PureExpr} (label : String) (b : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.assume label b md)

mutual
/-- Get all variables defined by the statement `s`. -/
def NondetStmt.definedVars [HasVarsImp P C] (s : NondetStmt P C) : List P.Ident :=
  match s with
  | .cmd c => HasVarsImp.definedVars c
  | .seq s1 s2 => NondetStmt.definedVars s1 ++ NondetStmt.definedVars s2
  | .choice s1 s2 => NondetStmt.definedVars s1 ++ NondetStmt.definedVars s2
  | .loop s => NondetStmt.definedVars s

def NondetStmts.definedVars [HasVarsImp P C] (ss : List (NondetStmt P C)) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => NondetStmt.definedVars s ++ NondetStmts.definedVars srest
end

mutual
/-- Get all variables modified by the statement `s`. -/
def NondetStmt.modifiedVars [HasVarsImp P C] (s : NondetStmt P C) : List P.Ident :=
  match s with
  | .cmd c => HasVarsImp.modifiedVars c
  | .seq s1 s2 => NondetStmt.modifiedVars s1 ++ NondetStmt.modifiedVars s2
  | .choice s1 s2 => NondetStmt.modifiedVars s1 ++ NondetStmt.modifiedVars s2
  | .loop s => NondetStmt.modifiedVars s

def NondetStmts.modifiedVars [HasVarsImp P C] (ss : List (NondetStmt P C)) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => NondetStmt.modifiedVars s ++ NondetStmts.modifiedVars srest
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (NondetStmt P C) where
  definedVars := NondetStmt.definedVars
  modifiedVars := NondetStmt.modifiedVars

---------------------------------------------------------------------

/-! ## Formatting -/

open Std (ToFormat Format format)

def formatNondetStmt (P : PureExpr) (s : NondetStmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]: Format :=
  match s with
  | .cmd cmd => format cmd
  | .seq s1 s2 => f!"({formatNondetStmt P s1}) ; ({formatNondetStmt P s2})"
  | .choice s1 s2 => f!"({formatNondetStmt P s1}) | ({formatNondetStmt P s2})"
  | .loop s => f!"({formatNondetStmt P s})*"

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (NondetStmt P C) where
  format s := formatNondetStmt P s

---------------------------------------------------------------------

end Imperative
