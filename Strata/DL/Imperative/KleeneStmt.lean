/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd

---------------------------------------------------------------------

namespace Imperative

public section

/-! # Imperative dialect: Kleene statements

These statements use assumptions to encode conditional branches and guarded
loops. This is roughly the structure used by most formalizations of [Guarded
Commands](https://en.wikipedia.org/wiki/Guarded_Command_Language), and in
[Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf).
-/

/--
A Kleene statement, parameterized by a type of pure expressions (`P`)
and a type of commands (`Cmd`).

This encodes the same types of control flow as `Stmt`, but using only
non-deterministic choices: arbitrarily choosing one of two sub-statements to
execute or executing a sub-statement an arbitrary number of times. Conditions
can be encoded if the command type includes assumptions.
-/
inductive KleeneStmt (P : PureExpr) (Cmd : Type) : Type where
  /-- An atomic command, of an arbitrary type. -/
  | cmd      (cmd : Cmd)
  /-- Execute `s1` followed by `s2`. -/
  | seq      (s1 s2 : KleeneStmt P Cmd)
  /-- Execute either `s1` or `s2`, arbitrarily. -/
  | choice   (s1 s2 : KleeneStmt P Cmd)
  /-- Execute `s` an arbitrary number of times (possibly zero). -/
  | loop     (s : KleeneStmt P Cmd)
  deriving Inhabited

abbrev KleeneStmt.init {P : PureExpr} (name : P.Ident) (ty : P.Ty) (expr : P.Expr) (md : MetaData P) :=
  KleeneStmt.cmd (P:=P) (Cmd.init name ty (.det expr) md)
abbrev KleeneStmt.set {P : PureExpr} (name : P.Ident) (expr : P.Expr) (md : MetaData P) :=
  KleeneStmt.cmd (P:=P) (Cmd.set name (.det expr) md)
abbrev KleeneStmt.havoc {P : PureExpr} (name : P.Ident) (md : MetaData P) :=
  KleeneStmt.cmd (P:=P) (Cmd.set name .nondet md)
abbrev KleeneStmt.assert {P : PureExpr} (label : String) (b : P.Expr) (md : MetaData P) :=
  KleeneStmt.cmd (P:=P) (Cmd.assert label b md)
abbrev KleeneStmt.assume {P : PureExpr} (label : String) (b : P.Expr) (md : MetaData P) :=
  KleeneStmt.cmd (P:=P) (Cmd.assume label b md)

mutual
/-- Get all variables defined by the statement `s`. -/
def KleeneStmt.definedVars [HasVarsImp P C] (s : KleeneStmt P C) : List P.Ident :=
  match s with
  | .cmd c => HasVarsImp.definedVars c
  | .seq s1 s2 => KleeneStmt.definedVars s1 ++ KleeneStmt.definedVars s2
  | .choice s1 s2 => KleeneStmt.definedVars s1 ++ KleeneStmt.definedVars s2
  | .loop s => KleeneStmt.definedVars s

def KleeneStmts.definedVars [HasVarsImp P C] (ss : List (KleeneStmt P C)) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => KleeneStmt.definedVars s ++ KleeneStmts.definedVars srest
end

mutual
/-- Get all variables modified by the statement `s`. -/
def KleeneStmt.modifiedVars [HasVarsImp P C] (s : KleeneStmt P C) : List P.Ident :=
  match s with
  | .cmd c => HasVarsImp.modifiedVars c
  | .seq s1 s2 => KleeneStmt.modifiedVars s1 ++ KleeneStmt.modifiedVars s2
  | .choice s1 s2 => KleeneStmt.modifiedVars s1 ++ KleeneStmt.modifiedVars s2
  | .loop s => KleeneStmt.modifiedVars s

def KleeneStmts.modifiedVars [HasVarsImp P C] (ss : List (KleeneStmt P C)) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => KleeneStmt.modifiedVars s ++ KleeneStmts.modifiedVars srest
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (KleeneStmt P C) where
  definedVars := KleeneStmt.definedVars
  modifiedVars := KleeneStmt.modifiedVars

---------------------------------------------------------------------

/-! ## Formatting -/

open Std (ToFormat Format format)

def formatKleeneStmt (P : PureExpr) (s : KleeneStmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]: Format :=
  match s with
  | .cmd cmd => format cmd
  | .seq s1 s2 => f!"({formatKleeneStmt P s1}) ; ({formatKleeneStmt P s2})"
  | .choice s1 s2 => f!"({formatKleeneStmt P s1}) | ({formatKleeneStmt P s2})"
  | .loop s => f!"({formatKleeneStmt P s})*"

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (KleeneStmt P C) where
  format s := formatKleeneStmt P s

---------------------------------------------------------------------

end -- public section
end Imperative
