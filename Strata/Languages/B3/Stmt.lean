/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Identifiers

namespace B3
open Std (ToFormat Format format)

/--
Type parameters for B3 Statement.
-/
structure StmtParams : Type 1 where
  Metadata : Type
  exprParams : ExprParams

abbrev StmtParams.Identifier (P : StmtParams) : Type := P.exprParams.Identifier

/--
Call argument for B3 procedure calls
-/
inductive CallArg (P : StmtParams) : Type where
  | expr   (e : Expression P.exprParams)
  | out    (id : P.Identifier)
  | inout  (id : P.Identifier)

/--
B3 Statement type - a proper tree structure parameterized by metadata.
Metadata is for the statement nodes, ExprMetadata is for expression nodes, IDMeta is for identifiers.
-/
inductive Stmt (P : StmtParams) : Type where
  | varDecl     (md : P.Metadata) (name : P.Identifier) (ty : Option String) (autoinv : Option (Expression P.exprParams)) (init : Option (Expression P.exprParams))
  | assign      (md : P.Metadata) (lhs : P.Identifier) (rhs : Expression P.exprParams)
  | reinit      (md : P.Metadata) (name : P.Identifier)
  | blockStmt   (md : P.Metadata) (stmts : List (Stmt P))
  | call        (md : P.Metadata) (procName : String) (args : List (CallArg P))
  -- assertions
  | check       (md : P.Metadata) (expr : Expression P.exprParams)
  | assume      (md : P.Metadata) (expr : Expression P.exprParams)
  | reach       (md : P.Metadata) (expr : Expression P.exprParams)
  | assert      (md : P.Metadata) (expr : Expression P.exprParams)
  | aForall     (md : P.Metadata) (var : P.Identifier) (ty : String) (body : Stmt P)
  -- control flow
  | choose      (md : P.Metadata) (branches : List (Stmt P))
  | ifStmt      (md : P.Metadata) (cond : Expression P.exprParams) (thenBranch : Stmt P) (elseBranch : Option (Stmt P))
  | ifCase      (md : P.Metadata) (cases : List (Expression P.exprParams × Stmt P))
  | loop        (md : P.Metadata) (invariants : List (Expression P.exprParams)) (body : Stmt P)
  | labeledStmt (md : P.Metadata) (label : String) (stmt : Stmt P)
  | exit        (md : P.Metadata) (label : Option String)
  | returnStmt  (md : P.Metadata)
  -- error reporting
  | probe       (md : P.Metadata) (label : String)

mutual
def CallArg.sizeOf : CallArg P → Nat
  | .expr e => e.sizeOf
  | .out _ => 1
  | .inout _ => 1

def CallArg.sizeOfList : List (CallArg P) → Nat
  | [] => 0
  | a :: as => a.sizeOf + CallArg.sizeOfList as

def Stmt.sizeOf : Stmt P → Nat
  | .varDecl _ _ _ autoinv init => 1 + (autoinv.map Expression.sizeOf).getD 0 + (init.map Expression.sizeOf).getD 0
  | .assign _ _ rhs => 1 + rhs.sizeOf
  | .reinit _ _ => 1
  | .blockStmt _ stmts => 1 + Stmt.sizeOfList stmts
  | .call _ _ args => 1 + CallArg.sizeOfList args
  | .check _ expr => 1 + expr.sizeOf
  | .assume _ expr => 1 + expr.sizeOf
  | .reach _ expr => 1 + expr.sizeOf
  | .assert _ expr => 1 + expr.sizeOf
  | .aForall _ _ _ body => 1 + body.sizeOf
  | .choose _ branches => 1 + Stmt.sizeOfList branches
  | .ifStmt _ cond thenB elseB =>
    1 + cond.sizeOf + thenB.sizeOf + match elseB with | some s => s.sizeOf | none => 0
  | .ifCase _ cases =>
    1 + Stmt.sizeOfCases cases
  | .loop _ invariants body => 1 + Expression.sizeOfList invariants + body.sizeOf
  | .labeledStmt _ _ stmt => 1 + stmt.sizeOf
  | .exit _ _ => 1
  | .returnStmt _ => 1
  | .probe _ _ => 1
  termination_by s => sizeOf s

def Stmt.sizeOfList : List (Stmt P) → Nat
  | [] => 0
  | s :: ss => s.sizeOf + Stmt.sizeOfList ss
  termination_by ss => sizeOf ss

def Stmt.sizeOfCases : List (Expression P.exprParams × Stmt P) → Nat
  | [] => 0
  | (e, s) :: cs => e.sizeOf + s.sizeOf + Stmt.sizeOfCases cs
  termination_by cs => sizeOf cs
end

instance : SizeOf (CallArg P) where
  sizeOf := CallArg.sizeOf

instance : SizeOf (Stmt P) where
  sizeOf := Stmt.sizeOf

---------------------------------------------------------------------
-- Repr Instances
---------------------------------------------------------------------

mutual
partial def CallArg.repr [Repr P.Metadata] [Repr P.exprParams.Metadata] [Repr P.Identifier] : CallArg P → String
  | .expr e => ".expr (" ++ Expression.repr e ++ ")"
  | .out id => s!".out {reprArg id}"
  | .inout id => s!".inout {reprArg id}"

partial def Stmt.repr [Repr P.Metadata] [Repr P.exprParams.Metadata] [Repr P.Identifier] : Stmt P → String
  | .varDecl md name ty autoinv init =>
      let tyRepr := match ty with | some t => s!"(some {reprArg t})" | none => "none"
      let autoinvRepr := match autoinv with | some e => s!"(some ({Expression.repr e}))" | none => "none"
      let initRepr := match init with | some e => s!"(some ({Expression.repr e}))" | none => "none"
      s!".varDecl {reprArg md} {reprArg name} {tyRepr} {autoinvRepr} {initRepr}"
  | .assign md lhs rhs => s!".assign {reprArg md} {reprArg lhs} ({Expression.repr rhs})"
  | .reinit md name => s!".reinit {reprArg md} {reprArg name}"
  | .blockStmt md stmts =>
      let stmtsRepr := "[" ++ String.intercalate ", " (stmts.map Stmt.repr) ++ "]"
      s!".blockStmt {reprArg md} {stmtsRepr}"
  | .call md procName args =>
      let argsRepr := "[" ++ String.intercalate ", " (args.map CallArg.repr) ++ "]"
      s!".call {reprArg md} {reprArg procName} {argsRepr}"
  | .check md expr => s!".check {reprArg md} ({Expression.repr expr})"
  | .assume md expr => s!".assume {reprArg md} ({Expression.repr expr})"
  | .reach md expr => s!".reach {reprArg md} ({Expression.repr expr})"
  | .assert md expr => s!".assert {reprArg md} ({Expression.repr expr})"
  | .aForall md var ty body => s!".aForall {reprArg md} {reprArg var} {reprArg ty} ({Stmt.repr body})"
  | .choose md branches =>
      let branchesRepr := "[" ++ String.intercalate ", " (branches.map Stmt.repr) ++ "]"
      s!".choose {reprArg md} {branchesRepr}"
  | .ifStmt md cond thenB elseB =>
      let elseRepr := match elseB with | some s => s!"(some ({Stmt.repr s}))" | none => "none"
      s!".ifStmt {reprArg md} ({Expression.repr cond}) ({Stmt.repr thenB}) {elseRepr}"
  | .ifCase md cases =>
      let casesRepr := "[" ++ String.intercalate ", " (cases.map fun (e, s) => s!"({Expression.repr e}, {Stmt.repr s})") ++ "]"
      s!".ifCase {reprArg md} {casesRepr}"
  | .loop md invariants body =>
      let invsRepr := "[" ++ String.intercalate ", " (invariants.map Expression.repr) ++ "]"
      s!".loop {reprArg md} {invsRepr} ({Stmt.repr body})"
  | .labeledStmt md label stmt => s!".labeledStmt {reprArg md} {reprArg label} ({Stmt.repr stmt})"
  | .exit md label =>
      let labelRepr := match label with | some l => s!"(some {reprArg l})" | none => "none"
      s!".exit {reprArg md} {labelRepr}"
  | .returnStmt md => s!".returnStmt {reprArg md}"
  | .probe md label => s!".probe {reprArg md} {reprArg label}"
end

instance [Repr P.Metadata] [Repr P.exprParams.Metadata] [Repr P.Identifier] : Repr (CallArg P) where
  reprPrec a _ := CallArg.repr a

instance [Repr P.Metadata] [Repr P.exprParams.Metadata] [Repr P.Identifier] : Repr (Stmt P) where
  reprPrec s _ := Stmt.repr s

-- Formatting is now handled by converting to DDM and using DDM's formatting
-- Statement and CallArg converters would be added to B3AST2DDM when needed

/-- Default StmtParams with Unit metadata and B3IdentifierMetadata -/
def defaultStmtParams : StmtParams := {
  Metadata := Unit
  exprParams := defaultExprParams
}

/-- B3 Statement with default parameters -/
abbrev B3Stmt := Stmt defaultStmtParams

/-- B3 CallArg with default parameters -/
abbrev B3CallArg := CallArg defaultStmtParams

instance : Repr Unit where
  reprPrec _ _ := "()"

instance : Repr B3IdentifierMetadata where
  reprPrec _ _ := "()"

instance : Repr (Lambda.Identifier B3IdentifierMetadata) where
  reprPrec id _ := id.name

instance : Repr B3Stmt where
  reprPrec s _ := @Stmt.repr defaultStmtParams (inferInstanceAs (Repr Unit)) (inferInstanceAs (Repr Unit)) (inferInstanceAs (Repr (Lambda.Identifier B3IdentifierMetadata))) s

instance : Repr B3CallArg where
  reprPrec a _ := @CallArg.repr defaultStmtParams (inferInstanceAs (Repr Unit)) (inferInstanceAs (Repr Unit)) (inferInstanceAs (Repr (Lambda.Identifier B3IdentifierMetadata))) a

/-- B3 Identifier for statements (same as B3Ident) -/
abbrev B3StmtIdent := defaultStmtParams.Identifier

instance : Std.ToFormat defaultStmtParams.Metadata := inferInstanceAs (Std.ToFormat Unit)
instance : Std.ToFormat defaultStmtParams.exprParams.Metadata := inferInstanceAs (Std.ToFormat Unit)
instance : Std.ToFormat defaultStmtParams.Identifier := inferInstanceAs (Std.ToFormat (Lambda.Identifier B3IdentifierMetadata))

instance : Coe String defaultStmtParams.Identifier where
  coe s := B3Ident.mk s

end B3
