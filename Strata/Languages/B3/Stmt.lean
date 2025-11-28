/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Identifiers

namespace B3
open Std (ToFormat Format format)

/--
Call argument for B3 procedure calls
-/
inductive CallArg : Type where
  | expr   (e : Expression)
  | out    (id : String)
  | inout  (id : String)
deriving Repr

/--
B3 Statement type - now using B3AST.Expression directly
-/
inductive Stmt : Type where
  | varDecl     (name : String) (ty : Option String) (autoinv : Option Expression) (init : Option Expression)
  | assign      (lhs : String) (rhs : Expression)
  | reinit      (name : String)
  | blockStmt   (stmts : List Stmt)
  | call        (procName : String) (args : List CallArg)
  | check       (expr : Expression)
  | assume      (expr : Expression)
  | reach       (expr : Expression)
  | assert      (expr : Expression)
  | aForall     (var : String) (ty : String) (body : Stmt)
  | choose      (branches : List Stmt)
  | ifStmt      (cond : Expression) (thenBranch : Stmt) (elseBranch : Option Stmt)
  | ifCase      (cases : List (Expression × Stmt))
  | loop        (invariants : List Expression) (body : Stmt)
  | labeledStmt (label : String) (stmt : Stmt)
  | exit        (label : Option String)
  | returnStmt
  | probe       (label : String)
deriving Repr

/-- Backward compatibility alias -/
abbrev B3Stmt := Stmt

/-- Backward compatibility alias -/
abbrev B3CallArg := CallArg

end B3
