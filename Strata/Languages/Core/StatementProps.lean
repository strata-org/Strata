/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.DL.Imperative.StmtProps
import all Strata.Languages.Core.Statement

/-! # Structural properties of Core statements

Structural (syntactic) lemmas about `Core.Statement`.  Currently: the Core
expression-mapping wrappers `Statement.mapExprs` / `Statements.mapExprs` preserve
`Imperative.Stmt.noFuncDecl` — mapping expressions never introduces or removes a
`funcDecl`.  These specialize the generic `Imperative.Stmt.noFuncDecl_mapExpr` /
`Block.noFuncDecl_mapExpr` (in `Strata.DL.Imperative.StmtProps`) to the Core
command mapper, and are used by `LiftInternalFuncDeclsCorrect` to show the lift
pass leaves no `funcDecl` behind after rewriting call sites with
`Statements.mapExprs`.

Key results:
- `Statement.noFuncDecl_mapExprs` — `Statement.mapExprs` preserves `noFuncDecl`.
- `Statements.noFuncDecl_mapExprs` — `Statements.mapExprs` preserves `noFuncDecl`.
-/

public section

namespace Core

open Imperative

/-- `Statements.mapExprs` is `Block.mapExpr` with the Core command mapper. -/
private theorem Statements.mapExprs_eq (f : Expression.Expr → Expression.Expr) (ss : Statements) :
    Statements.mapExprs f ss = Block.mapExpr f (Command.mapExpr f) ss := by
  induction ss with
  | nil => simp [Statements.mapExprs, Block.mapExpr]
  | cons s rest ih =>
    simp only [Statements.mapExprs, List.map_cons, Block.mapExpr, Statement.mapExprs] at *
    rw [ih]

/-- `Statement.mapExprs` preserves `noFuncDecl`. -/
@[simp] theorem Statement.noFuncDecl_mapExprs (f : Expression.Expr → Expression.Expr) (s : Statement) :
    Stmt.noFuncDecl (Statement.mapExprs f s) = Stmt.noFuncDecl s :=
  Imperative.Stmt.noFuncDecl_mapExpr f (Command.mapExpr f) s

/-- `Statements.mapExprs` preserves `noFuncDecl`: rewriting the expressions in a
block (as the lift pass does to its call sites) never introduces or removes a
`funcDecl`. -/
@[simp] theorem Statements.noFuncDecl_mapExprs (f : Expression.Expr → Expression.Expr) (ss : Statements) :
    Block.noFuncDecl (Statements.mapExprs f ss) = Block.noFuncDecl ss := by
  rw [Statements.mapExprs_eq]
  exact Imperative.Block.noFuncDecl_mapExpr f (Command.mapExpr f) ss

end Core

end -- public section
