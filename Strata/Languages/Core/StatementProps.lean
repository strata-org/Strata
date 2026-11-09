/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd

/-! # Properties of Core statements

Per-constructor equations for `mapStmtTys` and `mapStmtsTys`, which are defined
through the well-founded `Stmt.mapExpr` and `Block.mapExpr`.
-/

namespace Core

open Lambda Imperative

public section

/-- Mapping type annotations over a command statement maps them over the
    command. -/
theorem mapStmtTys_cmd (f : LMonoTy → LMonoTy) (c : Command) :
    mapStmtTys f (.cmd c) = .cmd (mapCmdTys f c) := by
  simp only [mapStmtTys, Stmt.mapExpr]

/-- Mapping type annotations over a labeled block maps them over its body. -/
theorem mapStmtTys_block (f : LMonoTy → LMonoTy) (l : String) (bss : List Statement)
    (md : MetaData Expression) :
    mapStmtTys f (.block l bss md) = .block l (mapStmtsTys f bss) md := by
  simp only [mapStmtTys, mapStmtsTys, Stmt.mapExpr]

/-- Mapping type annotations over a conditional maps them over its condition
    and both branches. -/
theorem mapStmtTys_ite (f : LMonoTy → LMonoTy) (cond : ExprOrNondet Expression)
    (tss ess : List Statement) (md : MetaData Expression) :
    mapStmtTys f (.ite cond tss ess md) =
      .ite (cond.map (mapExprTys f ·)) (mapStmtsTys f tss) (mapStmtsTys f ess) md := by
  cases cond <;> simp only [mapStmtTys, mapStmtsTys, Stmt.mapExpr, ExprOrNondet.map]

/-- Mapping type annotations over a loop maps them over its guard, measure,
    invariants and body. -/
theorem mapStmtTys_loop (f : LMonoTy → LMonoTy) (g : ExprOrNondet Expression)
    (m : Option Expression.Expr) (i : List (String × Expression.Expr))
    (bss : List Statement) (md : MetaData Expression) :
    mapStmtTys f (.loop g m i bss md) =
      .loop (g.map (mapExprTys f ·)) (m.map (mapExprTys f ·))
        (i.map (fun (l, e) => (l, mapExprTys f e))) (mapStmtsTys f bss) md := by
  cases g <;> simp only [mapStmtTys, mapStmtsTys, Stmt.mapExpr, ExprOrNondet.map]

/-- Mapping type annotations leaves an exit unchanged. -/
theorem mapStmtTys_exit (f : LMonoTy → LMonoTy) (l : String)
    (md : MetaData Expression) :
    mapStmtTys f (.exit l md) = .exit l md := by
  simp only [mapStmtTys, Stmt.mapExpr]

/-- Mapping type annotations leaves a type declaration unchanged. -/
theorem mapStmtTys_typeDecl (f : LMonoTy → LMonoTy) (t : TypeConstructor)
    (md : MetaData Expression) :
    mapStmtTys f (.typeDecl t md) = .typeDecl t md := by
  simp only [mapStmtTys, Stmt.mapExpr]

/-- Mapping type annotations over the empty statement list gives the empty
    list. -/
theorem mapStmtsTys_nil (f : LMonoTy → LMonoTy) : mapStmtsTys f [] = [] := by
  simp only [mapStmtsTys, Block.mapExpr]

/-- Mapping type annotations over a statement list maps them over its head and
    its tail. -/
theorem mapStmtsTys_cons (f : LMonoTy → LMonoTy) (s : Statement) (rest : List Statement) :
    mapStmtsTys f (s :: rest) = mapStmtTys f s :: mapStmtsTys f rest := by
  simp only [mapStmtTys, mapStmtsTys, Block.mapExpr]

end

end Core
