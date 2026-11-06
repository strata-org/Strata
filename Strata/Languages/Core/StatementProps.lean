/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.DL.Imperative.StmtProps
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd

/-! # Properties of Core statements

Per-constructor equations for `mapStmtTys` and `mapStmtsTys`, which are defined
through the well-founded `Stmt.mapExpr` and `Block.mapExpr`, and for
`Statement.noCalls` and `Statements.noCalls`.
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

/-! ## No procedure call, one constructor at a time -/

/-- A list makes no call exactly when its head and its rest make none. -/
theorem noCalls_eq_cons (s : Statement) (rest : List Statement) :
    Statements.noCalls (s :: rest) = (Statement.noCalls s && Statements.noCalls rest) := by
  rw [Statements.noCalls, Imperative.Block.allSubstmts_cons]; rfl

/-- A block makes no call exactly when its body makes none. -/
theorem noCalls_eq_block (l : String) (ss : List Statement) (md : MetaData Expression) :
    Statement.noCalls (.block l ss md) = Statements.noCalls ss := by
  rw [Statement.noCalls, Imperative.Stmt.allSubstmts_block]; rfl

/-- A conditional makes no call exactly when neither arm makes one. -/
theorem noCalls_eq_ite (c : ExprOrNondet Expression) (ts es : List Statement)
    (md : MetaData Expression) :
    Statement.noCalls (.ite c ts es md) = (Statements.noCalls ts && Statements.noCalls es) := by
  rw [Statement.noCalls, Imperative.Stmt.allSubstmts_ite]; rfl

/-- A loop makes no call exactly when its body makes none. -/
theorem noCalls_eq_loop (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (md : MetaData Expression) :
    Statement.noCalls (.loop g m invs body md) = Statements.noCalls body := by
  rw [Statement.noCalls, Imperative.Stmt.allSubstmts_loop]; rfl

/-- The empty statement list makes no procedure call. -/
theorem noCalls_nil : Statements.noCalls [] = true :=
  Imperative.Block.allSubstmts_nil _

/-- A list without calls has its head statement and its tail without calls. -/
theorem noCalls_cons {s : Statement} {rest : List Statement}
    (h : Statements.noCalls (s :: rest) = true) :
    Statement.noCalls s = true ∧ Statements.noCalls rest = true := by
  rwa [noCalls_eq_cons, Bool.and_eq_true] at h

/-- A statement without calls is a one-element list without calls. -/
theorem noCalls_singleton {s : Statement}
    (h : Statement.noCalls s = true) : Statements.noCalls [s] = true := by
  rw [noCalls_eq_cons, h, noCalls_nil, Bool.and_self]

/-- The body of a block without calls has none. -/
theorem noCalls_block {l : String} {ss : List Statement} {md : MetaData Expression}
    (h : Statement.noCalls (.block l ss md) = true) : Statements.noCalls ss = true := by
  rwa [noCalls_eq_block] at h

/-- Both arms of a conditional without calls have none. -/
theorem noCalls_ite {c : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} (h : Statement.noCalls (.ite c ts es md) = true) :
    Statements.noCalls ts = true ∧ Statements.noCalls es = true := by
  rwa [noCalls_eq_ite, Bool.and_eq_true] at h

/-- The body of a loop without calls has none. -/
theorem noCalls_loop {g : ExprOrNondet Expression} {m : Option Expression.Expr}
    {invs : List (String × Expression.Expr)} {body : List Statement}
    {md : MetaData Expression} (h : Statement.noCalls (.loop g m invs body md) = true) :
    Statements.noCalls body = true := by
  rwa [noCalls_eq_loop] at h

/-- A command statement without calls carries a base command. -/
theorem exists_baseCmd_of_noCalls {c : Command} (h : Statement.noCalls (.cmd c) = true) :
    ∃ c' : Imperative.Cmd Expression, c = .cmd c' := by
  cases c with
  | cmd c' => exact ⟨c', rfl⟩
  | call n args md =>
    rw [Statement.noCalls, Imperative.Stmt.allSubstmts_cmd] at h; cases h

end

end Core
