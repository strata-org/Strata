/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.WrittenTyVarScope
public import Strata.Languages.Core.Typing.Props.ExprEraseProps
import Strata.Languages.Core.StatementProps
import all Strata.Languages.Core.Typing.Props.StatementTypeProps
import Strata.DL.Lambda.LExprTEraseProps
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.WrittenTyVarScope
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd

/-! # Type erasure of commands and statements

Key theorems: `Statements.eraseAnnots_mapExpr` (a statement-list map that only changes type
annotations keeps the erasure `Statements.eraseAnnots`), and its instances for the checker's
type-only maps: `Statements.eraseAnnots_map_subst`, `Statements.eraseAnnots_mapStmtsTys`,
`Statements.eraseAnnots_skolemizeStmts` and `Command.eraseAnnots_renameCmd`. -/

namespace Core

open Lambda Imperative

public section

/-! ## Unfolding the erasure -/

/-- Erasing a command statement erases the command. -/
theorem Statement.eraseAnnots_cmd (c : Command) :
    Statement.eraseAnnots (.cmd c) = .cmd (Command.eraseAnnots c) := by
  simp only [Statement.eraseAnnots, Stmt.mapExpr]

/-- Erasing a block erases its body. -/
theorem Statement.eraseAnnots_block (l : String) (bss : List Statement)
    (md : MetaData Expression) :
    Statement.eraseAnnots (.block l bss md) = .block l (Statements.eraseAnnots bss) md := by
  simp only [Statement.eraseAnnots, Statements.eraseAnnots, Stmt.mapExpr]

/-- Erasing a conditional erases its condition and both branches. -/
theorem Statement.eraseAnnots_ite (cond : ExprOrNondet Expression) (tss ess : List Statement)
    (md : MetaData Expression) :
    Statement.eraseAnnots (.ite cond tss ess md) =
      .ite (cond.map LExpr.eraseTypes) (Statements.eraseAnnots tss)
        (Statements.eraseAnnots ess) md := by
  cases cond <;> simp only [Statement.eraseAnnots, Statements.eraseAnnots, Stmt.mapExpr,
    ExprOrNondet.map]

/-- Erasing a loop erases its guard, measure, invariants and body. -/
theorem Statement.eraseAnnots_loop (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (i : List (String × Expression.Expr)) (bss : List Statement) (md : MetaData Expression) :
    Statement.eraseAnnots (.loop g m i bss md) =
      .loop (g.map LExpr.eraseTypes) (m.map LExpr.eraseTypes)
        (i.map fun (l, e) => (l, e.eraseTypes)) (Statements.eraseAnnots bss) md := by
  cases g <;> simp only [Statement.eraseAnnots, Statements.eraseAnnots, Stmt.mapExpr,
    ExprOrNondet.map]

/-- Erasing an exit leaves it unchanged. -/
private theorem Statement.eraseAnnots_exit (l : String) (md : MetaData Expression) :
    Statement.eraseAnnots (.exit l md) = .exit l md := by
  simp only [Statement.eraseAnnots, Stmt.mapExpr]

/-- Erasing a type declaration leaves it unchanged. -/
private theorem Statement.eraseAnnots_typeDecl (t : TypeConstructor) (md : MetaData Expression) :
    Statement.eraseAnnots (.typeDecl t md) = .typeDecl t md := by
  simp only [Statement.eraseAnnots, Stmt.mapExpr]

/-- Erasing the empty statement list gives the empty list. -/
theorem Statements.eraseAnnots_nil : Statements.eraseAnnots [] = [] := by
  simp only [Statements.eraseAnnots, Block.mapExpr]

/-- Erasing a statement list erases its head and its tail. -/
theorem Statements.eraseAnnots_cons (s : Statement) (rest : List Statement) :
    Statements.eraseAnnots (s :: rest) =
      Statement.eraseAnnots s :: Statements.eraseAnnots rest := by
  simp only [Statement.eraseAnnots, Statements.eraseAnnots, Block.mapExpr]

/-- Erasing the concatenation of two statement lists erases each. -/
theorem Statements.eraseAnnots_append (ss ts : List Statement) :
    Statements.eraseAnnots (ss ++ ts) =
      Statements.eraseAnnots ss ++ Statements.eraseAnnots ts := by
  induction ss with
  | nil => simp only [List.nil_append, Statements.eraseAnnots_nil]
  | cons s rest ih =>
    simp only [List.cons_append, Statements.eraseAnnots_cons, ih]

/-! ## Calls -/

/-- Mapping an erasure-preserving function over the input expressions of call arguments keeps
    their erasure. -/
private theorem CallArg.map_mapInput_eraseTypes (g : Expression.Expr → Expression.Expr)
    (hg : ∀ e, (g e).eraseTypes = e.eraseTypes) (args : List (CallArg Expression)) :
    (args.map (CallArg.mapInput g)).map (CallArg.mapInput LExpr.eraseTypes) =
      args.map (CallArg.mapInput LExpr.eraseTypes) := by
  simp only [List.map_map]
  refine List.map_congr_left fun a _ => ?_
  cases a <;> simp only [Function.comp, CallArg.mapInput, hg]

/-- Replacing the input expressions of a call by expressions with the same erasure, position by
    position, keeps the erasure of the call's arguments. -/
theorem CallArg.replaceInArgs_mapInput_eraseTypes :
    ∀ (args : List (CallArg Expression)) (L : List Expression.Expr),
      L.map LExpr.eraseTypes = (CallArg.getInputExprs args).map LExpr.eraseTypes →
      (CallArg.replaceInArgs args L).map (CallArg.mapInput LExpr.eraseTypes) =
        args.map (CallArg.mapInput LExpr.eraseTypes)
  | [], L, _ => rfl
  | .inArg e :: rest, L, h => by
    rw [CallArg.getInputExprs_cons_inArg] at h
    cases L with
    | nil => simp only [List.map_nil, List.map_cons, reduceCtorEq] at h
    | cons l Lrest =>
      simp only [List.map_cons, List.cons.injEq] at h
      have ih := CallArg.replaceInArgs_mapInput_eraseTypes rest Lrest h.2
      simp only [CallArg.replaceInArgs, CallArg.replaceInArgs.go, List.map_cons,
        CallArg.mapInput, h.1] at ih ⊢
      rw [ih]
  | .inoutArg id :: rest, L, h => by
    rw [CallArg.getInputExprs_cons_inoutArg] at h
    cases L with
    | nil => simp only [List.map_nil, List.map_cons, reduceCtorEq] at h
    | cons l Lrest =>
      simp only [List.map_cons, List.cons.injEq] at h
      have ih := CallArg.replaceInArgs_mapInput_eraseTypes rest Lrest h.2
      simp only [CallArg.replaceInArgs, CallArg.replaceInArgs.go, List.map_cons,
        CallArg.mapInput] at ih ⊢
      rw [ih]
  | .outArg id :: rest, L, h => by
    rw [CallArg.getInputExprs_cons_outArg] at h
    have ih := CallArg.replaceInArgs_mapInput_eraseTypes rest L h
    simp only [CallArg.replaceInArgs, CallArg.replaceInArgs.go, List.map_cons,
      CallArg.mapInput] at ih ⊢
    rw [ih]

/-! ## Type-only maps on commands -/

/-- Applying a type substitution to a command keeps its erasure. -/
theorem Command.eraseAnnots_subst (S : Subst) (c : Command) :
    Command.eraseAnnots (Statement.Command.subst S c) = Command.eraseAnnots c := by
  have hg : ∀ e : Expression.Expr, (LExpr.applyTypeSubst e S).eraseTypes = e.eraseTypes :=
    fun e => LExpr.eraseTypes_applyTypeSubst e S
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases e <;> simp only [Statement.Command.subst, Statement.Cmd.subst,
        Statement.substExprOrNondet, ExprOrNondet.map, Command.eraseAnnots, Command.mapExpr, hg]
    | set x e md =>
      cases e <;> simp only [Statement.Command.subst, Statement.Cmd.subst,
        Statement.substExprOrNondet, ExprOrNondet.map, Command.eraseAnnots, Command.mapExpr, hg]
    | assert l b md =>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Command.eraseAnnots,
        Command.mapExpr, hg]
    | assume l b md =>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Command.eraseAnnots,
        Command.mapExpr, hg]
    | cover l b md =>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Command.eraseAnnots,
        Command.mapExpr, hg]
  | call pname tyArgs args md =>
    simp only [Statement.Command.subst, Command.eraseAnnots, Command.mapExpr,
      List.map_map]
    have h := CallArg.map_mapInput_eraseTypes (fun e => LExpr.applyTypeSubst e S) hg args
    simp only [Statement.CallArg.subst, List.map_map] at h ⊢
    rw [h]

/-- Rewriting the expressions of a command by an erasure-preserving function, and its declared
    types by any function, keeps its erasure. -/
private theorem Command.eraseAnnots_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (hg : ∀ e, (fe e).eraseTypes = e.eraseTypes) (c : Command) :
    Command.eraseAnnots (mapCmdWith fe ft c) = Command.eraseAnnots c := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases e <;> simp only [mapCmdWith, ExprOrNondet.map, Command.eraseAnnots,
        Command.mapExpr, hg]
    | set x e md =>
      cases e <;> simp only [mapCmdWith, ExprOrNondet.map, Command.eraseAnnots,
        Command.mapExpr, hg]
    | assert l b md => simp only [mapCmdWith, Command.eraseAnnots, Command.mapExpr, hg]
    | assume l b md => simp only [mapCmdWith, Command.eraseAnnots, Command.mapExpr, hg]
    | cover l b md => simp only [mapCmdWith, Command.eraseAnnots, Command.mapExpr, hg]
  | call pname tyArgs args md =>
    simp only [mapCmdWith, Command.eraseAnnots, Command.mapExpr]
    rw [CallArg.map_mapInput_eraseTypes _ hg]

/-- Rewriting the type annotations of a command keeps its erasure. -/
theorem Command.eraseAnnots_mapCmdTys (f : LMonoTy → LMonoTy) (c : Command) :
    Command.eraseAnnots (mapCmdTys f c) = Command.eraseAnnots c :=
  Command.eraseAnnots_mapCmdWith (mapExprTys f) f (fun e => LExpr.eraseTypes_mapExprTys f e) c

/-- Skolemizing a command keeps its erasure. -/
theorem Command.eraseAnnots_skolemizeCmd (nm : Option String) (σ : RigidNames) (c : Command) :
    Command.eraseAnnots (skolemizeCmd nm σ c) = Command.eraseAnnots c :=
  Command.eraseAnnots_mapCmdWith (skolemizeBody nm σ) (skolemizeTy σ)
    (fun e => eraseTypes_skolemizeBody nm σ e) c

/-- Renaming the written type variables of a command into a scope keeps its erasure. -/
theorem Command.eraseAnnots_renameCmd (rigid : List TyIdentifier)
    (m : WrittenTyVarScope.ScopeMap) (st : WrittenTyVarScope.ScopeState) (c : Command) :
    Command.eraseAnnots (WrittenTyVarScope.renameCmd rigid m st c).1 = Command.eraseAnnots c := by
  have hg : ∀ (m : WrittenTyVarScope.ScopeMap) (e : Expression.Expr),
      (WrittenTyVarScope.renameExpr m e).eraseTypes = e.eraseTypes :=
    fun m e => WrittenTyVarScope.eraseTypes_renameExpr m e
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases ty with
      | forAll vars ty =>
        cases vars with
        | nil =>
          cases e <;> simp only [WrittenTyVarScope.renameCmd, WrittenTyVarScope.renameExprOrNondet,
            ExprOrNondet.map, Command.eraseAnnots, Command.mapExpr, hg]
        | cons a as => simp only [WrittenTyVarScope.renameCmd]
    | set x e md =>
      cases e <;> simp only [WrittenTyVarScope.renameCmd, WrittenTyVarScope.renameExprOrNondet,
        ExprOrNondet.map, Command.eraseAnnots, Command.mapExpr, hg]
    | assert l b md =>
      simp only [WrittenTyVarScope.renameCmd, Command.eraseAnnots, Command.mapExpr, hg]
    | assume l b md =>
      simp only [WrittenTyVarScope.renameCmd, Command.eraseAnnots, Command.mapExpr, hg]
    | cover l b md =>
      simp only [WrittenTyVarScope.renameCmd, Command.eraseAnnots, Command.mapExpr, hg]
  | call pname tyArgs args md =>
    simp only [WrittenTyVarScope.renameCmd, WrittenTyVarScope.renameCallArgs,
      Command.eraseAnnots, Command.mapExpr]
    rw [CallArg.map_mapInput_eraseTypes _ (hg m)]

/-! ## Type-only maps on statements -/

/-- A statement-list map that rewrites expressions by an erasure-preserving function and
    commands by an erasure-preserving function keeps the erasure of the list. -/
private theorem Statements.eraseAnnots_mapExpr (g : Expression.Expr → Expression.Expr)
    (mc : Command → Command) (hg : ∀ e, (g e).eraseTypes = e.eraseTypes)
    (hmc : ∀ c, Command.eraseAnnots (mc c) = Command.eraseAnnots c) (ss : List Statement) :
    Statements.eraseAnnots (Block.mapExpr g mc ss) = Statements.eraseAnnots ss := by
  have hcomp : (LExpr.eraseTypes ∘ g) = LExpr.eraseTypes := funext hg
  have hpair : ((fun x : String × Expression.Expr => (x.1, x.2.eraseTypes)) ∘
      fun x : String × Expression.Expr => (x.1, g x.2)) =
        fun x : String × Expression.Expr => (x.1, x.2.eraseTypes) := by
    funext x
    simp only [Function.comp, hg]
  induction ss using Block.mapExpr.induct
    (motive1 := fun s => Statement.eraseAnnots (Stmt.mapExpr g mc s) = Statement.eraseAnnots s) <;>
    simp_all only [Stmt.mapExpr, Block.mapExpr, Statement.eraseAnnots_cmd,
      Statement.eraseAnnots_block, Statement.eraseAnnots_ite, Statement.eraseAnnots_loop,
      Statement.eraseAnnots_exit, Statement.eraseAnnots_typeDecl, Statements.eraseAnnots_nil,
      Statements.eraseAnnots_cons, ExprOrNondet.map, Option.map_map, List.map_map]
  all_goals simp only [hcomp, hpair]

/-- Rewriting the type annotations of a statement list keeps its erasure. -/
theorem Statements.eraseAnnots_mapStmtsTys (f : LMonoTy → LMonoTy) (ss : List Statement) :
    Statements.eraseAnnots (mapStmtsTys f ss) = Statements.eraseAnnots ss :=
  Statements.eraseAnnots_mapExpr (mapExprTys f) (mapCmdTys f)
    (fun e => LExpr.eraseTypes_mapExprTys f e) (Command.eraseAnnots_mapCmdTys f) ss

/-- Applying a type substitution to each statement of a list is the statement-list map of the
    substitution on expressions and commands. -/
private theorem map_subst_eq_mapExpr (S : Subst) (ss : List Statement) :
    ss.map (Statement.Statement.subst S) =
      Block.mapExpr (fun e => LExpr.applyTypeSubst e S) (Statement.Command.subst S) ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      Statement.Statement.subst S s =
        Stmt.mapExpr (fun e => LExpr.applyTypeSubst e S) (Statement.Command.subst S) s) <;>
    simp_all only [Statement.Statement.subst, Stmt.mapExpr, Block.mapExpr, Statement_subst_go_eq,
      List.reverse_nil, List.nil_append, List.map_cons, List.map_nil, ExprOrNondet.map]

/-- Applying a type substitution to each statement of a list keeps the list's erasure. -/
theorem Statements.eraseAnnots_map_subst (S : Subst) (ss : List Statement) :
    Statements.eraseAnnots (ss.map (Statement.Statement.subst S)) = Statements.eraseAnnots ss := by
  rw [map_subst_eq_mapExpr]
  exact Statements.eraseAnnots_mapExpr _ _ (fun e => LExpr.eraseTypes_applyTypeSubst e S)
    (Command.eraseAnnots_subst S) ss

/-- Skolemizing a statement list is the statement-list map of skolemization on expressions and
    commands. -/
private theorem skolemizeStmts_eq_mapExpr (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    skolemizeStmts nm σ ss = Block.mapExpr (skolemizeBody nm σ) (skolemizeCmd nm σ) ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      skolemizeStmt nm σ s = Stmt.mapExpr (skolemizeBody nm σ) (skolemizeCmd nm σ) s) <;>
    simp_all only [skolemizeStmt, skolemizeStmts, Stmt.mapExpr, Block.mapExpr]

/-- Skolemizing a statement list keeps its erasure. -/
theorem Statements.eraseAnnots_skolemizeStmts (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    Statements.eraseAnnots (skolemizeStmts nm σ ss) = Statements.eraseAnnots ss := by
  rw [skolemizeStmts_eq_mapExpr]
  exact Statements.eraseAnnots_mapExpr _ _ (eraseTypes_skolemizeBody nm σ)
    (Command.eraseAnnots_skolemizeCmd nm σ) ss

end

end Core
