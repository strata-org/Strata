/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
import Strata.Util.Tactics

---------------------------------------------------------------------

namespace Imperative

public section

/-! ## Execution Environment

An `Env` bundles the store, expression evaluator, and a cumulative failure
flag into a single record.  The `hasFailure` flag is OR-ed with the
per-command failure flag returned by `EvalCmdParam` at each `cmd_sem`,
so it monotonically accumulates assertion failures along an execution path.
-/

/-- Execution environment: store, evaluator, and cumulative failure flag. -/
structure Env (P : PureExpr) where
  /-- The current variable store. -/
  store : SemanticStore P
  /-- The current expression evaluator. -/
  eval  : SemanticEval P
  /-- Cumulative failure flag — `true` once any command has signalled failure. -/
  hasFailure : Bool := false

/-- Type of a function that extends the semantic evaluator with a new function definition. -/
@[expose] abbrev ExtendEval (P : PureExpr) := SemanticEval P → SemanticStore P → PureFunc P → SemanticEval P

mutual

/--
An inductively-defined big-step operational semantics that depends on
environment lookup and evaluation functions for expressions.

Note that `EvalStmt` is parameterized by commands `Cmd` as well as their
evaluation relation `EvalCmd`, and by `extendEval` which specifies how
`funcDecl` statements extend the evaluator.

The expression evaluator `δ` is threaded as state to support `funcDecl`,
which extends the evaluator with new function definitions. Commands do not
modify the evaluator, only `funcDecl` statements do.

The `Env` bundles the store, evaluator, and cumulative failure flag.
Commands may update the store and set the failure flag; only `funcDecl`
modifies the evaluator.
-/
inductive EvalStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  Env P → Stmt P Cmd → Env P → Prop where
  | cmd_sem :
    EvalCmd ρ.eval ρ.store c σ' hasAssertFailure →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    -- For example, if we require definedness on a block, then we won't be able to evaluate
    -- a block containing init x; havoc x, because it will require x to exist prior to the block
    isDefinedOver (HasVarsImp.modifiedVars) ρ.store c →
    ----
    EvalStmt P Cmd EvalCmd extendEval
      ρ (Stmt.cmd c) { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure }

  | block_sem :
    EvalBlock P Cmd EvalCmd extendEval ρ b ρ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval ρ (.block _ b md) ρ'

  | ite_true_sem :
    ρ.eval ρ.store c = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    EvalBlock P Cmd EvalCmd extendEval ρ t ρ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval ρ (.ite c t e md) ρ'

  | ite_false_sem :
    ρ.eval ρ.store c = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    EvalBlock P Cmd EvalCmd extendEval ρ e ρ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval ρ (.ite c t e md) ρ'

  | funcDecl_sem [HasSubstFvar P] [HasVarsPure P P.Expr] :
    EvalStmt P Cmd EvalCmd extendEval
      ρ (.funcDecl decl md) { ρ with eval := extendEval ρ.eval ρ.store decl }

  | typeDecl_sem :
    EvalStmt P Cmd EvalCmd extendEval ρ (.typeDecl tc md) ρ

  -- (TODO): Define semantics of `exit`.

inductive EvalBlock (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
    Env P → List (Stmt P Cmd) → Env P → Prop where
  | stmts_none_sem :
    EvalBlock P _ _ _ ρ [] ρ
  | stmts_some_sem :
    EvalStmt P Cmd EvalCmd extendEval ρ s ρ' →
    EvalBlock P Cmd EvalCmd extendEval ρ' ss ρ'' →
    EvalBlock P Cmd EvalCmd extendEval ρ (s :: ss) ρ''

end

theorem eval_stmts_singleton
  {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {s : Stmt P Cmd}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval ρ [s] ρ' ↔
  EvalStmt P Cmd EvalCmd extendEval ρ s ρ' := by
  constructor <;> intro Heval
  · cases Heval with | stmts_some_sem Heval Hempty =>
      cases Hempty; exact Heval
  · exact EvalBlock.stmts_some_sem Heval EvalBlock.stmts_none_sem

theorem eval_stmts_concat
  {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  {ρ ρ' ρ'' : Env P} {cmds1 cmds2 : List (Stmt P Cmd)}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval ρ cmds1 ρ' →
  EvalBlock P Cmd EvalCmd extendEval ρ' cmds2 ρ'' →
  EvalBlock P Cmd EvalCmd extendEval ρ (cmds1 ++ cmds2) ρ'' := by
  intro Heval1 Heval2
  induction cmds1 generalizing cmds2 ρ with
  | nil =>
    simp only [List.nil_append]
    cases Heval1; exact Heval2
  | cons cmd cmds ind =>
    cases Heval1
    apply EvalBlock.stmts_some_sem (by assumption)
    apply ind (by assumption) (by assumption)

theorem EvalCmdDefMonotone [HasFvar P] [HasBool P] [HasNot P] :
  isDefined σ v →
  EvalCmd P δ σ c σ' f →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval with
  | eval_init _ hinit _ => exact InitStateDefMonotone Hdef hinit
  | eval_init_unconstrained hinit _ => exact InitStateDefMonotone Hdef hinit
  | eval_set _ hup _ => exact UpdateStateDefMonotone Hdef hup
  | eval_havoc hup _ => exact UpdateStateDefMonotone Hdef hup
  | eval_assert_pass _ _ => exact Hdef
  | eval_assert_fail _ _ => exact Hdef
  | eval_assume _ _ => exact Hdef
  | eval_cover _ => exact Hdef

theorem EvalBlockEmpty {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  { ρ ρ' : Env P }
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval ρ ([]: (List (Stmt P Cmd))) ρ' → ρ = ρ' := by
  intros H; cases H <;> simp

mutual
theorem EvalStmtDefMonotone
  {P : PureExpr}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {v : List P.Ident} {s : Stmt P (Cmd P)}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined ρ.store v →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ s ρ' →
  isDefined ρ'.store v := by
  intros Hdef Heval
  cases Heval with
  | cmd_sem Hcmd _ =>
    simp
    exact EvalCmdDefMonotone Hdef Hcmd
  | block_sem Hblock =>
    exact EvalBlockDefMonotone Hdef Hblock
  | ite_true_sem _ _ Hblock =>
    exact EvalBlockDefMonotone Hdef Hblock
  | ite_false_sem _ _ Hblock =>
    exact EvalBlockDefMonotone Hdef Hblock
  | funcDecl_sem => simp; exact Hdef
  | typeDecl_sem => exact Hdef

theorem EvalBlockDefMonotone
  {P : PureExpr}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {v : List P.Ident} {ss : List (Stmt P (Cmd P))}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined ρ.store v →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval ρ ss ρ' →
  isDefined ρ'.store v := by
  intros Hdef Heval
  cases Heval with
  | stmts_none_sem => exact Hdef
  | stmts_some_sem Hstmt Hblock =>
    exact EvalBlockDefMonotone (EvalStmtDefMonotone Hdef Hstmt) Hblock
end

end -- public section
