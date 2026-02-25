/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.Stmt
import Strata.Util.Tactics

---------------------------------------------------------------------

namespace Imperative

/-- Type of a function that extends the semantic evaluator with a new function definition. -/
abbrev ExtendEval (P : PureExpr) := SemanticEval P → SemanticStore P → PureFunc P → SemanticEval P

/-- Exit status after evaluating a statement or block.
- `normal`: execution continues normally
- `exiting label`: an `exit label` was encountered and is propagating upward -/
inductive ExitStatus where
  | normal : ExitStatus
  | exiting : Option String → ExitStatus
  deriving Repr, BEq, Inhabited

/-- Does the exit status match a block label? An `exit` with no label matches
any block. An `exit l` matches a block labeled `l`. -/
def ExitStatus.consumedBy : ExitStatus → String → ExitStatus
  | .normal, _ => .normal
  | .exiting .none, _ => .normal
  | .exiting (.some l), blockLabel => if l == blockLabel then .normal else .exiting (.some l)

mutual

/-
Intended properties of exit semantics:
1. `exit` with no label exits the nearest enclosing block
2. `exit l` exits the nearest enclosing block labeled `l`
3. When an exit is active, remaining statements in a block are skipped
4. A block consumes the exit if the label matches (or exit has no label)
5. Exit does not modify the store or evaluator
6. Non-exit statements produce `normal` exit status
-/

/--
An inductively-defined operational semantics that depends on
environment lookup and evaluation functions for expressions.

Note that `EvalStmt` is parameterized by commands `Cmd` as well as their
evaluation relation `EvalCmd`, and by `extendEval` which specifies how
`funcDecl` statements extend the evaluator.

The expression evaluator `δ` is threaded as state to support `funcDecl`,
which extends the evaluator with new function definitions. Commands do not
modify the evaluator, only `funcDecl` statements do.

Each evaluation also produces an `ExitStatus`:
- `normal` means execution completed normally
- `exiting label` means an exit statement was encountered

The exit status propagates through blocks: when a statement produces
`exiting`, the remaining statements in the block are skipped.
-/
inductive EvalStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Stmt P Cmd → SemanticStore P → SemanticEval P → ExitStatus → Prop where
  | cmd_sem :
    EvalCmd δ σ c σ' →
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (Stmt.cmd c) σ' δ .normal

  | block_sem :
    EvalBlock P Cmd EvalCmd extendEval δ σ b σ' δ' e →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block label b) σ' δ' (e.consumedBy label)

  | ite_true_sem :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ t σ' δ' exit →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c t e) σ' δ' exit

  | ite_false_sem :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ e σ' δ' exit →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c t e) σ' δ' exit

  | exit_sem :
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.exit label) σ δ (.exiting label)

  | funcDecl_sem [HasSubstFvar P] [HasVarsPure P P.Expr] :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.funcDecl decl md) σ
      (extendEval δ σ decl) .normal

/-- Block evaluation with exit propagation.
When a statement produces an exit, remaining statements are skipped. -/
inductive EvalBlock (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
    SemanticEval P → SemanticStore P → List (Stmt P Cmd) → SemanticStore P → SemanticEval P → ExitStatus → Prop where
  | stmts_none_sem :
    EvalBlock P _ _ _ δ σ [] σ δ .normal
  | stmts_some_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ s σ' δ' .normal →
    EvalBlock P Cmd EvalCmd extendEval δ' σ' ss σ'' δ'' e →
    EvalBlock P Cmd EvalCmd extendEval δ σ (s :: ss) σ'' δ'' e
  | stmts_exit_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ s σ' δ' (.exiting label) →
    ----
    EvalBlock P Cmd EvalCmd extendEval δ σ (s :: ss) σ' δ' (.exiting label)

end

theorem eval_stmts_singleton
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ [cmd] σ' δ' exit ↔
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ cmd σ' δ' exit := by
  constructor <;> intro Heval
  · cases Heval with
    | stmts_some_sem Heval Hempty => cases Hempty; exact Heval
    | stmts_exit_sem Heval => exact Heval
  · match exit with
    | .normal => exact EvalBlock.stmts_some_sem Heval EvalBlock.stmts_none_sem
    | .exiting l => exact EvalBlock.stmts_exit_sem Heval

theorem eval_stmts_concat
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ cmds1 σ' δ' .normal →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ' σ' cmds2 σ'' δ'' exit →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ (cmds1 ++ cmds2) σ'' δ'' exit := by
  intro Heval1 Heval2
  induction cmds1 generalizing cmds2 σ δ
  · simp only [List.nil_append]
    cases Heval1; exact Heval2
  · rename_i cmd cmds ind
    cases Heval1 with
    | stmts_some_sem Heval1 Hrest =>
      apply EvalBlock.stmts_some_sem (by assumption)
      apply ind (by assumption) (by assumption)

theorem EvalCmdDefMonotone [HasFvar P] [HasBool P] [HasNot P] :
  isDefined σ v →
  EvalCmd P δ σ c σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval <;> try exact Hdef
  next _ Hup => exact InitStateDefMonotone Hdef Hup  -- eval_init
  next Hup => exact InitStateDefMonotone Hdef Hup    -- eval_init_unconstrained
  next _ Hup => exact UpdateStateDefMonotone Hdef Hup
  next Hup => exact UpdateStateDefMonotone Hdef Hup

theorem EvalBlockEmpty {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  { σ σ': SemanticStore P } { δ δ' : SemanticEval P }
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval δ σ ([]: (List (Stmt P Cmd))) σ' δ' exit → σ = σ' ∧ δ = δ' ∧ exit = .normal := by
  intros H; cases H <;> simp

mutual
theorem EvalStmtDefMonotone
  [DecidableEq P.Ident]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined σ v →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' δ' exit →
  isDefined σ' v := by
  intros Hdef Heval
  match s with
  | .cmd c =>
    cases Heval; next Hwf Hup =>
    exact EvalCmdDefMonotone Hdef Hup
  | .block l bss  _ =>
    cases Heval; next Hwf Hup =>
    apply EvalBlockDefMonotone <;> assumption
  | .ite c tss bss _ => cases Heval with
    | ite_true_sem Hsome Hwf Heval =>
      apply EvalBlockDefMonotone <;> assumption
    | ite_false_sem Hsome Hwf Heval =>
      apply EvalBlockDefMonotone <;> assumption
  | .exit _ _ => cases Heval; assumption
  | .loop _ _ _ _ _ => cases Heval
  | .funcDecl _ _ => cases Heval; assumption

theorem EvalBlockDefMonotone
  [DecidableEq P.Ident]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined σ v →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ' exit →
  isDefined σ' v := by
  intros Hdef Heval
  cases ss with
  | nil =>
    have Heq := EvalBlockEmpty Heval
    simp [← Heq.1]
    assumption
  | cons h t =>
    cases Heval with
    | stmts_some_sem Heval1 Heval2 =>
      apply EvalBlockDefMonotone (σ:=_) (δ:=_)
      apply EvalStmtDefMonotone <;> assumption
      assumption
    | stmts_exit_sem Heval1 =>
      apply EvalStmtDefMonotone <;> assumption
end

end Imperative
