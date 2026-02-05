/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.CmdSemantics

---------------------------------------------------------------------

namespace Imperative

mutual

/--
An inductively-defined operational semantics that depends on
environment lookup and evaluation functions for expressions.

Note that `EvalStmt` is parameterized by commands `Cmd` as well as their
evaluation relation `EvalCmd`.
-/
inductive EvalStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Stmt P Cmd → SemanticStore P → Prop where
  | cmd_sem :
    EvalCmd δ σ c σ' →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    -- For example, if we require definedness on a block, then we won't be able to evaluate
    -- a block containing init x; havoc x, because it will require x to exist prior to the block
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalStmt P Cmd EvalCmd δ σ (Stmt.cmd c) σ'

  | block_sem :
    EvalBlock P Cmd EvalCmd δ σ b σ' →
    ----
    EvalStmt P Cmd EvalCmd δ σ (.block _ b) σ'

  | ite_true_sem :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd δ σ t σ' →
    ----
    EvalStmt P Cmd EvalCmd δ σ (.ite c t e) σ'

  | ite_false_sem :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd δ σ e σ' →
    ----
    EvalStmt P Cmd EvalCmd δ σ (.ite c t e) σ'

  -- (TODO): Define semantics of `goto`.

inductive EvalBlock (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
    SemanticEval P → SemanticStore P → List (Stmt P Cmd) → SemanticStore P → Prop where
  | stmts_none_sem :
    EvalBlock P _ _ δ σ [] σ
  | stmts_some_sem :
    EvalStmt P Cmd EvalCmd δ σ s σ' →
    EvalBlock P Cmd EvalCmd δ σ' ss σ'' →
    EvalBlock P Cmd EvalCmd δ σ (s :: ss) σ''

end

theorem eval_stmts_singleton
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) δ σ [cmd] σ' ↔
  EvalStmt P (Cmd P) (EvalCmd P) δ σ cmd σ' := by
  constructor <;> intro Heval
  cases Heval with | @stmts_some_sem _ _ _ σ1 _ _ Heval Hempty =>
    cases Hempty; assumption
  apply EvalBlock.stmts_some_sem Heval (EvalBlock.stmts_none_sem)

theorem eval_stmts_concat
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) δ σ cmds1 σ' →
  EvalBlock P (Cmd P) (EvalCmd P) δ σ' cmds2 σ'' →
  EvalBlock P (Cmd P) (EvalCmd P) δ σ (cmds1 ++ cmds2) σ'' := by
  intro Heval1 Heval2
  induction cmds1 generalizing cmds2 σ
  simp only [List.nil_append]
  cases Heval1
  assumption
  rename_i cmd cmds ind
  cases Heval1
  apply EvalBlock.stmts_some_sem (by assumption)
  apply ind (by assumption) (by assumption)

theorem EvalCmdDefMonotone [HasFvar P] [HasBool P] [HasNot P] :
  isDefined σ v →
  EvalCmd P δ σ c σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval <;> try exact Hdef
  next _ _ Hup => exact InitStateDefMonotone Hdef Hup
  next _ _ Hup => exact UpdateStateDefMonotone Hdef Hup
  next _ _ Hup => exact UpdateStateDefMonotone Hdef Hup

theorem EvalBlockEmpty {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  { σ σ': SemanticStore P } { δ : SemanticEval P }
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd δ σ ([]: (List (Stmt P Cmd))) σ' → σ = σ' := by
  intros H; cases H <;> simp

mutual
theorem EvalStmtDefMonotone
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined σ v →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ s σ' →
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
  | .goto _ _ => cases Heval
  | .loop _ _ _ _ _ => cases Heval
  termination_by (Stmt.sizeOf s)
  decreasing_by all_goals simp [*] at * <;> omega

theorem EvalBlockDefMonotone
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined σ v →
  EvalBlock P (Cmd P) (EvalCmd P) δ σ ss σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases ss with
  | nil =>
    have Heq := EvalBlockEmpty Heval
    simp [← Heq]
    assumption
  | cons h t =>
    cases Heval <;> try assumption
    next σ1 Heval1 Heval2 =>
    apply EvalBlockDefMonotone (σ:=σ1)
    apply EvalStmtDefMonotone <;> assumption
    assumption
  termination_by (Block.sizeOf ss)
  decreasing_by all_goals simp [*] at * <;> decreasing_tactic
end
