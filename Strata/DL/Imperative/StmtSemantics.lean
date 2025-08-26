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
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  SemanticEval P → SemanticStore P → SemanticStore P →
  Stmt P Cmd → SemanticStore P → Prop where
  | cmd_sem :
    EvalCmd δ σ₀ σ c σ' →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    -- For example, if we require definedness on a block, then we won't be able to evaluate
    -- a block containing init x; havoc x, because it will require x to exist prior to the block
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalStmt P Cmd EvalCmd δ σ₀ σ (Stmt.cmd c) σ'

  | block_sem :
    EvalBlock P Cmd EvalCmd δ σ₀ σ b σ' →
    ----
    EvalStmt P Cmd EvalCmd δ σ₀ σ (.block _ b) σ'

  | ite_true_sem :
    δ σ₀ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd δ σ₀ σ t σ' →
    ----
    EvalStmt P Cmd EvalCmd δ σ₀ σ (.ite c t e) σ'

  | ite_false_sem :
    δ σ₀ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd δ σ₀ σ e σ' →
    ----
    EvalStmt P Cmd EvalCmd δ σ₀ σ (.ite c t e) σ'

  -- (TODO): Define semantics of `goto`.

inductive EvalStmts (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
    SemanticEval P → SemanticStore P → SemanticStore P →
    List (Stmt P Cmd) → SemanticStore P → Prop where
  | stmts_none_sem :
    EvalStmts P _ _ δ σ₀ σ [] σ
  | stmts_some_sem :
    EvalStmt P Cmd EvalCmd δ σ₀ σ s σ' →
    EvalStmts P Cmd EvalCmd δ σ₀ σ' ss σ'' →
    EvalStmts P Cmd EvalCmd δ σ₀ σ (s :: ss) σ''

inductive EvalBlock (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
    SemanticEval P → SemanticStore P → SemanticStore P →
  Block P Cmd → SemanticStore P → Prop where
  | block_sem :
    EvalStmts P Cmd EvalCmd δ σ₀ σ b.ss σ' →
    EvalBlock P Cmd EvalCmd δ σ₀ σ b σ'

end

theorem EvalCmdDefMonotone [HasFvar P] [HasBool P] [HasBoolNeg P] :
  isDefined σ v →
  EvalCmd P δ σ₀ σ c σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval <;> try exact Hdef
  next _ _ Hup => exact InitStateDefMonotone Hdef Hup
  next _ _ Hup => exact UpdateStateDefMonotone Hdef Hup
  next _ _ Hup => exact UpdateStateDefMonotone Hdef Hup

theorem EvalStmtsEmpty {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  { σ σ' σ₀: SemanticStore P } { δ : SemanticEval P }
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  EvalStmts P Cmd EvalCmd δ σ₀ σ ([]: (List (Stmt P Cmd))) σ' → σ = σ' := by
  intros H; cases H <;> simp

mutual
theorem EvalStmtDefMonotone
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P]
  :
  isDefined σ v →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ s σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases s
  case cmd c =>
    cases Heval; next Hwf Hup =>
    exact EvalCmdDefMonotone Hdef Hup
  next l b _ => cases Heval; next Hwf Hup => cases Hup; next Hup =>
    apply EvalStmtsDefMonotone (ss:=b.ss) <;> try assumption
  next c t b _ => cases Heval with
  | ite_true_sem Hsome Hwf Heval =>
    cases Heval; next Heval =>
    apply EvalStmtsDefMonotone (ss:=t.ss) <;> try assumption
  | ite_false_sem Hsome Hwf Heval =>
    cases Heval; next Heval =>
    apply EvalStmtsDefMonotone (ss:=b.ss) <;> try assumption
  case goto => cases Heval
  case loop => cases Heval
  termination_by (Stmt.sizeOf s)
  decreasing_by all_goals simp [*] at * <;> omega

theorem EvalStmtsDefMonotone
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P]
  :
  isDefined σ v →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ ss σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases ss with
  | nil =>
    have Heq := EvalStmtsEmpty Heval
    simp [← Heq]
    assumption
  | cons h t =>
    cases Heval <;> try assumption
    next σ1 Heval1 Heval2 =>
    apply EvalStmtsDefMonotone (σ:=σ1)
    apply EvalStmtDefMonotone <;> assumption
    assumption
  termination_by (Stmts.sizeOf ss)
  decreasing_by all_goals simp [*] at * <;> omega
end
