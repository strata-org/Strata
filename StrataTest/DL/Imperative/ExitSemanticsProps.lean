/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.StmtSemantics

/-! ## Properties of exit semantics

These theorems verify key properties of the exit semantics:
- Variable definedness is preserved through exit (store monotonicity)
- Block concatenation works when the first block exits normally
-/

namespace Imperative

mutual
/-- Exit preserves variable definedness through statements. -/
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

/-- Exit preserves variable definedness through blocks. -/
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

/-- Block concatenation: if the first block exits normally, the combined
block evaluates to the result of evaluating the second block after the first. -/
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

end Imperative
