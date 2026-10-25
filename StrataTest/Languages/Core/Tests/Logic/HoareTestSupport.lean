/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core
public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.DL.Imperative.StmtSemanticsProps

/-! # Core Hoare test run inversion support

Key results:
- `someValuation` supplies a valuation for any Core model;
- `singleton_run_inv` extracts a statement run from a singleton statement-list run;
- `assume_run_inv` characterizes an `assume` run;
- `assert_run_inv` characterizes an `assert` run.
-/

public section

namespace CoreHoareTestSupport

open Imperative

/-- An arbitrary valuation for a model over `Core.Factory`. -/
def someValuation (model : Lambda.Interp Core.Factory) :
    Core.Logic.DenoteValuation model where
  tyVarVal := fun _ => .tcons "bool" []
  freeVarVal := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  offFactoryHolds := fun _ => False

variable (π : String → Option Core.Procedure)

/-- A completed singleton statement-list run yields the corresponding statement run. -/
theorem singleton_run_inv {s : Core.Statement}
    {ρ ρ' : Imperative.Env Core.Expression}
    {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [s] ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [s] ρ) tr (.exiting lbl ρ')) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt s ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt s ρ) tr (.exiting lbl ρ') := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · rcases stmts_cons_headE (Core.EvalCommandE π) hterm with ⟨hcfg, _⟩ | hseq
    · simp at hcfg
    · obtain ⟨ρ₁, tr₁, tr₂, htr, hhead, htail⟩ :=
        seq_reaches_terminalE (Core.EvalCommandE π) hseq
      obtain ⟨htr₂, hcfg⟩ := stmts_nil_runE (Core.EvalCommandE π) htail
      subst htr₂
      rcases hcfg with hcfg | hcfg
      · simp at hcfg
      · injection hcfg with hρ; subst hρ
        rw [htr, List.append_nil]; exact .inl hhead
  · rcases stmts_cons_headE (Core.EvalCommandE π) hexit with ⟨hcfg, _⟩ | hseq
    · simp at hcfg
    · rcases seq_reaches_exitingE (Core.EvalCommandE π) hseq with
        hhead | ⟨ρ₁, tr₁, tr₂, _, _, htail⟩
      · exact .inr ⟨lbl, hhead⟩
      · obtain ⟨_, hcfg⟩ := stmts_nil_runE (Core.EvalCommandE π) htail
        rcases hcfg with hcfg | hcfg <;> simp at hcfg

/-- An `assume` statement emits its captured condition and preserves its environment. -/
theorem assume_run_inv {l : String} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assume l e md) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assume l e md) ρ) tr (.exiting lbl ρ')) :
    tr = [Event.assume ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assume =>
          obtain ⟨hcfg, hnil⟩ := stepStmtStarE_from_terminal hrest
          subst hnil
          injection hcfg with hρ
          subst hρ
          exact ⟨by simp, rfl⟩
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim
  · cases hexit with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assume =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim

/-- An `assert` statement emits its captured condition and preserves its environment. -/
theorem assert_run_inv {l : String} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assert l e md) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assert l e md) ρ) tr (.exiting lbl ρ')) :
    tr = [Event.assert ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assert =>
          obtain ⟨hcfg, hnil⟩ := stepStmtStarE_from_terminal hrest
          subst hnil
          injection hcfg with hρ
          subst hρ
          exact ⟨by simp, rfl⟩
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim
  · cases hexit with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assert =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim

end CoreHoareTestSupport

end -- public section
