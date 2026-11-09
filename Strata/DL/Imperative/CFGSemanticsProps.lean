/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.Cmd

public section

namespace Imperative

/-! # CFG small-step semantics: properties

Property lemmas about `StepCFGE`/`StepCFGStarE`, kept separate from any single
transform's correctness proof so they can be reused by any CFG client.

Key theorems:
  * `StepCFGE.deterministic` — one-step determinism of `StepCFGE`.
  * `StepCFGE.imp` — `StepCFGE` is monotone in its command relation.
  * `StepCFGE.preserves_factory` / `StepCFGStarE.preserves_factory` — one-step
    and traced CFG executions preserve the environment's expression factory.
  * `storeAgreement_through_projectStore'` — store agreement survives a
    block-exit projection.
  * `StepCFGE.semanticWF_evalCmdE` / `StepCFGStarE.semanticWF_evalCmdE` — CFG
    runs from well-formed stores emit semantically well-formed event snapshots. -/

/-- `StepCFGE` is deterministic: from a single source config, at most one target
    and event list are reachable in one step.  The shared source config carries
    the factory in its `Env` (`ρ.factory`), which pins each `condGoto` condition
    to one value, so `goto_true` and `goto_false` cannot both fire;
    `fetch`/`finish` are structurally functional and `step_cmd` inherits
    determinism from the command relation (`hcmd`).  This machine-checks the
    determinism the `StepCFGE` docstring relies on, guarding against a later
    constructor addition silently reintroducing nondeterminism. -/
theorem StepCFGE.deterministic
    {l CmdT : Type} {EventT : Type _} [BEq l] {P : PureExpr} {EvalCmd : EvalCmdParamE P CmdT EventT}
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P]
    {s t₁ t₂ : CFGConfig l CmdT P} {tr₁ tr₂ : List EventT}
    (hcmd : ∀ σ c σ₁ e₁ σ₂ e₂,
      EvalCmd s.getEnv.factory σ c σ₁ e₁ →
      EvalCmd s.getEnv.factory σ c σ₂ e₂ → σ₁ = σ₂ ∧ e₁ = e₂)
    (h₁ : StepCFGE P EvalCmd s tr₁ t₁)
    (h₂ : StepCFGE P EvalCmd s tr₂ t₂) :
    t₁ = t₂ ∧ tr₁ = tr₂ := by
  cases h₁ <;> cases h₂ <;> first | exact ⟨rfl, rfl⟩ | skip
  case fetch.fetch =>
    -- `List.lookup` is functional: the two fetched blocks agree.
    simp_all
  case step_cmd.step_cmd =>
    -- The command relation is deterministic (`hcmd`) under the shared factory.
    rename_i h₁ _ h₂
    obtain ⟨rfl, rfl⟩ := hcmd _ _ _ _ _ _ h₁ h₂
    exact ⟨rfl, rfl⟩
  case goto_true.goto_false =>
    -- The shared source config pins the condition, so `tt = ff` — impossible.
    exact absurd
      ((‹P.eval _ _ _ = some (HasBool.ttVal _)›).symm.trans ‹P.eval _ _ _ = some (HasBool.ffVal _)›)
      (by simp [HasBool.ttVal_ne_ffVal])
  case goto_false.goto_true =>
    exact absurd
      ((‹P.eval _ _ _ = some (HasBool.ttVal _)›).symm.trans ‹P.eval _ _ _ = some (HasBool.ffVal _)›)
      (by simp [HasBool.ttVal_ne_ffVal])

/-- Store-agreement transport through a `.block`-step projection, tolerant of
factory restoration: the outer env's factory field may be restored to any parent
factory `f` (as it is by `step_block_done`/`step_block_exit_match` in mainline),
since store agreement only depends on the store field.  Given a record-update
equality showing the outer store is the projection of the inner store, and an
agreement between the inner store and a CFG store, derive agreement between the
outer store and the CFG store. -/
theorem storeAgreement_through_projectStore' {P : PureExpr}
    {σ_parent : SemanticStore P} {ρ_inner ρ_blk : Env P}
    {σ_cfg : SemanticStore P}
    (h_ρ_blk_eq : ρ_blk = { ρ_inner with store := projectStore σ_parent ρ_inner.store })
    (h_agree_body : StoreAgreement ρ_inner.store σ_cfg) :
    StoreAgreement ρ_blk.store σ_cfg := by
  have h_store : ρ_blk.store = projectStore σ_parent ρ_inner.store := by rw [h_ρ_blk_eq]
  rw [h_store]
  exact StoreAgreement.trans (StoreAgreement.of_projectStore _ _) h_agree_body

/-! ## `StepCFGE`: monotonicity and factory preservation -/

section StepCFGE

variable {l CmdT : Type} {EventT : Type _} [BEq l] {P : PureExpr}
  {EvalCmd : EvalCmdParamE P CmdT EventT}
  [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P]
  {cfg : CFG l (DetBlock l CmdT P)}

/-- Monotonicity of `StepCFGE` in the command relation: if `EvalCmd` implies
`EvalCmd'` pointwise, every `StepCFGE` step for `EvalCmd` is a `StepCFGE` step
for `EvalCmd'`.  The control-flow rules are command-agnostic; only `step_cmd`
uses the hypothesis. -/
theorem StepCFGE.imp
    {EvalCmd' : EvalCmdParamE P CmdT EventT}
    (h_imp : ∀ fac σ c σ' emitted, EvalCmd fac σ c σ' emitted → EvalCmd' fac σ c σ' emitted)
    {c : CFGConfig l CmdT P} {tr : List EventT} {c' : CFGConfig l CmdT P}
    (h : StepCFGE P EvalCmd c tr c') :
    StepCFGE P EvalCmd' c tr c' := by
  cases h with
  | step_cmd h => exact .step_cmd (h_imp _ _ _ _ _ h)
  | fetch h => exact .fetch h
  | goto_true h => exact .goto_true h
  | goto_false h => exact .goto_false h
  | finish => exact .finish

/-- A CFG event step preserves the expression factory in its environment. -/
theorem StepCFGE.preserves_factory
    {c : CFGConfig l CmdT P} {tr : List EventT} {c' : CFGConfig l CmdT P}
    (h : StepCFGE P EvalCmd c tr c') :
    c.getEnv.factory = c'.getEnv.factory := by
  cases h <;> rfl

/-- A traced CFG execution preserves the expression factory. -/
theorem StepCFGStarE.preserves_factory
    {c : CFGConfig l CmdT P} {tr : List EventT} {c' : CFGConfig l CmdT P}
    (h : StepCFGStarE P EvalCmd c tr c') :
    c.getEnv.factory = c'.getEnv.factory := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ hstep _ ih => exact hstep.preserves_factory.trans ih

end StepCFGE

section CFGEventSnapshots

variable {l : Type} [BEq l] {P : PureExpr}
  [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]

/-- A base-command CFG step preserves store well-formedness and emits only
well-formed event snapshots. -/
theorem StepCFGE.semanticWF_evalCmdE
    {c c' : CFGConfig l (Cmd P) P} {trace : Trace P}
    (hstep : StepCFGE P (EvalCmdE P) c trace c')
    (hval : WellFormedSemanticEvalVal c.getEnv.factory)
    (hcongr : WellFormedSemanticEvalExprCongr c.getEnv.factory)
    (hstore : WellFormedStore c.getEnv.store c.getEnv.factory) :
    WellFormedStore c'.getEnv.store c'.getEnv.factory ∧ Trace.semanticWF trace := by
  cases hstep with
  | step_cmd heval =>
      refine ⟨evalCmdE_storeWellDefined hval heval hstore, ?_⟩
      rw [heval.emitted_eq]
      exact Cmd.emittedEvents_semanticWF _ _ _ hstore hcongr
  | _ => exact ⟨hstore, by simp [Trace.semanticWF]⟩

/-- A base-command CFG run from a well-formed store emits only well-formed
event snapshots. -/
theorem StepCFGStarE.semanticWF_evalCmdE
    {c c' : CFGConfig l (Cmd P) P} {trace : Trace P}
    (hrun : StepCFGStarE P (EvalCmdE P) c trace c')
    (hval : WellFormedSemanticEvalVal c.getEnv.factory)
    (hcongr : WellFormedSemanticEvalExprCongr c.getEnv.factory)
    (hstore : WellFormedStore c.getEnv.store c.getEnv.factory) :
    Trace.semanticWF trace := by
  induction hrun with
  | refl => simp [Trace.semanticWF]
  | step _ _ _ _ _ hstep _ ih =>
      have hfactory := hstep.preserves_factory
      obtain ⟨hstore', hhead⟩ := hstep.semanticWF_evalCmdE hval hcongr hstore
      exact Trace.semanticWF_append hhead
        (ih (hfactory ▸ hval) (hfactory ▸ hcongr) hstore')

end CFGEventSnapshots

end Imperative
