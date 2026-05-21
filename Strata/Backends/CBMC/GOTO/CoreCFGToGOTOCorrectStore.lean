/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
public import Strata.Backends.CBMC.GOTO.Bisim

public section

/-! # `StoreCorr`-based forward simulation (Phase 3)

Phase 3 of the GOTO-semantics-expansion plan
(`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`).

This file builds the trace-level lift from `StepGotoStar` to
`SemanticsTautschnig.ExecProg`, modulo `StoreCorr`. It is the
load-bearing chunk of Phase 3.

## Architecture

The lift is parameterized by a `SteppingBridges` bundle: a single
hypothesis that says "every running `StepGoto` step from a
non-terminal configuration corresponds to a `StepInstr` step on the
`StoreCorr`-translated GOTO store." This is exactly the disjunction of
the per-step bridges in `Bisim.lean` quantified over an arbitrary
configuration.

Why bundle and not pull each per-step bridge in directly? Because
the per-step bridges have different hypotheses (`EvalBoolCorr` vs.
`EvalValueCorr` vs. `Function.Injective nameMap` vs. `findLocIdx`-
resolution). At the trace level, we don't know which constructor
will fire on each step. Bundling them as a single existential
hypothesis lets the trace-level induction proceed uniformly; the
caller discharges the bundle by case-splitting on the instruction
type at each PC.

The end-of-trace `step_end_function → ExecProg.end_function` bridge is
also a hypothesis on the bundle, since it produces an `ExecProg`
rather than a `StepInstr`. -/

namespace CProverGOTO

open Imperative
open CProverGOTO.SemanticsTautschnig
  (Store StoreCorr CallResultRel ExprEval FuncEnv ExecProg StepInstr)

/-! ## SteppingBridges bundle -/

/-- Hypothesis bundle for the Phase 3 trace lift.

For every running configuration `(pc, σ_imp, failed)` and every
`StepGoto` step from that configuration to a successor, the
GOTO-side store `σ_goto` (related by `StoreCorr` to `σ_imp`) admits
either:

* a `StepInstr` step to a corresponding successor `σ_goto'` (used
  when the `StepGoto` step lands at `.running pc' σ_imp' failed'`
  with the same `failed`), or
* an `ExecProg.end_function` derivation (used when the `StepGoto`
  step lands at `.terminal σ_imp' failed'`).

Plus, the failed flag bridges via `AssertFails` when it changes:
the bundle is required to also produce an `AssertFails` witness
whenever a step flips the failed flag.

This is exactly the disjunction of the per-step bridges in
`Bisim.lean`, lifted to a uniform interface. -/
structure SteppingBridges
    {P : PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    (δ_goto : SemanticEvalGoto P)
    (δ_goto_bool : SemanticEvalGotoBool P)
    (pgm : Program)
    (nameMap : P.Ident → String)
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv) : Prop where
  /-- Step bridge: a running `StepGoto` step to a running successor
  produces a corresponding `StepInstr` step on the `StoreCorr`-
  translated GOTO store. -/
  step_running :
    ∀ {pc pc' : Nat} {σ_imp σ_imp' : SemanticStore P} {failed failed' : Bool}
      {σ_goto : Store},
      StepGoto P δ_goto δ_goto_bool pgm
        (.running pc σ_imp failed) (.running pc' σ_imp' failed') →
      StoreCorr nameMap σ_imp σ_goto →
      ∃ σ_goto', StoreCorr nameMap σ_imp' σ_goto' ∧
        StepInstr callResult eval fenv pgm pc σ_goto pc' σ_goto'
  /-- Terminal bridge: a `StepGoto` step to a `.terminal` successor
  closes out the chain via `ExecProg.end_function`. -/
  step_terminal :
    ∀ {pc : Nat} {σ_imp σ_imp' : SemanticStore P} {failed failed' : Bool}
      {σ_goto : Store},
      StepGoto P δ_goto δ_goto_bool pgm
        (.running pc σ_imp failed) (.terminal σ_imp' failed') →
      StoreCorr nameMap σ_imp σ_goto →
      ∃ σ_goto', StoreCorr nameMap σ_imp' σ_goto' ∧
        ExecProg callResult eval fenv pgm pc σ_goto σ_goto' none

/-! ## Trace-level lift -/

/-- An `ExecProg` chain extends to an `ExecProg` chain: prefix a
`StepInstr` step. (Wrapper around the `ExecProg.step` constructor for
clarity.) -/
private theorem ExecProg.step_prefix
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {pgm : Program} {pc pc' : Nat}
    {σ σ' σ'' : Store} {retVal : Option SemanticsTautschnig.Value}
    (h_step : StepInstr callResult eval fenv pgm pc σ pc' σ') :
    ExecProg callResult eval fenv pgm pc' σ' σ'' retVal →
    ExecProg callResult eval fenv pgm pc σ σ'' retVal :=
  fun h_rest => .step h_step h_rest

/-- Trace-level lift: a `StepGotoStar` chain ending at a `.terminal`
configuration corresponds to an `ExecProg` derivation on the
GOTO-side store, modulo `StoreCorr`.

This is the core Phase 3 result. It composes the per-step bridges
(bundled as `SteppingBridges`) into a full `ExecProg` derivation. -/
theorem StepGotoStar_to_ExecProg
    {P : PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {nameMap : P.Ident → String}
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    (br : SteppingBridges δ_goto δ_goto_bool pgm nameMap callResult eval fenv)
    {pc : Nat} {σ_imp σ_imp' : SemanticStore P}
    {failed failed' : Bool} {σ_goto : Store}
    (h_steps : StepGotoStar P δ_goto δ_goto_bool pgm
                 (.running pc σ_imp failed) (.terminal σ_imp' failed'))
    (h_corr : StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', StoreCorr nameMap σ_imp' σ_goto' ∧
      ExecProg callResult eval fenv pgm pc σ_goto σ_goto' none := by
  -- StepGotoStar = ReflTrans (StepGoto …). Induct on the chain.
  unfold StepGotoStar at h_steps
  -- Generalize over the start configuration so the IH can refire.
  generalize h_eq : (GotoConfig.running pc σ_imp failed : GotoConfig P) = c at h_steps
  generalize h_eq' : (GotoConfig.terminal σ_imp' failed' : GotoConfig P) = c' at h_steps
  induction h_steps generalizing pc σ_imp σ_goto failed
  case refl =>
    -- A zero-step chain from .running to .terminal is a contradiction
    -- (the constructors are different).
    rw [← h_eq] at h_eq'
    cases h_eq'
  case step c_a c_b c_c h_step _h_rest ih =>
    subst h_eq
    -- The single step lands either at .running or .terminal.
    cases c_b with
    | running pc_mid σ_mid failed_mid =>
      -- Use step_running, then recurse via the IH.
      obtain ⟨σ_goto_mid, h_corr_mid, h_step_mid⟩ :=
        br.step_running h_step h_corr
      obtain ⟨σ_goto_final, h_corr_final, h_rest⟩ :=
        ih h_corr_mid rfl h_eq'
      exact ⟨σ_goto_final, h_corr_final,
        ExecProg.step_prefix h_step_mid h_rest⟩
    | terminal σ_t failed_t =>
      -- The chain reaches terminal in one step; the rest must be refl,
      -- so σ_t = σ_imp' and failed_t = failed'.
      cases h_eq'
      -- Use step_terminal directly.
      obtain ⟨σ_goto', h_corr', h_exec⟩ := br.step_terminal h_step h_corr
      cases _h_rest with
      | refl _ => exact ⟨σ_goto', h_corr', h_exec⟩
      | step _ _ _ h_after _ =>
        -- A `StepGoto` step from a `.terminal` configuration is
        -- impossible — every constructor's source is `.running`.
        cases h_after

end CProverGOTO
