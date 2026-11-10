/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.DL.Imperative.InterpreterCompleteGeneric
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSoundGeneric
import all Strata.DL.Imperative.InterpreterCompleteGeneric
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps

/-! # Fuel monotonicity of an engine run, over an abstract observation

An engine run that reaches a final configuration reaches the same one at any
larger fuel.  This module proves it once over an arbitrary observation
`obs : InterpObs P m` (`obs_runInterp_fuel_mono`), so every instance of the engine
gets it.

Nothing new is assumed beyond the `InterpObs` laws: the proof inverts a successful step
(`obs_stepBaseCmdStore_fuel_mono`, `obs_stepInterp_fuel_mono`) and replays it at the larger fuel.

The language-level hypothesis is `BoundedEvalMono P` — the evaluator's own fuel
monotonicity — which suffices because fuel appears in
`stepInterp` only as the bound handed to `InterpLang.boundedEval`, and on the
configurations that do not evaluate anything the engine term does not mention fuel at
all, so the run is literally unchanged.

The conclusion keeps the *same* result state, so the recorded trace is unchanged too;
`obs_runInterp_fuel_mono_trace` states that form. -/

namespace Imperative
open scoped C1

public section

section FuelMono

variable {P : PureExpr} {m : Type → Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m]

/-! ## One base command -/

omit [HasBoolOps P] [HasFvar P] in
/-- When the language's bounded evaluator is fuel-monotone (`BoundedEvalMono`: a value found at
    some fuel is found at every larger fuel), a successful `stepBaseCmdStore` run under the
    observation `obs` reaches the same store and the same state at any larger fuel. -/
theorem obs_stepBaseCmdStore_fuel_mono (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    (fuel fuel' : Nat) (hle : fuel ≤ fuel') (f : InterpLang.RFactory P) (σ : IStore P)
    (cmd : Cmd P) (cfgr : obs.Cfg) (st st' : obs.St) (σ' : IStore P)
    (h : obs.run (stepBaseCmdStore (m := m) fuel f σ cmd) cfgr st = (.ok σ', st')) :
    obs.run (stepBaseCmdStore (m := m) fuel' f σ cmd) cfgr st = (.ok σ', st') := by
  rcases cmd with ⟨_, _, _ | _⟩ | ⟨_, _ | _⟩ <;> grind [stepBaseCmdStore, BoundedEvalMono]

/-! ## One step -/

omit [HasBoolOps P] [HasFvar P] in
/-- When the language's bounded evaluator is fuel-monotone, a successful `resolveGuard` run is
    reproduced, with the same result and state, at any larger fuel. -/
private theorem obs_resolveGuard_fuel_mono (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (env : IEnv P) (g : ExprOrNondet P) {b : Bool}
    {cfgr : obs.Cfg} {st st' : obs.St}
    (h : obs.run (resolveGuard (m := m) fuel env g) cfgr st = (.ok b, st')) :
    obs.run (resolveGuard (m := m) fuel' env g) cfgr st = (.ok b, st') := by
  cases g with
  | det c =>
    simp only [resolveGuard] at h ⊢
    split at h
    · rename_i v hv
      rw [hMono _ _ _ _ _ _ hle hv]
      exact h
    · simp [InterpObs.run_throw] at h
  | nondet => exact h

omit [HasBoolOps P] [HasFvar P] in
/-- When the language's bounded evaluator is fuel-monotone, a successful `stepInterp` step from a
    `.stmt` configuration is reproduced, with the same result and state, at any larger fuel. -/
private theorem obs_stepInterp_fuel_mono_stmt (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    (fuel fuel' : Nat) (hle : fuel ≤ fuel') (s : Stmt P (Cmd P)) (env : IEnv P)
    (cfg' : IConfig P (Cmd P)) (cfgr : obs.Cfg) (st st' : obs.St)
    (h : obs.run (stepInterp (baseStepCmd (m := m)) fuel (.stmt s env)) cfgr st
          = (.ok cfg', st')) :
    obs.run (stepInterp (baseStepCmd (m := m)) fuel' (.stmt s env)) cfgr st
      = (.ok cfg', st') := by
  rcases s with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    grind [stepInterp, baseStepCmd, obs_stepBaseCmdStore_fuel_mono, obs_resolveGuard_fuel_mono]

omit [HasBoolOps P] [HasFvar P] in
/-- When the language's bounded evaluator is fuel-monotone, a successful `stepInterp` step from a
    non-terminal, non-exiting configuration is reproduced, with the same result and state, at any
    larger fuel. -/
theorem obs_stepInterp_fuel_mono (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    (fuel fuel' : Nat) (hle : fuel ≤ fuel') :
    ∀ (cfg cfg' : IConfig P (Cmd P)) (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (stepInterp (baseStepCmd (m := m)) fuel cfg) cfgr st = (.ok cfg', st') →
      (∀ e, cfg ≠ .terminal e) → (∀ l e, cfg ≠ .exiting l e) →
      obs.run (stepInterp (baseStepCmd (m := m)) fuel' cfg) cfgr st = (.ok cfg', st') := by
  intro c
  induction c
  case seq i _ _ | block i _ => cases i <;> grind [stepInterp]
  case seqs i k _ => cases i <;> cases k <;> grind [stepInterp]
  case stmts i _ => rcases i with _ | ⟨_, _ | _⟩ <;> grind [stepInterp]
  all_goals grind [obs_stepInterp_fuel_mono_stmt]

/-! ## The whole run -/

omit [HasBoolOps P] [HasFvar P] in
/-- **Whole-run fuel monotonicity, for any monad.**  When the language's bounded evaluator is
fuel-monotone, a run of the base-command engine that reaches `final` under the observation `obs`
reaches the *same* `final` and the *same* result state at any larger fuel, under any reader
config and from any start state. -/
theorem obs_runInterp_fuel_mono (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    (cfgr : obs.Cfg) :
    ∀ (fuel k : Nat) (start final : IConfig P (Cmd P)) (st st' : obs.St),
      obs.run (runInterp (baseStepCmd (m := m)) fuel start) cfgr st = (.ok final, st') →
      obs.run (runInterp (baseStepCmd (m := m)) (fuel + k) start) cfgr st = (.ok final, st') := by
  intro n k
  have hstep := fun a => obs_stepInterp_fuel_mono obs hMono a (a + k) (by simp)
  induction n <;> intro c <;> cases c <;>
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true, obs_run_zero,
      obs_run_succ, runInterp_terminal, runInterp_exiting, Prod.mk.injEq, false_and, false_implies,
      Nat.zero_add, Nat.succ_add, Nat.succ_eq_add_one] <;>
    grind

omit [HasBoolOps P] [HasFvar P] in
/-- **Whole-run fuel monotonicity, `≤` form.**  When the language's bounded evaluator is
fuel-monotone, a run of the base-command engine that reaches `final` at `fuel` reaches the same
`final` and the same result state at every fuel `fuel' ≥ fuel`. -/
private theorem obs_runInterp_fuel_mono_le (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    (cfgr : obs.Cfg) (fuel fuel' : Nat) (hle : fuel ≤ fuel')
    (start final : IConfig P (Cmd P)) (st st' : obs.St)
    (h : obs.run (runInterp (baseStepCmd (m := m)) fuel start) cfgr st = (.ok final, st')) :
    obs.run (runInterp (baseStepCmd (m := m)) fuel' start) cfgr st = (.ok final, st') := by
  grind [obs_runInterp_fuel_mono, Nat.le.dest]

omit [HasBoolOps P] [HasFvar P] in
/-- **Whole-run fuel monotonicity, stated over the recorded trace.**  When the language's bounded
evaluator is fuel-monotone, a run of the base-command engine that succeeds at `fuel` succeeds at
every larger fuel with the same final configuration and a result state recording the same
trace. -/
theorem obs_runInterp_fuel_mono_trace (obs : InterpObs P m) (hMono : BoundedEvalMono P)
    (cfgr : obs.Cfg) (fuel fuel' : Nat) (hle : fuel ≤ fuel')
    (start final : IConfig P (Cmd P)) (st st' : obs.St)
    (h : obs.run (runInterp (baseStepCmd (m := m)) fuel start) cfgr st = (.ok final, st')) :
    ∃ st'', obs.run (runInterp (baseStepCmd (m := m)) fuel' start) cfgr st = (.ok final, st'')
      ∧ obs.trace st'' = obs.trace st' := by grind [obs_runInterp_fuel_mono_le]

end FuelMono

end -- public section

end Imperative
