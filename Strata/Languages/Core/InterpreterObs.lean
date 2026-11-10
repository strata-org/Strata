/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterObs
public import Strata.Languages.Core.InterpreterSound
public import Strata.Languages.Core.InterpreterEvalProps
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterSoundGeneric
import all Strata.Languages.Core.InterpreterEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterEvalProps
import Strata.Languages.Core.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterObsProps
public import Strata.Languages.Core.InterpreterProps

/-! # Core's `EvalM` observation

Key definitions:
* `evalRun`: runs an `EvalM` computation, mapping `EvalM`'s error type `EvalHalt` to
  `StopReason` through `evalHaltReason`, which keeps engine-thrown reasons unchanged.
* `obsEval`: the `InterpObs` observation of `EvalM`.

Key theorems: the `evalRun` run lemmas `evalRun_pure`, `evalRun_throw`, `evalRun_read_bind`,
and `evalRun_emit_trace` (a successful `emit` prepends its event to the trace).

Whole-run soundness of Core's `EvalM` and `ReplayM` runs (`runInterpEval_sound`,
`runInterpReplay_sound`) and further `evalRun` lemmas are in `Core/InterpreterObsProps.lean`. -/

namespace Core

open Imperative

public section

/-- The `StopReason` an `EvalHalt` reports to the generic engine: a `stuck` halt carries its reason,
    and every other halt reports `expressionWasNotBoolean`. -/
def evalHaltReason : EvalHalt → StopReason
  | .stuck r => r
  | .assertFailed _ => .expressionWasNotBoolean
  | .assumeDidNotReduceToBool _ => .expressionWasNotBoolean
  | .nondetChoiceUnsupported => .expressionWasNotBoolean

/-- Run an `EvalM` computation under the options `opts` from the state `st`, reporting an `EvalHalt`
    error as its `evalHaltReason`. -/
def evalRun {α : Type} (x : EvalM α) (opts : EvalOpts) (st : EvalState) :
    Except StopReason α × EvalState :=
  match (((x.run opts).run).run st) with
  | (.ok a, s) => (.ok a, s)
  | (.error h, s) => (.error (evalHaltReason h), s)

/-- `evalRun` of `read >>= f` runs `f` on the run's options. -/
theorem evalRun_read_bind {α : Type} (f : EvalOpts → EvalM α) (opts : EvalOpts)
    (st : EvalState) :
    evalRun ((read : EvalM EvalOpts) >>= f) opts st = evalRun (f opts) opts st := (rfl)

/-- `evalRun` of an engine `throw r` fails with `r`, state unchanged. -/
theorem evalRun_throw {α : Type} (r : StopReason) (opts : EvalOpts) (st : EvalState) :
    evalRun (throw r : EvalM α) opts st = (.error r, st) := (rfl)

/-- `evalRun` of `pure x` succeeds with `x`, state unchanged. -/
theorem evalRun_pure {α : Type} (x : α) (opts : EvalOpts) (st : EvalState) :
    evalRun (pure x : EvalM α) opts st = (.ok x, st) := (rfl)

/-- `evalRun` of `x >>= g`: on success continue with `g` from `x`'s final state; on error
    stop with that error and state. -/
private theorem evalRun_bind {α β : Type} (x : EvalM α) (g : α → EvalM β) (opts : EvalOpts)
    (st : EvalState) :
    evalRun (x >>= g) opts st
      = (match evalRun x opts st with
         | (.ok a, st') => evalRun (g a) opts st'
         | (.error e, st') => (.error e, st')) := by
  rcases h : (x.run opts).run.run st with ⟨_ | _, _⟩ <;>
    simp_all only [evalRun, ReaderT.run_bind, ExceptT.run_bind, StateT.run_bind] <;> rfl

/-- A successful `EvalM` `emit` prepends its event to the trace. -/
theorem evalRun_emit_trace (ev : IEvent Expression) (opts : EvalOpts) (st st' : EvalState)
    (u : Unit) (h : evalRun (InterpEffects.emit (P := Expression) (m := EvalM) ev) opts st
        = (.ok u, st')) :
    st'.traceRev = ev :: st.traceRev := by
  simp only [InterpEffects.emit, evalRun_read_bind] at h
  (repeat' split at h) <;> cases h <;> rfl

/-- `EvalM`'s `choose` returns `evalDefaultChoice` if defined, else fails; the state is unchanged.
    -/
private theorem obsEval_choose (f : Lambda.Factory CoreLParams) (store : RStore Expression)
    (ty : Expression.Ty) (opts : EvalOpts) (st : EvalState) :
    evalRun (InterpEffects.choose (P := Expression) (m := EvalM) f store ty) opts st
      = (match evalDefaultChoice f ty with
         | some v => .ok v
         | none => .error (evalHaltReason .nondetChoiceUnsupported), st) := by
  simp only [InterpEffects.choose]
  split <;> simp only [*] <;> rfl

/-- A choice `EvalM` resolves passes the engine's value and type checks; the state is unchanged. -/
private theorem obsEval_choose_ok (f : Lambda.Factory CoreLParams) (store : RStore Expression)
    (ty : Expression.Ty) (opts : EvalOpts) (st : EvalState) (v : Expression.Expr)
    (st' : EvalState)
    (h : evalRun (InterpEffects.choose (P := Expression) (m := EvalM) f store ty) opts st
      = (.ok v, st')) :
    ((InterpLang.ops (P := Expression)).isValue f v = true
      ∧ (InterpLang.ops (P := Expression)).hasType f v ty = true) ∧ st' = st := by
  rw [obsEval_choose] at h
  split at h <;> simp_all [evalDefaultChoice]

/-- `EvalM` as an `InterpObs` observation: its configuration is `EvalOpts`, its state
    `EvalState`, its run projection `evalRun`, and its trace the recorded `traceRev`.
    `@[expose]`d so that `obsEval.Cfg` reduces to `EvalOpts` in statements. -/
@[expose] def obsEval : InterpObs Expression EvalM where
  Cfg := EvalOpts
  St := EvalState
  run := evalRun
  trace st := st.traceRev
  run_pure := fun x opts st => evalRun_pure x opts st
  run_throw := fun r opts st => evalRun_throw r opts st
  run_bind := by
    intro α β ma f opts st
    rw [evalRun_bind]
    rcases hx : evalRun ma opts st with ⟨r, s⟩
    cases r <;> rfl
  emit_trace := evalRun_emit_trace
  choose_sound := by
    intro factory store ty opts st v st' h
    obtain ⟨hv, rfl⟩ := obsEval_choose_ok factory store ty opts st v st' h
    exact ⟨hv, rfl⟩
  branch_stuck := fun _ _ _ opts st => evalRun_throw .expressionWasNotBoolean opts st

end -- public section

end Core
