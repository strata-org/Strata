/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.InterpreterEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterEval
import all Strata.DL.Imperative.Interpreter

/-! # Properties of Core's `EvalM` effect monad

Lemmas about the definitions of `Core/InterpreterEval.lean`.

Key theorems:
* `evalM_emit_assert`, `evalM_emit_assume`, `evalM_emit_cover`: `emit` unfolded on each event
  kind.
* `evalM_run_read_bind`, `evalM_run_pure`, `evalM_run_throwH`, `evalM_run_throw`,
  `evalM_run_modify_throwH`: `read`, `pure`, `throw` and `modify`-then-`throw` under the run
  projection.
* `EvalOpts.legacy_fuel`, `EvalOpts.legacy_assertPolicy`, `EvalOpts.legacy_assumePolicy`: the
  fields of the `EvalOpts.legacy` options. -/

namespace Core

open Imperative

public section

/-! ## `emit` and the run projection -/

/-- Running `read >>= f` under the options `opts` runs `f opts`: `read` returns the options. -/
theorem evalM_run_read_bind {α : Type} (f : EvalOpts → EvalM α) (opts : EvalOpts) :
    ((read >>= f : EvalM α).run opts) = (f opts).run opts := by
  simp only [bind, ReaderT.bind, ReaderT.run, read, readThe, MonadReaderOf.read,
    ReaderT.read]
  rfl

/-- `EvalM.emit` on an `assume`: `.ignore` records and continues; `.enforce` evaluates the
    condition and stops unless it is the true literal up to metadata. -/
theorem evalM_emit_assume (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    (InterpEffects.emit (m := EvalM) (.assume arg))
      = (do let opts ← (read : EvalM EvalOpts)
            match opts.assumePolicy with
            | .ignore =>
              modify (fun st => { st with traceRev := (REvent.assume arg) :: st.traceRev })
            | .enforce =>
              match evalBounded opts.fuel arg.factory arg.store arg.expr with
              | some v =>
                match InterpLang.boolLit? (P := Expression) v with
                | some true =>
                  modify (fun st => { st with traceRev := (REvent.assume arg) :: st.traceRev })
                | some false =>
                  throw (StopReason.assumptionFalseUnderReplay arg.label)
                | none =>
                  throwThe EvalHalt (EvalHalt.assumeDidNotReduceToBool arg.label)
              | none =>
                throwThe EvalHalt (EvalHalt.assumeDidNotReduceToBool arg.label)) := rfl

/-- `EvalM.emit` on a `cover` records the event and continues, under every policy. -/
theorem evalM_emit_cover (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    (InterpEffects.emit (m := EvalM) (.cover arg))
      = (do let _ ← (read : EvalM EvalOpts)
            modify (fun st => { st with traceRev := (REvent.cover arg) :: st.traceRev })) := rfl

/-- The run of `pure x` returns `.ok x` and leaves the state unchanged. -/
theorem evalM_run_pure {α : Type} (x : α) (opts : EvalOpts) (s : EvalState) :
    (((pure x : EvalM α).run opts).run).run s = (.ok x, s) := by
  simp only [pure, ReaderT.pure, ReaderT.run, ExceptT.pure, ExceptT.mk, ExceptT.run,
    StateT.pure, StateT.run]

/-- The run of a throw of an `EvalHalt` `h` returns `.error h` and leaves the state unchanged. -/
theorem evalM_run_throwH {α : Type} (h : EvalHalt) (opts : EvalOpts) (s : EvalState) :
    (((throwThe EvalHalt h : EvalM α).run opts).run).run s = (.error h, s) := by
  simp only [throwThe, MonadExceptOf.throw, ReaderT.run, ExceptT.run, StateT.run]
  rfl

/-- The run of a throw of a `StopReason` `r` returns the `EvalHalt.stuck r` error and leaves the
    state unchanged. -/
theorem evalM_run_throw {α : Type} (r : StopReason) (opts : EvalOpts) (s : EvalState) :
    (((throw r : EvalM α).run opts).run).run s = (.error (.stuck r), s) := by
  simp only [throw, throwThe, MonadExceptOf.throw, ReaderT.run, ExceptT.run, StateT.run,
    ExceptT.mk, pure]
  rfl

/-- The run of `modify`-then-`throw` of an `EvalHalt`: the modified state persists and the
    outcome is `.error`. -/
theorem evalM_run_modify_throwH {α : Type} (g : EvalState → EvalState) (h : EvalHalt)
    (opts : EvalOpts) (s : EvalState) :
    ((((modify g : EvalM PUnit) >>= fun _ => (throwThe EvalHalt h : EvalM α)).run opts).run).run s
      = (.error h, g s) := by
  simp only [bind, ReaderT.bind, ReaderT.run, modify, modifyGet, MonadStateOf.modifyGet,
    throwThe, MonadExceptOf.throw, ExceptT.run, StateT.run]
  rfl

/-- `EvalM.emit` on an `assert`: evaluate the condition; false records and halts or collects,
    true records, anything else is stuck. -/
theorem evalM_emit_assert (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    (InterpEffects.emit (m := EvalM) (.assert arg))
      = (do let opts ← (read : EvalM EvalOpts)
            match evalBounded opts.fuel arg.factory arg.store arg.expr with
            | some v =>
              match InterpLang.boolLit? (P := Expression) v with
              | some false =>
                match opts.assertPolicy with
                | .halt => do
                  modify (fun st => { st with traceRev := REvent.assert arg :: st.traceRev })
                  throwThe EvalHalt (EvalHalt.assertFailed arg)
                | .collect =>
                  modify (fun st =>
                      { st with
                        traceRev := REvent.assert arg :: st.traceRev,
                        assertFailures := (arg.label, v, arg.metadata) :: st.assertFailures })
              | some true =>
                modify (fun st => { st with traceRev := REvent.assert arg :: st.traceRev })
              | none => throw StopReason.expressionWasNotBoolean
            | none => throw StopReason.expressionDidNotEvaluate) := rfl

/-! ## The `EvalOpts.legacy` options -/

/-- `EvalOpts.legacy n` has fuel `n`. -/
@[simp] theorem EvalOpts.legacy_fuel (n : Nat) : (EvalOpts.legacy n).fuel = n := rfl

/-- `EvalOpts.legacy` halts on a false assertion. -/
@[simp] theorem EvalOpts.legacy_assertPolicy (n : Nat) :
    (EvalOpts.legacy n).assertPolicy = .halt := rfl

/-- `EvalOpts.legacy` ignores assumes. -/
@[simp] theorem EvalOpts.legacy_assumePolicy (n : Nat) :
    (EvalOpts.legacy n).assumePolicy = .ignore := rfl

end
end Core
