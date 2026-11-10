/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterSoundGeneric
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
import Strata.DL.Imperative.InterpreterReplayTactics

/-! # `obsReplay`, the `ReplayM` observation

* `replayRun`: runs a `ReplayM` program from a config and a state; its run lemmas
  (`replayRun_pure`, `replayRun_bind`, `replayRun_emit_state`, `replayRun_choose`, ...).
* `interruptOff`, `RunBridge`: a run with the stop hook against the same run without it.
* `obsReplay`: `ReplayM` as an `InterpObs` instance.

Further run lemmas, the `RunBridge` lemmas and whole-run replay soundness
(`runInterp_sound_replay`) are in `InterpreterObsProps.lean`. -/

namespace Imperative

public section

-- The `ReplayM` run lemmas below are stated over the language's instances for uniformity.

section Observations
variable {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]

/-! ## `ReplayM` run lemmas under `replayRun` -/

/-- Run a `ReplayM` computation under the configuration `cfg` from the state `st`, returning its
    outcome and final state. -/
@[expose] def replayRun {α : Type} (x : ReplayM P α) (cfg : ReplayCfg P) (st : ReplayState P) :
    Except StopReason α × ReplayState P := ((x.run cfg).run).run st

omit [HasBool P] [DecidableEq P.Expr] in
/-- `replayRun` of `read >>= f` runs `f` on the run's config. -/
theorem replayRun_read_bind {α : Type} (f : ReplayCfg P → ReplayM P α)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    replayRun ((read : ReplayM P (ReplayCfg P)) >>= f) cfg st = replayRun (f cfg) cfg st := rfl

omit [HasBool P] [DecidableEq P.Expr] in
/-- `replayRun` of `get >>= f` runs `f` on the current state. -/
theorem replayRun_get_bind {α : Type} (f : ReplayState P → ReplayM P α)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    replayRun ((get : ReplayM P (ReplayState P)) >>= f) cfg st = replayRun (f st) cfg st := rfl

omit [HasBool P] [DecidableEq P.Expr] in
/-- `replayRun` of `modify g >>= f` runs `f` from the updated state `g st`. -/
theorem replayRun_modify_bind {α : Type} (g : ReplayState P → ReplayState P)
    (f : PUnit → ReplayM P α) (cfg : ReplayCfg P) (st : ReplayState P) :
    replayRun ((modify g : ReplayM P PUnit) >>= f) cfg st = replayRun (f ⟨⟩) cfg (g st) := rfl

omit [HasBool P] [DecidableEq P.Expr] in
/-- `replayRun` of `pure x` succeeds with `x` and leaves the state unchanged. -/
theorem replayRun_pure {α : Type} (x : α) (cfg : ReplayCfg P) (st : ReplayState P) :
    replayRun (pure x : ReplayM P α) cfg st = (.ok x, st) := rfl

omit [HasBool P] [DecidableEq P.Expr] in
/-- `replayRun` of `throw r` fails with `r` and leaves the state unchanged. -/
theorem replayRun_throw {α : Type} (r : StopReason) (cfg : ReplayCfg P)
    (st : ReplayState P) : replayRun (throw r : ReplayM P α) cfg st = (.error r, st) := rfl

omit [HasBool P] [DecidableEq P.Expr] in
/-- `replayRun` of `x >>= g`: continue with `g` on success, stop with the error otherwise. -/
theorem replayRun_bind {α β : Type} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    replayRun (x >>= g) cfg st
      = (match replayRun x cfg st with
         | (.ok a, st') => replayRun (g a) cfg st'
         | (.error e, st') => (.error e, st')) := by
  simp only [replayRun, ReaderT.run_bind, ExceptT.run_bind, StateT.run_bind]
  split <;> simp only [*] <;> rfl

/-- `emit` records the event in every outcome, whatever `interruptOn` says. -/
theorem replayRun_emit_state (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P) :
    (replayRun (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st).2
      = { st with traceRev := ev :: st.traceRev } := by
  simp only [InterpEffects.emit, replayRun_modify_bind, replayRun_read_bind]
  split <;> rfl

/-- Whatever the stop hook `interruptOn` says, a successful `emit` has recorded the event. -/
private theorem replayRun_emit_ok (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P)
    (u : PUnit) (st' : ReplayState P)
    (h : replayRun (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st = (.ok u, st')) :
    st' = { st with traceRev := ev :: st.traceRev } := (h ▸ replayRun_emit_state .. :)

/-- A successful `choose` in `ReplayM` passed the value checks and left the trace unchanged. -/
theorem replayRun_choose (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) (v : P.Expr) (st' : ReplayState P)
    (h : replayRun (InterpEffects.choose (P := P) factory store ty) cfg st = (.ok v, st')) :
    ((InterpLang.ops (P := P)).isValue factory v = true
      ∧ (InterpLang.ops (P := P)).hasType factory v ty = true)
    ∧ st'.traceRev = st.traceRev := by eff_inv [] <;> grind

/-! ## `RunBridge`: the interrupt-on run against the interrupt-off run -/

/-- `cfg` with the stop hook disabled (`interruptOn := fun _ => none`), so `emit` is record-only. -/
@[expose] def interruptOff (cfg : ReplayCfg P) : ReplayCfg P :=
  { cfg with interruptOn := fun _ => none }

/-- Relates the run of `x` under `cfg` to its run with the stop hook disabled
    (`interruptOff cfg`): the trace recorded under `cfg` is a suffix of the trace recorded
    with the hook off, and a run under `cfg` that succeeds coincides with the hook-off run. -/
@[reducible, expose] def RunBridge {α : Type} (x : ReplayM P α) (cfg : ReplayCfg P)
    (st : ReplayState P) : Prop :=
  (replayRun x cfg st).2.traceRev <:+ (replayRun x (interruptOff cfg) st).2.traceRev
  ∧ (∀ a, (replayRun x cfg st).1 = .ok a →
      replayRun x cfg st = replayRun x (interruptOff cfg) st)

/-- The replay observation: `ReplayM`'s reader config, state, run projection and recorded trace.
    `@[expose]`d so its fields unfold in statements outside this module. -/
@[expose] def obsReplay : InterpObs P (ReplayM P) where
  Cfg := ReplayCfg P
  St := ReplayState P
  run := replayRun
  trace st := st.traceRev
  run_pure := fun x cfg st => replayRun_pure x cfg st
  run_throw := fun r cfg st => replayRun_throw r cfg st
  run_bind := by
    intro α β ma f cfg st
    rw [replayRun_bind]
    rcases hx : replayRun ma cfg st with ⟨r, s⟩
    cases r <;> rfl
  emit_trace := by
    intro ev cfg st st' u h
    rw [replayRun_emit_ok ev cfg st u st' h]
  choose_sound := fun f store ty cfg st v st' h => replayRun_choose f store ty cfg st v st' h
  branch_stuck := fun _ _ _ cfg st => replayRun_throw .expressionWasNotBoolean cfg st

end Observations

end -- public section

end Imperative
