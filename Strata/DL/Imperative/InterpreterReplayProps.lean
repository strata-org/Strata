/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.InterpreterObs
import Strata.DL.Imperative.InterpreterObsProps

/-! # Properties of `ReplayM`, `runReplayRun` and `runReplay`

Lemmas about the definitions of `InterpreterReplay.lean`:
* `runReplay_genuine_iff`: the replay verdict is genuine iff some recorded event fires `haltOn`;
* `runReplayRun_eq` and the `replayM_run_*` lemmas: how `read`, `get`, `modify`, `pure`,
  `throw`, `>>=` and `emit` evaluate under the raw run `((x.run cfg).run).run st` of a `ReplayM`
  program (the same run as `replayRun x cfg st`);
* `replayM_ext`: `ReplayM` programs with the same runs are equal.
-/

namespace Imperative
public section
variable {P : PureExpr} {CmdT : Type}

/-! ## The replay verdict -/

/-- **Genuineness ⟺ target reached**: the verdict of `runReplay` is *genuine* iff some event
    recorded by the run satisfies the halt predicate `haltOn`. -/
theorem runReplay_genuine_iff [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (driver : ReplayM P (IConfig P CmdT)) (cfg : ReplayCfg P) (haltOn : IEvent P → Bool)
    (oracle : List P.Expr) :
    (runReplay driver cfg haltOn oracle).1 = .genuine ↔
      ∃ ev ∈ (runReplayRun driver cfg oracle).2.traceRev, haltOn ev = true := by grind [runReplay]

end
end Imperative

namespace Imperative
public section

/-! ## Raw runs of `ReplayM` programs -/

/-- Unfold `runReplayRun` into the reader, exception and state layers, seeded with the oracle. -/
theorem runReplayRun_eq {P : PureExpr} {CmdT : Type} [HasBool P] [DecidableEq P.Expr]
    [InterpLang P] (driver : ReplayM P (IConfig P CmdT)) (cfg : ReplayCfg P)
    (oracle : List P.Expr) :
    runReplayRun driver cfg oracle = ((driver.run cfg).run).run { remaining := oracle } := (rfl)

/-- With the stop hook off (`cfg.interruptOn = fun _ => none`), the raw run of `emit` records the
    event and returns `.ok`. -/
theorem replayM_run_emit_none {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P) (h : cfg.interruptOn = fun _ => none) :
    (((InterpEffects.emit (P := P) (m := ReplayM P) ev).run cfg).run).run st
      = (.ok ⟨⟩, { st with traceRev := ev :: st.traceRev }) := replayRun_emit _ _ _ h

/-- The raw run of `emit` records the event in its final state, whatever `interruptOn` says. -/
theorem replayM_run_emit_state {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P) :
    ((((InterpEffects.emit (P := P) (m := ReplayM P) ev).run cfg).run).run st).2
      = { st with traceRev := ev :: st.traceRev } := replayRun_emit_state ..

/-- The raw run of `read >>= f` runs `f` on the run's config, leaving the state untouched. -/
theorem replayM_run_read_bind {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {α : Type} (f : ReplayCfg P → ReplayM P α) (cfg : ReplayCfg P) (st : ReplayState P) :
    ((((read : ReplayM P (ReplayCfg P)) >>= f).run cfg).run).run st
      = (((f cfg).run cfg).run).run st := rfl

/-- The raw run of `get >>= f` runs `f` on the current state, leaving it unchanged. -/
theorem replayM_run_get_bind {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {α : Type} (f : ReplayState P → ReplayM P α) (cfg : ReplayCfg P) (st : ReplayState P) :
    ((((get : ReplayM P (ReplayState P)) >>= f).run cfg).run).run st
      = (((f st).run cfg).run).run st := rfl

/-- The raw run of `modify g >>= f` runs `f ()` from the updated state `g st`. -/
theorem replayM_run_modify_bind {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {α : Type} (g : ReplayState P → ReplayState P) (f : PUnit → ReplayM P α)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    ((((modify g : ReplayM P PUnit) >>= f).run cfg).run).run st
      = (((f ⟨⟩).run cfg).run).run (g st) := rfl

/-- The raw run of `pure x` succeeds with `x` and leaves the state unchanged. -/
theorem replayM_run_pure {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {α : Type} (x : α) (cfg : ReplayCfg P) (st : ReplayState P) :
    (((pure x : ReplayM P α).run cfg).run).run st = (.ok x, st) := rfl

/-- The raw run of `throw r` fails with `r` and leaves the state unchanged. -/
theorem replayM_run_throw {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {α : Type} (r : StopReason) (cfg : ReplayCfg P) (st : ReplayState P) :
    (((throw r : ReplayM P α).run cfg).run).run st = (.error r, st) := rfl

/-- The raw run of `x >>= g` runs `x`, then `g a` from the resulting state on success, and stops
    on an error with the state `x` left. -/
theorem replayM_run_bind {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {α β : Type} (x : ReplayM P α) (g : α → ReplayM P β) (cfg : ReplayCfg P)
    (st : ReplayState P) :
    (((x >>= g).run cfg).run).run st
      = (match (((x.run cfg).run).run st) with
         | (.ok a, st') => (((g a).run cfg).run).run st'
         | (.error e, st') => (.error e, st')) := replayRun_bind ..

end
end Imperative

namespace Imperative
public section
variable {P : PureExpr} {CmdT : Type}
variable [DecidableEq P.Ident]
section Replay
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]

/-! ## Extensionality -/

omit [DecidableEq P.Ident] [HasBool P] [DecidableEq P.Expr] in
/-- `ReplayM` computations with the same `replayRun` from every config and state are equal. -/
theorem replayM_ext {α : Type} {x y : ReplayM P α}
    (h : ∀ rc s, replayRun x rc s = replayRun y rc s) : x = y := funext (funext <| h ·)

end Replay
end
end Imperative
