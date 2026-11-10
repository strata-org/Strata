/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterKleene
public import Strata.DL.Imperative.InterpreterKleeneSound
public import Strata.DL.Imperative.InterpreterKleeneComplete
public import Strata.DL.Imperative.InterpreterCFGKleeneFollows
public import Strata.Languages.Core.InterpreterCallComplete
import all Strata.Languages.Core.InterpreterKleene
import all Strata.Languages.Core.InterpreterCallSound
import Strata.Languages.Core.InterpreterProps
public import Strata.Languages.Core.InterpreterEvalSound

/-! # Soundness and completeness of the Core call-aware monadic Kleene interpreter

Key theorems:
* `runCoreInterpKleene_replay_soundE`: a successful replay run of `runCoreInterpKleene`
  from a tracked start records exactly the events of a `StepKleeneExtStarE` derivation
  between the abstractions (`IKleeneConfig.abs`) of its start and final configurations;
  it is the generic `Imperative.Calls.runCallInterpKleene_replay_soundE` at Core, with the
  language typeclasses and the bounded-evaluator soundness discharged;
* `runCoreInterpKleene_completeE`: every engine-realizable Kleene derivation reaching a
  terminal config is reproduced by a `runCoreInterpKleene` run at every sufficiently large
  fuel;
* `runCoreInterpKleene_complete_follows`, `runCoreInterpKleene_replayComplete`: every Kleene run
  that reads its nondeterministic choices off an oracle and reaches a terminal config is
  reproduced by a `runCoreInterpKleene` run at every sufficiently large fuel, along the oracle,
  monad-generically and under `ReplayM`. -/

namespace Core

open Imperative Imperative.Calls

public section

/-- **Core call-aware Kleene soundness over the replay monad.**  Let a replay run of
    `runCoreInterpKleene π` with oracle `oracle` succeed from the interpreter configuration
    `start` to `final`, where `start` is `Tracked` (every scope frame records exactly the
    names defined at its level) and denotes at the factory `F` (`IKleeneConfig.Denoting`).
    Assume every procedure of `π` passes the local well-formedness check `ProcsOk`, `F` is
    well-formed (`FactoryWF`), the semantic image `start.abs F` satisfies the Kleene invariant
    `KCfgOk` (a well-formed, typed store on the active environment, and well-formed call sites
    in every command still to run), and the bounded evaluator is sound at `F`
    (`BoundedEvalSoundAt`).  Then the run's recorded runtime trace is a
    trace whose semantic image is the event list of a derivation of the call-aware Kleene
    reference semantics `Imperative.StepKleeneExtStarE` from `start.abs F` to `final.abs F`. -/
theorem runCoreInterpKleene_replay_soundE
    (π : String → Option Procedure)
    (fuel d : Nat) (start final : IKleeneConfig Expression Command)
    (cfg : ReplayCfg Expression) (oracle : List Expression.Expr) (st' : ReplayState Expression)
    (hprocs : Imperative.Calls.ProcsOk π)
    (hrun : replayRun (runCoreInterpKleene (m := ReplayM Expression) π fuel start d) cfg
      { remaining := oracle } = (.ok final, st'))
    (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : start.Denoting F)
    (hinv : KCfgOk (Imperative.Calls.CallEnvOk (P := Expression))
      (fun c => Imperative.Calls.CmdCallOk π c = true) (start.abs F))
    (htr : start.Tracked) :
    ∃ revs : List (IEvent Expression),
      Imperative.StepKleeneExtStarE π (start.abs F) (revs.map (REvent.abs F)) (final.abs F)
      ∧ st'.traceRev = revs.reverse :=
  runCallInterpKleene_replay_soundE _ hprocs _ _ _ _ _ _ _ hrun F hEval hfac hd hinv htr

/-- **Core call-aware Kleene soundness over the replay monad.** Let a replay run of
    `runCoreInterpKleene π` with oracle `oracle` succeed from the interpreter configuration `start`
    to `final`, where `start` is `Tracked` (every scope frame records exactly the names defined at
    its level) and denotes at the factory `F` (`IKleeneConfig.Denoting`). Assume every procedure of
    `π` passes the local well-formedness check `ProcsOk`, `F` is well-formed (`FactoryWF`), the
    semantic image `start.abs F` satisfies the Kleene invariant `KCfgOk` (a well-formed, typed store
    on the active environment, and well-formed call sites in every command still to run), and the
    functions of `F` meet the conditions under which the bounded evaluator is sound
    (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives program factories). Then the run's
    recorded runtime trace is a trace whose semantic image is the event list of a derivation of the
    call-aware Kleene reference semantics `Imperative.StepKleeneExtStarE` from `start.abs F` to
    `final.abs F`. -/
theorem runCoreInterpKleene_replay_soundE_of_evalFactoryWF
    (π : String → Option Procedure)
    (fuel d : Nat)
    (start final : IKleeneConfig Expression Command)
    (cfg : ReplayCfg Expression)
    (oracle : List Expression.Expr)
    (st' : ReplayState Expression)
    (hprocs : Imperative.Calls.ProcsOk π)
    (hrun : replayRun (runCoreInterpKleene (m := ReplayM Expression) π fuel start d) cfg
      { remaining := oracle } = (.ok final, st'))
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : start.Denoting F)
    (hinv : KCfgOk (Imperative.Calls.CallEnvOk (P := Expression))
      (fun c => Imperative.Calls.CmdCallOk π c = true) (start.abs F))
    (htr : start.Tracked) :
    ∃ revs : List (IEvent Expression),
      Imperative.StepKleeneExtStarE π (start.abs F) (revs.map (REvent.abs F)) (final.abs F)
      ∧ st'.traceRev = revs.reverse :=
  runCoreInterpKleene_replay_soundE π fuel d start final cfg oracle st' hprocs hrun F
    (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) hfac hd hinv htr

/-- **Core call-aware Kleene completeness.** Every derivation of the engine-realizable Kleene
    semantics `StepKleeneEngStarE R (EvalCommandEngAtE π R n)` (each `.choice`, `.loop` and
    in-call nondeterministic choice read off the choice record `R`, calls nested at most `n`
    deep) from the semantic image under the factory `F` of a tracked interpreter configuration
    `start` that denotes at `F`, reaching a terminal config, is reproduced by a
    `runCoreInterpKleene π` run from `start` at every sufficiently large fuel and call-depth
    limit, ending in a configuration that denotes at `F` and stands for the derivation's end,
    and emitting runtime events whose semantic images are exactly the derivation's events. It
    assumes that the observation `obs` emits every event and resolves every choice recorded in
    `R` under the reader config `cfgr`. Turning a plain `StepKleeneExtStarE`
    derivation into an engine-realizable one is a separate realizability argument. -/
theorem runCoreInterpKleene_completeE {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m)
    (π : String → Option Procedure)
    (F : Expression.Factory) (R : ChoiceRecord Expression) (n : Nat)
    (cfgr : obs.Cfg)
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (start : IKleeneConfig Expression Command) (final : KleeneConfig Expression Command)
    (evs : List (Event Expression)) (hden : start.Denoting F) (ht : start.Tracked)
    (hstar : StepKleeneEngStarE R (Imperative.Calls.EvalCommandEngAtE π R n) (start.abs F)
      evs final)
    (hdone : ∃ e, final = .terminal e) (st : obs.St) :
    ∃ (f0 : Nat) (final' : IKleeneConfig Expression Command) (st' : obs.St),
      final'.abs F = final ∧ final'.Denoting F ∧ (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterpKleene π fuel start d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs :=
  runInterpKleene_callCompleteE obs π R n cfgr hemit hchoose boundedEvalMono_core _ final evs
    start ⟨hden, ht, rfl⟩ hstar hdone st

/-- **Core call-aware Kleene completeness along an oracle**, monad-generically.  An
    oracle-reading Kleene run over the call-aware command relation `Calls.OracleCmdAt π n` (calls
    nested at most `n` deep; each `.choice`, `.loop` and command choice arbitrary) from the
    semantic image under the factory `F` of a tracked interpreter configuration `start` that
    denotes at `F`, with oracle `o`, to a terminal `y.1` with oracle `y.2`, whose events satisfy
    `Q`, is reproduced, from every state `st` with `Pending st o`, by a `runCoreInterpKleene π` run
    from `start` at every sufficiently large fuel and call-depth limit, ending in a configuration
    that denotes at `F` and stands for `y.1`, leaving `Pending st' y.2` and emitting runtime
    events whose semantic images are exactly the run's events.  It assumes that `emit` succeeds
    on the events satisfying `Q`, that `choose` follows the pending choices that `R` allows, that
    every engine-realizable base-command step with typed choices is one with choices in `R`
    (`hlift`), and that `R` allows `tt` and `ff` as Booleans (`hbool`). -/
theorem runCoreInterpKleene_complete_follows {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m) (π : String → Option Procedure) (cfgr : obs.Cfg)
    {F : Expression.Factory} {R : ChoiceRecord Expression} {Q : Event Expression → Prop}
    (Pending : obs.St → List Expression.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE Expression (ChoiceRecord.typed Expression) f σ c σ' evs →
      EvalCmdEngE Expression R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    (n : Nat) {start : IKleeneConfig Expression Command} {o : List Expression.Val}
    {y : KleeneConfig Expression Command × List Expression.Val}
    {evs : List (Event Expression)} (hd : start.Denoting F) (ht : start.Tracked)
    (hrun : ReflTransTrace (OracleKleeneStepE (Calls.OracleCmdAt π n)) (start.abs F, o) evs y)
    (hdone : ∃ e, y.1 = .terminal e) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St)
    (hst : Pending st o) :
    ∃ (f0 : Nat) (final' : IKleeneConfig Expression Command) (st' : obs.St),
      final'.abs F = y.1 ∧ final'.Denoting F ∧ (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterpKleene π fuel start d) cfgr st = (.ok final', st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs :=
  runInterpKleene_callComplete_follows obs π cfgr Pending hemit hf boundedEvalMono_core hlift
    hbool n hd ht hrun hdone hq st hst

/-- **Core call-aware Kleene `ReplayM` completeness**, nondeterministic runs included.  If an
    oracle-reading Kleene run over `Calls.OracleCmdAt π n` from the semantic image under the
    factory `F` of a tracked interpreter configuration `start` that denotes at `F` reads the
    choices `cs` and reaches the terminal configuration `final` (oracle `cs` consumed), then from
    every replay state whose oracle tail begins with a runtime segment `rs` that witnesses `cs`
    (`OracleWitness`) and passes `choose`'s type check for typed choices (`OracleTyped`), under
    every config whose stop hook is off, `runCoreInterpKleene π` from `start` reaches a
    configuration that denotes at `F` and stands for `final` at every sufficiently large fuel and
    call-depth limit, prepending runtime events denoting exactly the run's events to the trace. -/
theorem runCoreInterpKleene_replayComplete (π : String → Option Procedure)
    (cfg : ReplayCfg Expression) {F : Expression.Factory}
    (hcfg : cfg.interruptOn = fun _ => none) (n : Nat)
    {start : IKleeneConfig Expression Command} {final : KleeneConfig Expression Command}
    {evs : List (Event Expression)} {cs : List Expression.Val}
    (hd : start.Denoting F) (ht : start.Tracked)
    (hrun : ReflTransTrace (OracleKleeneStepE (Calls.OracleCmdAt π n)) (start.abs F, cs) evs
      (final, []))
    (hdone : ∃ e, final = .terminal e) (st : ReplayState Expression) (rs : List Expression.Expr)
    (hpre : rs <+: st.remaining) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed Expression) rs cs) :
    ∃ (f0 : Nat) (final' : IKleeneConfig Expression Command) (st' : ReplayState Expression),
      final'.abs F = final ∧ final'.Denoting F ∧ (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        replayRun (runCoreInterpKleene π fuel start d) cfg st = (.ok final', st'))
      ∧ (obsReplay (P := Expression)).TraceExt F st st' evs :=
  kleene_replayRun_complete π cfg hcfg boundedEvalMono_core n hd ht hrun hdone st rs hpre hrs hty

end -- public section

end Core
