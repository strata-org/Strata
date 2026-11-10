/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterCFG
public import Strata.DL.Imperative.InterpreterCFGCallComplete
public import Strata.DL.Imperative.InterpreterCFGKleeneFollows
import all Strata.Languages.Core.InterpreterCFG
import Strata.Languages.Core.InterpreterProps
public import Strata.Languages.Core.InterpreterEvalSound

/-! # Soundness and completeness of the Core call-aware monadic CFG interpreter

Key theorems, both stated against the event-trace CFG reference semantics:
* `runCoreInterpCFG_soundE`: a successful `runCoreInterpCFG` run is a `StepCFGExtStarE`
  derivation emitting exactly the run's recorded events;
* `runCoreInterpCFG_soundE_of_evalFactoryWF`: the same, with the bounded evaluator's soundness
  derived from `EvalFactoryWF` of the factory;
* `runCoreInterpCFG_completeE`: every engine-realizable CFG derivation ending in a halted
  config is reproduced by a `runCoreInterpCFG` run at every sufficiently large fuel;
* `runCoreInterpCFG_complete_follows`, `runCoreInterpCFG_replayComplete`: every CFG run that
  reads its nondeterministic choices off an oracle and halts is reproduced by a
  `runCoreInterpCFG` run at every sufficiently large fuel, along the oracle, monad-generically and
  under `ReplayM`. -/

namespace Core

open Imperative Imperative.Calls

public section

/-- **Core call-aware CFG soundness.**  Let a `runCoreInterpCFG π` run, observed through
    `obs`, succeed from `start` to `final`, where `start` denotes at the factory `F`
    (`ICFGConfig.Denoting`).  Assume every procedure of `π` passes the local well-formedness
    check `ProcsOk` (distinct formals; a body with every exit covered and every call site well
    formed), `F` is well-formed (`FactoryWF`), the semantic image of `start` (`ICFGConfig.abs`)
    satisfies the CFG invariant `CFGCfgInv` at `F` (a well-formed, typed running store,
    well-formed call sites in every block, and `F` in the environment), and the bounded
    evaluator is sound at `F` (`BoundedEvalSoundAt`).  Then the run is
    a derivation of the call-aware CFG reference semantics `StepCFGExtStarE π` from the semantic
    image of `start` to exactly that of `final`, emitting the semantic images of exactly the
    events the run recorded, and `final` denotes at `F`. -/
theorem runCoreInterpCFG_soundE {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m)
    (π : String → Option Procedure)
    (F : Expression.Factory)
    (hprocs : Calls.ProcsOk π)
    (hfac : FactoryWF (P := Expression) F)
    (hEval : BoundedEvalSoundAt Expression F)
    (fuel : Nat) (start final : ICFGConfig String Command Expression)
    (cfgr : obs.Cfg) (st st' : obs.St)
    (hden : start.Denoting F)
    (hInv : Calls.CFGCfgInv π F (start.abs F))
    (hrun : obs.run (runCoreInterpCFG π fuel start) cfgr st = (.ok final, st')) :
    ∃ revs : List (IEvent Expression), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGExtStarE π (start.abs F) (revs.map (REvent.abs F)) (final.abs F)
      ∧ final.Denoting F :=
  runInterpCFG_callSoundE obs π F hprocs hfac hEval fuel _ start final cfgr
    st st' hden hInv hrun

/-- **Core call-aware CFG soundness.** Let a `runCoreInterpCFG π` run, observed through `obs`,
    succeed from `start` to `final`, where `start` denotes at the factory `F`
    (`ICFGConfig.Denoting`). Assume every procedure of `π` passes the local well-formedness check
    `ProcsOk` (distinct formals; a body with every exit covered and every call site well formed),
    `F` is well-formed (`FactoryWF`), the semantic image of `start` (`ICFGConfig.abs`) satisfies the
    CFG invariant `CFGCfgInv` at `F` (a well-formed, typed running store, well-formed call sites in
    every block, and `F` in the environment), and the functions of `F` meet the conditions under
    which the bounded evaluator is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives
    program factories). Then the run is a derivation of the call-aware CFG reference semantics
    `StepCFGExtStarE π` from the semantic image of `start` to exactly that of `final`, emitting the
    semantic images of exactly the events the run recorded, and `final` denotes at `F`. -/
theorem runCoreInterpCFG_soundE_of_evalFactoryWF
    {m : Type → Type}
    [Monad m]
    [LawfulMonad m]
    [InterpEffects Expression m]
    [MonadExcept StopReason m]
    (obs : InterpObs Expression m)
    (π : String → Option Procedure)
    (F : Expression.Factory)
    (hprocs : Calls.ProcsOk π)
    (hfac : FactoryWF (P := Expression) F)
    (hEvalF : EvalFactoryWF F.factory)
    (fuel : Nat)
    (start final : ICFGConfig String Command Expression)
    (cfgr : obs.Cfg)
    (st st' : obs.St)
    (hden : start.Denoting F)
    (hInv : Calls.CFGCfgInv π F (start.abs F))
    (hrun : obs.run (runCoreInterpCFG π fuel start) cfgr st = (.ok final, st')) :
    ∃ revs : List (IEvent Expression), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGExtStarE π (start.abs F) (revs.map (REvent.abs F)) (final.abs F)
      ∧ final.Denoting F :=
  runCoreInterpCFG_soundE obs π F hprocs hfac (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) fuel
    start final cfgr st st' hden hInv hrun

/-- **Core call-aware CFG completeness.**  Every derivation of the engine-realizable CFG
    semantics (the engine-realizable CFG event closure `StepCFGEngStarE` whose command relation
    `EvalCommandEngAtE π R n` reads every nondeterministic choice off the choice record `R` and
    nests calls at most `n` deep) from the semantic image under the factory `F` (`ICFGConfig.abs`)
    of a configuration `start` that denotes at `F`, ending in a halted config, is reproduced by a
    `runCoreInterpCFG π` run from `start` at every sufficiently large fuel, reaching a configuration
    that denotes the derivation's end and emitting runtime events whose semantic images are exactly
    its events.  It assumes that the observation `obs` emits every event and resolves every choice
    recorded in `R` under the reader config `cfgr`.  The derivation's guard steps carry the
    engine's guard evaluation (`StepCFGEngE`). -/
theorem runCoreInterpCFG_completeE {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m)
    (π : String → Option Procedure)
    (F : Expression.Factory) (R : ChoiceRecord Expression) (n : Nat) (cfgr : obs.Cfg)
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (start : ICFGConfig String Command Expression) (final : CFGConfig String Command Expression)
    (evs : List (Event Expression)) (hden : start.Denoting F)
    (hstar : StepCFGEngStarE Expression (Calls.EvalCommandEngAtE π R n) (start.abs F)
      evs final)
    (hdone : final.Done) (st : obs.St) :
    ∃ (f0 : Nat) (final' : ICFGConfig String Command Expression) (st' : obs.St),
      final'.abs F = final ∧ final'.Denoting F ∧ (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterpCFG π fuel start d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs :=
  (runInterpCFG_callCompleteE obs π F R n cfgr hemit hchoose boundedEvalMono_core start final evs
    hden hstar hdone st).imp fun _ ⟨st', final', ⟨hd, ha⟩, h, ht⟩ => ⟨final', st', ha, hd, h, ht⟩

/-- **Core call-aware CFG completeness along an oracle**, monad-generically.  An oracle-reading
    CFG run over the call-aware command relation `Calls.OracleCmdAt π n` (calls nested at most `n`
    deep; nondeterministic choices arbitrary) from the semantic image under the factory `F` of a
    configuration `start` that denotes at `F`, with oracle `o`, to a halted `y.1` with oracle
    `y.2`, whose events satisfy `Q`, is reproduced, from every state `st` with `Pending st o`, by
    a `runCoreInterpCFG π` run from `start` at every sufficiently large fuel and call-depth limit,
    reaching a configuration that denotes `y.1`, leaving `Pending st' y.2` and emitting runtime
    events whose semantic images are exactly the run's events.  It assumes that `emit` succeeds
    on the events satisfying `Q`, that `choose` follows the pending choices that `R` allows, that
    every engine-realizable base-command step with typed choices is one with choices in `R`
    (`hlift`), and that `R` allows `tt` and `ff` as Booleans (`hbool`). -/
theorem runCoreInterpCFG_complete_follows {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m) (π : String → Option Procedure) (cfgr : obs.Cfg)
    {F : Expression.Factory} {R : ChoiceRecord Expression} {Q : Event Expression → Prop}
    (Pending : obs.St → List Expression.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE Expression (ChoiceRecord.typed Expression) f σ c σ' evs →
      EvalCmdEngE Expression R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    (n : Nat) {start : ICFGConfig String Command Expression} {o : List Expression.Val}
    {y : CFGConfig String Command Expression × List Expression.Val}
    {evs : List (Event Expression)} (hden : start.Denoting F)
    (hrun : ReflTransTrace (OracleCFGStepE (Calls.OracleCmdAt π n)) (start.abs F, o) evs y)
    (hdone : y.1.Done) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st o) :
    ∃ f0 st', ∃ y1 : ICFGConfig String Command Expression, y1.Denotes F y.1 ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterpCFG π fuel start d) cfgr st = (.ok y1, st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs :=
  runInterpCFG_callComplete_follows obs π cfgr Pending hemit hf boundedEvalMono_core hlift hbool n
    hden hrun hdone hq st hst

/-- **Core call-aware CFG `ReplayM` completeness**, nondeterministic runs included.  If an
    oracle-reading CFG run over `Calls.OracleCmdAt π n` from the semantic image under the factory
    `F` of a configuration `start` that denotes at `F` reads the choices `cs` and halts at
    `final` (oracle `cs` consumed), then from every replay state whose oracle tail begins with a
    runtime segment `rs` that witnesses `cs` (`OracleWitness`) and passes `choose`'s type check
    for typed choices (`OracleTyped`), under every config whose stop hook is off,
    `runCoreInterpCFG π` from `start` reaches a configuration denoting `final` at every
    sufficiently large fuel and call-depth limit, prepending runtime events denoting exactly the
    run's events to the trace. -/
theorem runCoreInterpCFG_replayComplete (π : String → Option Procedure)
    (cfg : ReplayCfg Expression) {F : Expression.Factory}
    (hcfg : cfg.interruptOn = fun _ => none) (n : Nat)
    {start : ICFGConfig String Command Expression} {final : CFGConfig String Command Expression}
    {evs : List (Event Expression)} {cs : List Expression.Val} (hden : start.Denoting F)
    (hrun : ReflTransTrace (OracleCFGStepE (Calls.OracleCmdAt π n)) (start.abs F, cs) evs
      (final, []))
    (hdone : final.Done) (st : ReplayState Expression) (rs : List Expression.Expr)
    (hpre : rs <+: st.remaining) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed Expression) rs cs) :
    ∃ f0 st', ∃ final' : ICFGConfig String Command Expression, final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        replayRun (runCoreInterpCFG π fuel start d) cfg st = (.ok final', st'))
      ∧ (obsReplay (P := Expression)).TraceExt F st st' evs :=
  cfg_replayRun_complete π cfg hcfg boundedEvalMono_core n hden hrun hdone st rs hpre hrs hty

end -- public section

end Core
