/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterCallSound
public import Strata.DL.Imperative.InterpreterCompleteGeneric
public import Strata.DL.Imperative.InterpreterCompleteObs
public import Strata.Languages.Core.InterpreterBridgeStatements
public import Strata.DL.Imperative.InterpreterCallComplete
public import Strata.DL.Imperative.InterpreterCallCompleteProps
import all Strata.DL.Imperative.InterpreterCompleteGeneric
import all Strata.Languages.Core.InterpreterBridgeStatements
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterObs
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Languages.Core.Interpreter
import all Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterCallCompleteProps
import Strata.Languages.Core.InterpreterReplayTactics
import Strata.DL.Imperative.CFGSemanticsProps
public import Strata.Languages.Core.InterpreterComplete
public import Strata.DL.Imperative.CmdSemanticsProps

/-! # Core `.call` completeness against the reference event semantics

The completeness direction of Core's `.call` soundness: every reference `.call`
execution is *performed* by the engine (`Core.replayStepCmd`), at every sufficiently
large stepper index and driver fuel, emitting exactly the reference rule's events.
The per-command and whole-run completeness is the generic call-aware completeness
(`Calls.call_runCallInterp_complete`) at `Expression`; this module
states Core's engine-realizable relation over Core's definitions, maps it to the
generic one, and derives `core_runCoreInterp_complete` and, against `CoreStepStarE`,
`core_runCoreInterp_complete_of_agree`.  `core_runCoreInterp_complete_follows` is the generic
`Calls.call_runCallInterp_complete_follows` at `Expression`, and `core_replayRun_complete` is its
`ReplayM` instance.  The `EvalM` theorems `core_runCoreInterp_complete_eval` and
`core_runCoreInterp_complete_eval_of_deterministic` take `emit` only on well-formed runtime events
(`Calls.EvGood`): a replay run of the same reference run supplies well-formed events standing for
its events, and the generic run along the choice sequence with `emit` on well-formed events
(`Calls.call_runCallInterp_follows_prefixG`) then runs at `EvalM`.  `core_replayComplete` is the
generic `Calls.call_replayComplete` at `Expression`.

As in the base-command completeness development, the
derivation has to be given in the **engine-realizable** form, because the reference
relation admits executions the engine rejects on grounds that are not about calls:
a nondeterministic `init x : ty` may commit a value of any type, and the engine's
`choose` rejects it.  `EvalCommandEngAtE` below is Core's engine-realizable command
relation — the reference `EvalCommandE` with its base-command arm replaced by
`EvalCmdEngE` (which carries the engine's executable value checks), its call arm carrying the
engine's argument evaluation (`Calls.CallArgsReach`) and typed write-back check
(`Calls.WriteBackOK`), CFG callee bodies run through `StepCFGEngE`, and with a
**call-nesting height** index.

The height index carries no semantic content: `EvalCommandEngAtE π R n` is the
engine-realizable command relation restricted to derivations whose calls nest at
most `n` deep.  It is there so that the `.call` completeness proof — which must
appeal to whole-run completeness of the callee body, which in turn is built from
command completeness — recurses on a `Nat` rather than through the nested mutual
derivation.  The call arm is the only arm that consumes height. -/

namespace Core

open Imperative

public section

/-! ## Core's engine-realizable command relation, indexed by call-nesting height -/

/-- A Core command relation: what the `.call` arm's callee body run and the
    statement relation are parameterized by. -/
abbrev CoreCmdRel :=
  Expression.Factory → CoreStore → Command → CoreStore → Trace Expression → Prop

/-- A Core procedure-body relation: the callee body run of a `.call` arm. -/
abbrev CoreBodyRel :=
  Procedure.Body → Imperative.Env Expression → CoreStore → Trace Expression → Prop

/-- Execution of a Core procedure body whose commands run through the command relation `E`,
    matching `BigStepE`: a structured body runs as `.block ""` through the engine-realizable
    statement relation built from `E`; a CFG body runs from its entry block at the factory of the
    entry environment through the engine-realizable event-trace CFG relation over `E`
    (`StepCFGEngE`), and its final store is the halting store projected through the entry
    store. -/
@[expose] def CoreBodyExecEngOf
    (R : ChoiceRecord Expression) (E : CoreCmdRel) : CoreBodyRel
  | .structured ss, ρ, σ', emitted =>
      ∃ ρ' : Imperative.Env Expression,
        ReflTransTrace (Imperative.StepEngParamE Expression R E)
          (.stmt (Stmt.block "" ss #[]) ρ) emitted (.terminal ρ')
        ∧ ρ'.store = σ'
  | .cfg g, ρ, σ', emitted =>
      ∃ ρEnd : Imperative.Env Expression,
        StepCFGEngStarE Expression E (.atBlock g g.entry ρ) emitted (.terminal ρEnd)
        ∧ projectStore ρ.store ρEnd.store = σ'

/-- The base-command arm of the engine-realizable Core command relation: the
    reference `EvalCommandE.cmd_sem` arm with the engine's executable value checks
    (`EvalCmdEngE`). -/
@[expose] def CoreCmdArmEng (R : ChoiceRecord Expression) : CoreCmdRel :=
  fun fac σ c σ' emitted =>
    ∃ base, c = CmdExt.cmd base ∧ EvalCmdEngE Expression R fac σ base σ' emitted

/-- The call arm of the engine-realizable Core command relation, with the callee
    body run supplied as `B`: the reference `EvalCommandE.call_sem` arm, plus the two facts the
    engine's `.call` machinery needs of the individual call: the engine reaches the value of
    every input expression (`Calls.CallArgsReach`), and its typed write-back check passes
    (`Calls.WriteBackOK`). -/
@[expose] def CoreCallArmEng (π : String → Option Procedure) (B : CoreBodyRel) : CoreCmdRel :=
  fun fac σ c σ' emitted =>
    ∃ nm p callArgs md σAO σ_final bodyEvents,
      c = CmdExt.call nm callArgs md
      ∧ π nm = some p
      ∧ CallEntry fac σ p callArgs σAO
      ∧ B p.body ⟨σAO, fac⟩ σ_final bodyEvents
      ∧ CallExit fac σ p callArgs σ_final σ'
      ∧ emitted =
          defaultAssertEvents fac σAO (Imperative.Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++ defaultAssertEvents fac σ_final p.spec.postconditions
      ∧ Calls.CallArgsReach fac σ callArgs ∧ Calls.WriteBackOK fac σ p callArgs σ_final

/-- Engine-realizable Core command semantics at call-nesting height `n`: base
    commands at every height, and calls whose callee body is itself an
    engine-realizable run at height `n - 1`.  At height `0` only base commands
    are related. -/
@[expose] def EvalCommandEngAtE
    (π : String → Option Procedure)
    (R : ChoiceRecord Expression) : Nat → CoreCmdRel
  | 0 => CoreCmdArmEng R
  | n + 1 => fun fac σ c σ' emitted =>
      CoreCmdArmEng R fac σ c σ' emitted
      ∨ CoreCallArmEng π
          (CoreBodyExecEngOf R (EvalCommandEngAtE π R n)) fac σ c σ' emitted

/-- Traced closure of the engine-realizable Core statement relation at height `n`. -/
abbrev CoreStepEngAtStarE
    (π : String → Option Procedure)
    (R : ChoiceRecord Expression) (n : Nat) :=
  ReflTransTrace
    (Imperative.StepEngParamE Expression R (EvalCommandEngAtE π R n))

/-! ## Core's engine-realizable relation is the generic one -/

section Bridge

variable (π : String → Option Procedure) (R : ChoiceRecord Expression)

/-- Core's engine-realizable command relation at height `n` implies the generic one. -/
private theorem evalCommandEngAtE_toGeneric :
    ∀ (n : Nat) {fac : Expression.Factory} {σ σ' : CoreStore} {c : Command}
      {evs : Trace Expression},
      EvalCommandEngAtE π R n fac σ c σ' evs →
        Calls.EvalCommandEngAtE π R n fac σ c σ' evs := fun n => by
  induction n with
  | zero => exact id
  | succ _ ih =>
    rintro _ _ _ _ _ (h | ⟨_, ⟨_, _, _ | _⟩, _, _, _, _, _, rfl, k, l, hb, s, t, ha, hw⟩)
    · exact .inl h
    · obtain ⟨_, o, p⟩ := hb
      exact .inr ⟨_, _, _, _, _, _, _, rfl, k, (callEntry_iff ..).1 l,
        ⟨_, o.imp fun _ _ _ => Calls.stepEngParamE_imp (P := Expression) fun _ _ _ _ _ => ih, p⟩,
        (callExit_iff ..).1 s, t, ha, hw⟩
    · obtain ⟨_, o, p⟩ := hb
      exact .inr ⟨_, _, _, _, _, _, _, rfl, k, (callEntry_iff ..).1 l,
        ⟨_, o.imp fun _ _ _ => StepCFGEngE.imp fun _ _ _ _ _ => ih, p⟩, (callExit_iff ..).1 s, t,
        ha, hw⟩

/-- Core's engine-realizable run at height `n` is a generic one. -/
private theorem coreStepEngAtStarE_toGeneric (n : Nat) {c c' : CoreConfig}
    {evs : Trace Expression} (h : CoreStepEngAtStarE π R n c evs c') :
    Calls.StepEngAtStarE π R n c evs c' :=
  h.imp fun _ _ _ => Calls.stepEngParamE_imp (P := Expression) fun _ _ _ _ _ =>
    evalCommandEngAtE_toGeneric π R n

end Bridge

/-! ## Whole-run completeness -/

/-- **Core whole-run completeness at call-nesting height `n`:** for an observation whose `emit`
    always succeeds and whose `choose` resolves `R`, and a fuel-monotone bounded evaluator, every
    engine-realizable Core run from `start` ending in a done config `final` is reproduced by
    `runCoreInterp π` from every interpreter configuration `istart` denoting `start` to one
    denoting `final` at every sufficiently large fuel and call-depth limit, emitting runtime events
    denoting exactly the run's events.  The run's rules carry the engine's evaluation facts
    (`EngEval`, `Calls.CallArgsReach`, `Calls.WriteBackOK`, `StepCFGEngE`). -/
theorem core_runCoreInterp_complete {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m)
    (π : String → Option Procedure)
    (cfgr : obs.Cfg) {F : Expression.Factory} {R : ChoiceRecord Expression}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono Expression)
    (n : Nat) (start final : Config Expression Command) (evs : List (Event Expression))
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (hrun : CoreStepEngAtStarE π R n start evs final) (hdone : Config.Done final)
    (st : obs.St) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterp π fuel istart d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact
    Calls.call_runCallInterp_complete obs π cfgr hemit hchoose hMono n istart final evs hstart.1
      hstart.2.1 (hstart.2.2 ▸ coreStepEngAtStarE_toGeneric π R n hrun) hdone st

/-- **Core whole-run completeness against the reference semantics**: a reference Core run of
    `CoreStepStarE π` along which the engine agrees with Core's engine-realizable relation at
    call-nesting height `n` (`EngineAgreesFrom`), ending in a done config `final`, is reproduced
    by `runCoreInterp π` from every interpreter configuration `istart` denoting `start` to one
    denoting `final` at every sufficiently large fuel and call-depth limit, emitting runtime events
    denoting exactly the run's events. -/
theorem core_runCoreInterp_complete_of_agree {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m) (π : String → Option Procedure)
    (cfgr : obs.Cfg) {F : Expression.Factory} {R : ChoiceRecord Expression}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (n : Nat) (start final : Config Expression Command) (evs : List (Event Expression))
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := Expression) R (EvalCommandE π)
      (EvalCommandEngAtE π R n) start)
    (hrun : CoreStepStarE π start evs final) (hdone : Config.Done final) (st : obs.St) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterp π fuel istart d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact core_runCoreInterp_complete obs π cfgr hemit hchoose boundedEvalMono_core n start final evs
    istart hstart (StepStmtStarE.toStepEngParamStarE hrun hag) hdone st

/-! ## Replay completeness for Core `Command` -/

section CoreReplayComplete

/-- The replay configuration `genuine` runs at: strict oracle. -/
abbrev replayCfgOf (_target : AssertId Expression) (_fuel : Nat) :
    (obsReplay (P := Expression)).Cfg :=
  { oracleConfig := .strict }

/-- **Completeness of Core replay.**  If a reference Core run from the configuration `cex.cfg`
    stands for resolves its choices as `cs` (`Calls.RunChoices`) and emits an event of the target
    obligation whose condition the reference evaluator and the engine both evaluate to the Boolean
    witnessing it (`Calls.assertFailureE`), and `cex.oracle` begins with a runtime segment `rs`
    that witnesses `cs` (`OracleWitness`) and passes `choose`'s type check for typed choices
    (`OracleTyped`), then `cex`, replayed with its own oracle, reaches that failure (`genuine`) at
    every sufficiently large fuel and call-depth limit.  The run may stop anywhere, after the
    failing event or not. -/
theorem core_replayComplete {F : Expression.Factory}
    (π : String → Option Procedure)
    (target : AssertId Expression) (cex : CexA Expression Command)
    {evs : List (Event Expression)} {final : Config Expression Command}
    {cs : List Expression.Val} (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hrun : Calls.RunChoices π (cex.cfg.abs F) evs final cs)
    (rs : List Expression.Expr) (hpre : rs <+: cex.oracle) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed Expression) rs cs)
    (hfail : ∃ ev ∈ evs, Calls.assertFailureE target ev) :
    ∃ f0, ∀ fuel' d, f0 ≤ fuel' → f0 ≤ d → genuine π target fuel' cex d :=
  Calls.call_replayComplete π target cex boundedEvalMono_core F hd ht hrun rs hpre hrs hty hfail

/-- **Core whole-run completeness along a choice sequence**, monad-generically. If a reference Core
    run from `start` resolves its choices as `cs` (`Calls.RunChoices`), ends in a done
    configuration `final` and emits events satisfying `Q`, then from every state `st` with
    `Pending st cs`, `runCoreInterp π` from every interpreter configuration `istart` denoting
    `start` reaches one denoting `final` at every large enough fuel and call-depth limit,
    prepending runtime events denoting exactly the run's events to the trace; given that `emit`
    succeeds on `Q`, that `choose` follows the pending choices that `R` allows, that every
    engine-realizable base-command step with typed choices is one with choices in `R` (`hlift`),
    and that `R` allows `tt` and `ff` as Booleans (`hbool`). -/
theorem core_runCoreInterp_complete_follows {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m) (π : String → Option Procedure) (cfgr : obs.Cfg)
    {F : Expression.Factory}
    {R : ChoiceRecord Expression} {Q : Event Expression → Prop}
    (Pending : obs.St → List Expression.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE Expression (ChoiceRecord.typed Expression) f σ c σ' evs →
      EvalCmdEngE Expression R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    {start final : Config Expression Command} {evs : List (Event Expression)}
    {cs : List Expression.Val} (istart : IConfig Expression Command)
    (hstart : istart.Denotes F start)
    (hrun : Calls.RunChoices π start evs final cs)
    (hdone : Config.Done final) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCoreInterp π fuel istart d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact
    Calls.call_runCallInterp_complete_follows obs π cfgr Pending hemit hf boundedEvalMono_core hlift
      hbool hstart.1 hstart.2.1 (hstart.2.2 ▸ hrun) hdone hq st hst

/-- **Whole-run Core `ReplayM` completeness with calls**, nondeterministic runs included.  If a
    reference Core run from `start` resolves its choices as `cs` (`Calls.RunChoices`) and ends in
    a done configuration `final`, then from every replay state whose oracle tail begins with a
    runtime segment `rs` that witnesses `cs` (`OracleWitness`) and passes `choose`'s type check
    for typed choices (`OracleTyped`), under every config whose stop hook is off,
    `runCoreInterp π` from every interpreter configuration `istart` denoting `start` reaches one
    denoting `final` at every large enough fuel and call-depth limit, prepending runtime events
    denoting exactly the run's events to the trace. -/
theorem core_replayRun_complete {F : Expression.Factory} (π : String → Option Procedure)
    (cfg : ReplayCfg Expression)
    (hcfg : cfg.interruptOn = fun _ => none)
    {start final : Config Expression Command} {evs : List (Event Expression)}
    {cs : List Expression.Val} (istart : IConfig Expression Command)
    (hstart : istart.Denotes F start)
    (hrun : Calls.RunChoices π start evs final cs)
    (hdone : Config.Done final) (st : ReplayState Expression) (rs : List Expression.Expr)
    (hpre : rs <+: st.remaining) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed Expression) rs cs) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : ReplayState Expression),
      final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        replayRun (runCoreInterp π fuel istart d) cfg st = (.ok final', st'))
      ∧ (obsReplay (P := Expression)).TraceExt F st st' evs := by
  exact
    Calls.call_replayRun_complete π cfg hcfg boundedEvalMono_core hstart.1 hstart.2.1
      (hstart.2.2 ▸ hrun) hdone st rs hpre hrs hty

/-- **Whole-run Core `EvalM` completeness with calls, on choice-free runs.**  If a reference Core
    run from `start` resolves no choice (`Calls.RunChoices … []`), ends in a done configuration
    `final`, and every list of well-formed runtime events (`Calls.EvGood`) standing for its events
    goes through at `opts` (`EvalEmitsOk`), then from every state `runCoreInterp π` at `EvalM` from
    every interpreter configuration `istart` denoting `start` reaches one denoting `final` at every
    large enough fuel and call-depth limit, prepending runtime events denoting exactly the run's
    events to the trace. -/
theorem core_runCoreInterp_complete_eval {F : Expression.Factory} (π : String → Option Procedure)
    (opts : EvalOpts)
    {start final : Config Expression Command} {evs : List (Event Expression)}
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (hrun : Calls.RunChoices π start evs final [])
    (hdone : Config.Done final)
    (hemit : ∀ revs : List (IEvent Expression), (∀ ev ∈ revs, Calls.EvGood F ev) →
      revs.map (REvent.abs F) = evs → EvalEmitsOk opts revs) (st : EvalState) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : EvalState), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        evalRun (runCoreInterp π fuel istart d) opts st = (.ok final', st'))
      ∧ obsEval.TraceExt F st st' evs := by
  have hrun' := hstart.2.2 ▸ hrun
  obtain ⟨-, -, -, st0, -, -, -, -, ⟨-, hgood⟩, revs0, hmap, htr0⟩ :=
    Calls.call_runCallInterp_follows_prefixG (obsReplay (P := Expression)) π (Calls.cfgGood F)
      (Q := fun _ => True) _ (Calls.emitGood_replay F _) (Calls.chooseFollows_good F)
      boundedEvalMono_core (fun _ _ _ _ _ h => h) (fun f _ => HasBool.boolIsValOfTy f)
      hstart.1 hstart.2.1 hrun' (fun _ _ => trivial) { remaining := [] }
      ⟨⟨[], List.nil_prefix, ⟨rfl, nofun⟩, nofun⟩, nofun⟩
  simp only [obsReplay] at htr0
  have hQ : ∀ rev, Calls.EvGood F rev → rev.abs F ∈ evs → EvalEmitOk opts rev := by
    intro rev hg hm
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    have hl : i < revs0.length := by simpa [← hmap] using hi
    have hg0 : ∀ ev ∈ revs0, Calls.EvGood F ev := fun ev h => hgood ev (by simp [htr0, h])
    refine hemit (revs0.set i rev) (fun ev h => ?_) ?_ rev ?_
    · exact (List.mem_or_eq_of_mem_set h).elim (hg0 ev) (· ▸ hg)
    · rw [List.map_set, hmap, ← he, List.set_getElem_self]
    · simp [List.mem_set, hl]
  obtain ⟨k, f0, cy, st', h, hy, hdy, hty, -, ht⟩ :=
    Calls.call_runCallInterp_follows_prefixG obsEval π opts (Q := (· ∈ evs)) (fun _ cs => cs = [])
      (fun ev st hg hm => (evalEmitOk_iff opts ev).1 (hQ ev hg hm) st)
      (chooseFollows_nil _ _ (ChoiceRecord.typed Expression)) boundedEvalMono_core
      (fun _ _ _ _ _ h => h) (fun f _ => HasBool.boolIsValOfTy f) hstart.1 hstart.2.1 hrun'
      (fun _ h => h) st rfl
  refine ⟨f0 + k, cy, st', ⟨hdy, hty, hy⟩, fun fuel d hfuel hd => ?_, ht⟩
  have hk := h (fuel - k) d (by omega) (by omega)
  unfold Calls.runCallInterp at hk
  rw [Nat.sub_add_cancel (by omega : k ≤ fuel),
    runInterp_of_abs_done (P := Expression) (c := cy) _ _ (hy ▸ hdone)] at hk
  exact hk.trans (evalRun_pure cy opts st')

/-- **Whole-run Core `EvalM` completeness with calls, on deterministic programs.**  A reference
    Core run from a configuration of a deterministic program (`Calls.ProgDeterministic`) with a
    choice sequence (`Calls.RunChoices`), ending in a done configuration `final` and whose events
    every list of well-formed runtime events (`Calls.EvGood`) standing for them lets go through at
    `opts` (`EvalEmitsOk`), is reproduced by `runCoreInterp π` at `EvalM` from every interpreter
    configuration `istart` denoting `start` to one denoting `final`, from every state at every large
    enough fuel and call-depth limit, prepending runtime events denoting exactly the run's events to
    the trace. -/
theorem core_runCoreInterp_complete_eval_of_deterministic {F : Expression.Factory}
    (π : String → Option Procedure)
    (opts : EvalOpts)
    {start final : Config Expression Command} {evs : List (Event Expression)}
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (hdet : Calls.ProgDeterministic π start)
    {cs : List Expression.Val} (hrun : Calls.RunChoices π start evs final cs)
    (hdone : Config.Done final)
    (hemit : ∀ revs : List (IEvent Expression), (∀ ev ∈ revs, Calls.EvGood F ev) →
      revs.map (REvent.abs F) = evs → EvalEmitsOk opts revs) (st : EvalState) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : EvalState), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        evalRun (runCoreInterp π fuel istart d) opts st = (.ok final', st'))
      ∧ obsEval.TraceExt F st st' evs := by
  exact core_runCoreInterp_complete_eval π opts istart hstart
    (Calls.runChoices_nil_of_deterministic hdet hrun ▸ hrun) hdone hemit st

end CoreReplayComplete

end -- public section

end Core
