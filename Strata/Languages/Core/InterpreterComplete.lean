/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCompleteObs
public import Strata.Languages.Core.InterpreterObs
import Strata.Languages.Core.InterpreterObsProps
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.InterpreterCompleteGeneric
import all Strata.Languages.Core.InterpreterObs
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.Interpreter
import Strata.Languages.Core.InterpreterReplayTactics
import Strata.Languages.Core.InterpreterDomainProps
import Strata.DL.Lambda.LExprEvalFuelProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps
public import Strata.Languages.Core.InterpreterProps
public import Strata.DL.Imperative.InterpreterCallCompleteProps
import all Strata.DL.Imperative.InterpreterCallCompleteProps

/-! # Core-level whole-run completeness

Reads the monad-generic whole-run completeness off Core's language instance and Core's
`EvalM` observation.

The generic development's hypothesis on the language's evaluator is discharged at Core by
`boundedEvalMono_core` (`Core.evalBounded` is upward fuel-monotone).  The reference runs are
related to engine runs by the run-local premise `EngineAgreesFrom`: every reference step from a
configuration the run reaches is an engine-realizable step, whose rules carry the engine's
evaluation facts (`EngEval`).  For `EvalM`, whose `emit` can throw, `runInterpEval_complete_on`
assumes that every list of well-formed runtime events (`Calls.EvGood`) standing for the
derivation's events goes through (`EvalEmitsOk`); the global `EmitTotal` is unsatisfiable
(`not_emitTotal_obsEval`).

The last section of this module reduces the engine-check agreement at Core to a typing
condition on `.init`/`.set` right-hand sides (`CoreTypesAgreeAt`).

Key theorems: `runInterpReplay_complete`, `runInterpEval_complete_on`, `evalEmitOk_iff`,
`not_emitTotal_obsEval`, `engineChecksAgreeAt_of_coreTypesAgree`,
`runInterpReplay_complete_assert`. -/

namespace Core

open Imperative

public section

section CoreLang

/-! ## `ReplayM` completeness at Core -/

/-- **Core replay completeness under engine agreement.**  If every reference step from a
    configuration a reference run from `start` reaches is an engine-realizable step under the
    empty choice record (`EngineAgreesFrom`), then every reference run from `start` that ends in a
    done configuration is reproduced by a `ReplayM` run of the base-command engine with the stop
    hook off from every interpreter configuration `istart` denoting `start` to one denoting
    `final`, at every sufficiently large fuel, with runtime events denoting exactly the run's
    events prepended to the trace. -/
theorem runInterpReplay_complete {F : Expression.Factory}
    (cfg : (Imperative.obsReplay (P := Expression)).Cfg)
    (hcfg : cfg.interruptOn = fun _ => none)
    (start final : Config Expression (Cmd Expression)) (evs : List (Event Expression))
    (istart : IConfig Expression (Cmd Expression)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := Expression) (ChoiceRecord.bot Expression)
      (@EvalCmdE Expression _ _) (EvalCmdEngE Expression (ChoiceRecord.bot Expression)) start)
    (st : (Imperative.obsReplay (P := Expression)).St)
    (hrun : StepStmtStarE Expression (@EvalCmdE Expression _ _)
              start evs final)
    (hdone : Imperative.Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig Expression (Cmd Expression))
      (st' : (Imperative.obsReplay (P := Expression)).St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        (Imperative.obsReplay (P := Expression)).run
          (runInterp (baseStepCmd (P := Expression) (m := ReplayM Expression)) fuel
            istart)
          cfg st = (.ok final', st'))
      ∧ (Imperative.obsReplay (P := Expression)).TraceExt F st st' evs :=
  runInterp_complete_replay_of_agree _ hcfg boundedEvalMono_core _ _ _ st istart hstart hag hrun
    hdone

/-! ## `EvalEmitOk`: when `EvalM`'s `emit` succeeds on one event -/

/-- `EvalM`'s `emit` succeeds on `ev` at `opts`: a `cover` always; an `assert` whose captured
    condition evaluates to `true` (`.halt`) or to a Boolean literal (`.collect`), up to metadata
    (`InterpLang.boolLit?`); an `assume` always (`.ignore`) or when its condition evaluates to
    `true` up to metadata (`.enforce`). -/
@[expose] def EvalEmitOk (opts : EvalOpts) : IEvent Expression → Prop
  | .assert arg =>
    match opts.assertPolicy with
    | .halt =>
      (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
        (InterpLang.boolLit? (P := Expression)) = some true
    | .collect =>
      (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
          (InterpLang.boolLit? (P := Expression)) = some true
        ∨ (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
          (InterpLang.boolLit? (P := Expression)) = some false
  | .assume arg =>
    match opts.assumePolicy with
    | .ignore => True
    | .enforce =>
      (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
        (InterpLang.boolLit? (P := Expression)) = some true
  | .cover _ => True

/-- Every event a run emits goes through under `opts`. -/
@[expose] def EvalEmitsOk (opts : EvalOpts) (evs : List (IEvent Expression)) : Prop :=
  ∀ ev ∈ evs, EvalEmitOk opts ev

/-! ### `EvalEmitOk` at each policy -/

/-- Under `AssertPolicy.halt`, an emitted `assert` must evaluate to `true` up to metadata. -/
theorem evalEmitOk_assert_halt (opts : EvalOpts) (harg : opts.assertPolicy = .halt)
    (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    EvalEmitOk opts (.assert arg)
      ↔ (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
          (InterpLang.boolLit? (P := Expression)) = some true := by simp! [*]

/-- Under `AssertPolicy.collect`, an emitted `assert` must evaluate to a Boolean literal up to
    metadata. -/
theorem evalEmitOk_assert_collect (opts : EvalOpts) (harg : opts.assertPolicy = .collect)
    (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    EvalEmitOk opts (.assert arg)
      ↔ ((evalBounded opts.fuel arg.factory arg.store arg.expr).bind
            (InterpLang.boolLit? (P := Expression)) = some true
          ∨ (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
            (InterpLang.boolLit? (P := Expression)) = some false) := by simp! [*]

/-- Under `AssumePolicy.ignore`, an emitted `assume` is unconstrained. -/
theorem evalEmitOk_assume_ignore (opts : EvalOpts) (hass : opts.assumePolicy = .ignore)
    (arg : REventArg Expression (Lambda.Factory CoreLParams)) : EvalEmitOk opts (.assume arg) := by simp! [*]

/-- Under `AssumePolicy.enforce`, an emitted `assume` must evaluate to `true` up to metadata. -/
theorem evalEmitOk_assume_enforce (opts : EvalOpts) (hass : opts.assumePolicy = .enforce)
    (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    EvalEmitOk opts (.assume arg)
      ↔ (evalBounded opts.fuel arg.factory arg.store arg.expr).bind
          (InterpLang.boolLit? (P := Expression)) = some true := by simp! [*]

/-- A `cover` event is unconstrained under every policy. -/
theorem evalEmitOk_cover (opts : EvalOpts) (arg : REventArg Expression (Lambda.Factory CoreLParams)) :
    EvalEmitOk opts (.cover arg) := ⟨⟩

/-! ### `EvalEmitOk` is exactly `emit`-success -/

/-- `EvalEmitOk` suffices: `emit` records the event and continues. -/
private theorem evalRun_emit_ok_of_evalEmitOk (opts : EvalOpts) (ev : IEvent Expression)
    (h : EvalEmitOk opts ev) (st : EvalState) :
    ∃ st', evalRun (InterpEffects.emit (P := Expression) (m := EvalM) ev) opts st
             = (.ok ⟨⟩, st') := by
  simp only [InterpEffects.emit, evalRun_read_bind]
  (repeat' split) <;> simp only [EvalEmitOk, *] at h <;> (try split at h) <;>
    simp_all only [Option.bind_some, Option.some.injEq, Bool.false_eq_true, or_true, evalRun_modify,
        Prod.mk.injEq, true_and, exists_eq', Bool.true_eq_false, or_false, reduceCtorEq, or_self,
        Option.bind_none]

/-- `EvalEmitOk` is necessary: a successful `emit` witnesses it. -/
private theorem evalEmitOk_of_evalRun_emit_ok (opts : EvalOpts) (ev : IEvent Expression)
    (st st' : EvalState) (u : Unit)
    (h : evalRun (InterpEffects.emit (P := Expression) (m := EvalM) ev) opts st
          = (.ok u, st')) :
    EvalEmitOk opts ev := by
  simp only [InterpEffects.emit, evalRun_read_bind] at h
  (repeat' split at h) <;> cases h <;> grind [EvalEmitOk]

/-- `EvalEmitOk` characterizes `emit`-success, at every state. -/
theorem evalEmitOk_iff (opts : EvalOpts) (ev : IEvent Expression) :
    EvalEmitOk opts ev
      ↔ ∀ st : EvalState,
          ∃ st', evalRun (InterpEffects.emit (P := Expression) (m := EvalM) ev) opts st
                   = (.ok ⟨⟩, st') :=
  ⟨evalRun_emit_ok_of_evalEmitOk _ _, fun h =>
    let ⟨_, e⟩ := h {}
    evalEmitOk_of_evalRun_emit_ok _ _ _ _ _ e⟩

/-! ### The generic `emit` hypotheses at `EvalM` -/

/-- `EvalM`'s `emit` is total on the event class `EvalEmitOk opts`. -/
theorem emitTotalOn_eval (opts : EvalOpts) :
    Imperative.EmitTotalOn obsEval opts
      (fun ev => ∀ (F : Expression.Factory) (rev : IEvent Expression), rev.abs F = ev →
        EvalEmitOk opts rev) :=
  fun F ev st h => evalRun_emit_ok_of_evalEmitOk _ _ (h F ev rfl) st

/-- Unrestricted `emit` totality is `EvalEmitOk` on every event. -/
private theorem emitTotal_obsEval_iff (opts : EvalOpts) :
    Imperative.EmitTotal obsEval opts ↔ ∀ ev : IEvent Expression, EvalEmitOk opts ev := by
  simp only [evalEmitOk_iff]
  rfl

/-! ### `EmitTotal` is unsatisfiable at `EvalM` -/

/-- An `assert` event whose captured condition is the integer literal `0`. -/
def nonBoolAssertEvent (f : Lambda.Factory CoreLParams) : IEvent Expression :=
  .assert { factory := f, store := fun _ => none, label := "", expr := .intConst default 0,
            metadata := #[] }

/-- `nonBoolAssertEvent f` fails `EvalEmitOk` under every `EvalOpts`. -/
private theorem not_evalEmitOk_nonBoolAssertEvent (opts : EvalOpts) (f : Lambda.Factory CoreLParams) :
    ¬ EvalEmitOk opts (nonBoolAssertEvent f) := by
  simp! only [nonBoolAssertEvent, EvalEmitOk, evalBounded_intConst, Option.some.injEq]
  split <;> nofun

/-- **`EmitTotal` is false at `EvalM`, at every `EvalOpts`**, for every captured factory. -/
theorem not_emitTotal_obsEval (opts : EvalOpts) (f : Lambda.Factory CoreLParams) :
    ¬ Imperative.EmitTotal obsEval opts :=
  (not_evalEmitOk_nonBoolAssertEvent _ f <| (emitTotal_obsEval_iff _).1 · _)

/-! ## `EvalM` completeness with a satisfiable `emit` hypothesis -/

/-- Every engine-realizable base-command evaluation from a denoting environment is performed by
    one `baseStepCmd` step that keeps `Pending`, when `emit` succeeds on the well-formed runtime
    events whose images satisfy `Q` (`Calls.EmitGoodOn`) and keeps `Pending`. -/
private theorem cmdFollows_base {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m] (obs : InterpObs Expression m)
    (cfgr : obs.Cfg) {F : Expression.Factory} {Q : Event Expression → Prop}
    (Pending : obs.St → List Expression.Val → Prop) (hemit : Calls.EmitGoodOn obs cfgr F Q)
    (hpe : ∀ ev cs st st' u, obs.run (InterpEffects.emit (P := Expression) ev) cfgr st
      = (.ok u, st') → Pending st cs → Pending st' cs) :
    CmdFollowsFam obs (fun _ _ => baseStepCmd (P := Expression) (m := m)) cfgr F Pending Q
      (OracleCmdEngE (ChoiceRecord.bot Expression)) :=
  fun _ _ _ _ _ _ hdρ h hq st hst =>
    (Calls.oracleCmdEngE_followsG obs cfgr Pending hemit
      ⟨fun _ _ _ _ _ _ _ _ h => False.elim h, hpe⟩ boundedEvalMono_core hdρ.1 h hq st hst).imp
      fun _ ⟨σi, s, hσ, hdσ, a, b⟩ => ⟨σi, s, hσ, hdσ,
        fun _ _ k _ _ hk => obs_stepInterp_cmd_fwd _ _ _ _ _ _ _ _ (hdρ.2 ▸ a k hk), b⟩

/-- A reference run from the abstraction of a tracked configuration `start` whose every step is
    engine-realizable under the empty choice record (`EngineAgreesFrom`), ending at a
    configuration the driver stops at and emitting events satisfying `Q`, is reproduced by
    `runInterp baseStepCmd` from `start` at every large enough fuel from every state `st` with
    `Pending st` at every choice list, to a configuration denoting `final` and a state with
    `Pending · []`, prepending runtime events standing for exactly the run's events to the trace,
    when `emit` succeeds on the well-formed runtime events whose images satisfy `Q` and keeps
    `Pending`. -/
private theorem runInterp_follows_base {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m] (obs : InterpObs Expression m)
    (cfgr : obs.Cfg) {F : Expression.Factory} {Q : Event Expression → Prop}
    (Pending : obs.St → List Expression.Val → Prop) (hemit : Calls.EmitGoodOn obs cfgr F Q)
    (hpe : ∀ ev cs st st' u, obs.run (InterpEffects.emit (P := Expression) ev) cfgr st
      = (.ok u, st') → Pending st cs → Pending st' cs)
    {start : IConfig Expression (Cmd Expression)} {final : Config Expression (Cmd Expression)}
    {evs : List (Event Expression)} (hd : start.Denoting F) (ht : start.Tracked)
    (hag : EngineAgreesFrom (P := Expression) (ChoiceRecord.bot Expression)
      (@EvalCmdE Expression _ _) (EvalCmdEngE Expression (ChoiceRecord.bot Expression))
      (start.abs F))
    (hrun : StepStmtStarE Expression (@EvalCmdE Expression _ _) (start.abs F) evs final)
    (hdone : Imperative.Config.Done final) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St)
    (hst : ∀ cs, Pending st cs) :
    ∃ (f0 : Nat) (final' : IConfig Expression (Cmd Expression)) (st' : obs.St),
      final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (P := Expression) (m := m)) fuel start) cfgr st
          = (.ok final', st'))
      ∧ Pending st' [] ∧ obs.TraceExt F st st' evs := by
  obtain ⟨cs, hcs⟩ := runChoicesParam_of_stepEngStarE (hrun.toStepEngParamStarE' hag)
  obtain ⟨f0, cy, s, hy, h, hp, htr⟩ := runInterp_complete_follows_fam obs _ cfgr Pending
    ⟨fun _ _ _ _ _ _ _ _ h => False.elim h, hpe⟩ boundedEvalMono_core
    (cmdFollows_base obs cfgr Pending hemit hpe)
    (fun _ _ _ _ _ _ _ h => evalCmdE_cmdDefsSound _ _ _ _ _ h.1.toEvalCmdE)
    (List.append_nil cs ▸ hcs []) hdone hq st (hst _) start rfl hd ht
  exact ⟨f0, cy, s, hy, fun k hk => h k k k hk hk hk, hp, htr⟩

/-- **`EvalM` completeness under engine agreement.**  If every reference step from a
    configuration a reference run from `start` reaches is an engine-realizable step under the
    empty choice record (`EngineAgreesFrom`), and every list of well-formed runtime events
    (`Calls.EvGood`) standing for the run's events goes through `EvalM`'s `emit` at `opts`
    (`EvalEmitsOk`), then a reference run from `start` that ends in a done configuration is
    reproduced by an `EvalM` run from every interpreter configuration `istart` denoting `start` to
    one denoting `final` at every sufficiently large fuel, with runtime events denoting exactly its
    events prepended to the trace.  Under `.halt` this asks every emitted assert to evaluate to
    `true`; under `.enforce`, every emitted assume. -/
theorem runInterpEval_complete_on {F : Expression.Factory} (opts : (obsEval).Cfg)
    (start final : Config Expression (Cmd Expression)) (evs : List (Event Expression))
    (istart : IConfig Expression (Cmd Expression)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := Expression) (ChoiceRecord.bot Expression)
      (@EvalCmdE Expression _ _) (EvalCmdEngE Expression (ChoiceRecord.bot Expression)) start)
    (st : (obsEval).St)
    (hrun : StepStmtStarE Expression (@EvalCmdE Expression _ _)
              start evs final)
    (hdone : Imperative.Config.Done final)
    (hemit : ∀ revs : List (IEvent Expression), (∀ ev ∈ revs, Calls.EvGood F ev) →
      revs.map (REvent.abs F) = evs → EvalEmitsOk opts revs) :
    ∃ (f0 : Nat) (final' : IConfig Expression (Cmd Expression)) (st' : (obsEval).St),
      final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        (obsEval).run
          (runInterp (baseStepCmd (P := Expression) (m := EvalM)) fuel istart)
          opts st = (.ok final', st'))
      ∧ (obsEval).TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  have hpg : ∀ (ev : IEvent Expression) (cs : List Expression.Val) (s s' : ReplayState Expression)
      (u : Unit), replayRun (InterpEffects.emit (P := Expression) ev) (Calls.cfgGood F) s
        = (.ok u, s') → (∀ e ∈ s.traceRev, Calls.EvGood F e) →
        ∀ e ∈ s'.traceRev, Calls.EvGood F e :=
    fun ev _ s s' _ he hp e h => by
      have htr : s'.traceRev = ev :: s.traceRev :=
        (obsReplay (P := Expression)).emit_trace _ _ _ _ _ he
      rw [htr] at h
      exact (List.mem_cons.1 h).elim (· ▸ Calls.evGood_of_emit he) (hp e)
  obtain ⟨-, -, sW, -, -, hgW, W, hWm, hWt⟩ := runInterp_follows_base obsReplay (Calls.cfgGood F)
    (Q := fun _ => True) (fun s _ => ∀ e ∈ s.traceRev, Calls.EvGood F e)
    (Calls.emitGood_replay F _) hpg hd ht hag hrun hdone (fun _ _ => trivial)
    { remaining := [] } (fun _ _ h => nomatch h)
  have hWg : ∀ ev ∈ W, Calls.EvGood F ev := fun ev h => hgW ev (by
    change sW.traceRev = W.reverse ++ [] at hWt
    simpa [hWt] using h)
  have hq : ∀ ev ∈ evs, ∀ rev, Calls.EvGood F rev → rev.abs F = ev → EvalEmitOk opts rev := by
    intro ev hev rev hg hab
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hev
    obtain ⟨W1, W2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 hWm
    obtain ⟨w, W2, rfl, -, h3⟩ := List.map_eq_cons_iff.1 h2
    refine hemit (W1 ++ rev :: W2) (fun e he => ?_) (by simp [h1, h3, hab]) rev (by simp)
    simp only [List.mem_append, List.mem_cons] at he
    rcases he with he | rfl | he
    · exact hWg e (by simp [he])
    · exact hg
    · exact hWg e (by simp [he])
  obtain ⟨f0, c, s, hc, h, -, htr⟩ := runInterp_follows_base obsEval opts (fun _ _ => True)
    (fun ev st hg hq => evalRun_emit_ok_of_evalEmitOk _ _ (hq ev hg rfl) st)
    (fun _ _ _ _ _ _ _ => trivial) hd ht hag hrun hdone hq st (fun _ => trivial)
  exact ⟨f0, c, s, hc, h, htr⟩

/-- **`EvalM` completeness under engine agreement at the legacy options.** At
    `EvalOpts.legacy n`, if every reference step from a configuration a reference run from `start`
    reaches is an engine-realizable step under the empty choice record (`EngineAgreesFrom`), every
    reference run from `start`, ending at a configuration the driver stops at and such that every
    assert of every list of well-formed runtime events (`Calls.EvGood`) standing for its events
    evaluates to `true` under `evalBounded n`, is reproduced by an `EvalM` run of
    `runInterp baseStepCmd` from every interpreter configuration `istart` denoting `start` to one
    denoting `final` at every sufficiently large fuel, with runtime events denoting exactly the
    run's events prepended to the trace. -/
theorem runInterpEval_complete_legacy {F : Expression.Factory} (n : Nat)
    (start final : Config Expression (Cmd Expression)) (evs : List (Event Expression))
    (istart : IConfig Expression (Cmd Expression)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := Expression) (ChoiceRecord.bot Expression)
      (@EvalCmdE Expression _ _) (EvalCmdEngE Expression (ChoiceRecord.bot Expression)) start)
    (st : (obsEval).St)
    (hrun : StepStmtStarE Expression (@EvalCmdE Expression _ _)
              start evs final)
    (hdone : Imperative.Config.Done final)
    (hasserts : ∀ revs : List (IEvent Expression), (∀ ev ∈ revs, Calls.EvGood F ev) →
      revs.map (REvent.abs F) = evs → ∀ arg, REvent.assert arg ∈ revs →
      evalBounded n arg.factory arg.store arg.expr = some (HasBool.tt (P := Expression))) :
    ∃ (f0 : Nat) (final' : IConfig Expression (Cmd Expression)) (st' : (obsEval).St),
      final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        (obsEval).run
          (runInterp (baseStepCmd (P := Expression) (m := EvalM)) fuel istart)
          (EvalOpts.legacy n) st = (.ok final', st'))
      ∧ (obsEval).TraceExt F st st' evs := by
  refine runInterpEval_complete_on _ start final evs istart hstart hag st hrun hdone
    fun revs hg hm ev hev => ?_
  cases ev with
  | assert arg =>
    simp [EvalEmitOk, hasserts revs hg hm arg hev, HasBool.tt, Core.true]
  | assume => exact trivial
  | cover => exact trivial

/-! ## Discharging the engine-check obligation at Core

`Imperative.EngineChecksAgreeAt` asks, at the base command in active position of a configuration,
for the engine's evaluation of a deterministic `.init`/`.set` right-hand side: the bounded
evaluator reaches its reference value, and every runtime value it commits passes the three
executable checks `isValue`, `hasType`, `sameType`.  Core's bounded evaluator commits only value
expressions, so the obligation reduces to the reach fact and the *typing* of `.init`/`.set`
right-hand sides (`CoreTypesAgreeAt` below). -/

/-- **The residual obligation at Core, reach and typing.**  What
`Imperative.EngineChecksAgreeAt` amounts to at Core once `isValue` is discharged:
for the base command in active position of `c`, the engine must evaluate the right-hand side
`e` of an `.init x ty (.det e)` to a value of the declared type `ty`, and the right-hand side
`e` of a `.set x (.det e)` to a value that type checks against the factory (`typeCheckWith`) to
the same type as the value already stored at `x`, reaching the reference value at some fuel in
both cases (`EngEval`).
Nothing is asked of `assert`, `assume` or `cover`, and nothing at any store other
than the one `c`'s own environment carries. -/
def CoreTypesAgreeAt (c : Config Expression (Cmd Expression)) : Prop :=
  (∀ (ρ : Imperative.Env Expression) (x : Expression.Ident) (ty : Expression.Ty)
      (e : Expression.Expr) (md : MetaData Expression),
      Imperative.CmdFocus (P := Expression) c ρ (.init x ty (.det e) md) →
      EngEval Expression ρ.factory ρ.store e
        (fun _ r => valueHasType ρ.factory.factory r ty = true))
  ∧ (∀ (ρ : Imperative.Env Expression) (x : Expression.Ident)
      (e : Expression.Expr) (md : MetaData Expression),
      Imperative.CmdFocus (P := Expression) c ρ (.set x (.det e) md) →
      EngEval Expression ρ.factory ρ.store e (fun σr r => ∀ old, σr x = some old →
        old.typeCheckWith ρ.factory.factory [] = r.typeCheckWith ρ.factory.factory []))

/-- Core's bounded evaluator commits only value expressions (`isValue`). -/
private theorem isValue_of_evalBounded {n : Nat} {F : Lambda.Factory CoreLParams}
    {σr : RStore Expression} {e r : Expression.Expr} (h : evalBounded n F σr e = some r) :
    (InterpLang.ops (P := Expression)).isValue F r = true := by
  have he := (evalBounded_eq_some_iff.1 h).2.1
  have hv := Lambda.eval_value_isValue n F σr e (b := true) (by rw [he])
  rwa [he] at hv

/-- The typing condition `CoreTypesAgreeAt c` implies the engine-check agreement
    `EngineChecksAgreeAt R c`, for every choice record `R`. -/
theorem engineChecksAgreeAt_of_coreTypesAgree
    {R : Imperative.ChoiceRecord Expression} {c : Config Expression (Cmd Expression)}
    (h : CoreTypesAgreeAt c) : Imperative.EngineChecksAgreeAt (P := Expression) R c :=
    fun _ _ _ _ f e d => by
  cases e with
  | eval_init e i hty hwf =>
    obtain ⟨hx, rfl⟩ := i.eq_update
    have hi := h.1 _ _ _ _ _ f
    exact .eval_init hx e ⟨hi.1, fun σr n r hsd hb =>
      ⟨isValue_of_evalBounded hb, hi.2 σr n r hsd hb⟩⟩ hty hwf
  | eval_set e u hty hwf =>
    obtain ⟨⟨_, o⟩, rfl⟩ := u.eq_update
    have hs := h.2 _ _ _ _ f
    exact .eval_set o e ⟨hs.1, fun σr n r hsd hb ro hro =>
      ⟨isValue_of_evalBounded hb, beq_iff_eq.2 (hs.2 σr n r hsd hb ro hro)⟩⟩ hty hwf
  | _ => first | constructor | cases d

/-! ### Replay of a one-`assert` program -/

/-- The one-`assert` program is reproduced by a `ReplayM` run at every sufficiently large fuel,
    recording exactly the asserted event. -/
theorem runInterpReplay_complete_assert (cfg : (Imperative.obsReplay (P := Expression)).Cfg)
    (hcfg : cfg.interruptOn = fun _ => none)
    (ρ : IEnv Expression) (label : String) (e : Expression.Expr)
    (md : MetaData Expression) (st : (Imperative.obsReplay (P := Expression)).St) :
    ∃ (f0 : Nat) (st' : (Imperative.obsReplay (P := Expression)).St),
      (∀ fuel, f0 ≤ fuel →
        (Imperative.obsReplay (P := Expression)).run
          (runInterp (baseStepCmd (P := Expression) (m := ReplayM Expression)) fuel
            (.stmt (.cmd (.assert label e md)) ρ))
          cfg st = (.ok (.terminal ρ), st'))
      ∧ (Imperative.obsReplay (P := Expression)).trace st'
          = REvent.assert ⟨ρ.factory, ρ.store.get, label, e, md⟩
            :: (Imperative.obsReplay (P := Expression)).trace st := by
  obtain ⟨_, _⟩ := cfg
  subst hcfg
  refine ⟨1, { st with traceRev := _ :: st.traceRev }, fun fuel hf => ?_, rfl⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  simp only [obsReplay, runInterp, stepInterp, baseStepCmd, stepBaseCmdStore, List.forM_eq_forM,
    bind_pure_comp, Functor.map_map, bind_map_left, runInterp_terminal]
  rfl

/-- The environment with the empty store and the default factory. -/
def assertTrueEnv : Imperative.IEnv Expression :=
  { store := .ofStore (fun _ => none), factory := (default : Lambda.Factory CoreLParams) }

/-- The program `assert "l" tt` in the interpreter environment of `assertTrueEnv` is run to the
    terminal configuration of that environment by a `ReplayM` run from the empty oracle at every
    sufficiently large fuel (`runInterpReplay_complete_assert` at a concrete environment, with
    every hypothesis discharged). -/
private theorem runInterpReplay_complete_assert_nonvacuous :
    ∃ (f0 : Nat) (st' : (Imperative.obsReplay (P := Expression)).St),
      ∀ fuel, f0 ≤ fuel →
        (Imperative.obsReplay (P := Expression)).run
          (runInterp (baseStepCmd (P := Expression) (m := ReplayM Expression)) fuel
            (.stmt (.cmd (.assert "l" (HasBool.tt (P := Expression))
              Imperative.MetaData.empty)) assertTrueEnv))
          {} { remaining := [] }
          = (.ok (.terminal assertTrueEnv), st') :=
  let ⟨f, s, h, _⟩ := runInterpReplay_complete_assert {} rfl ..
  ⟨f, s, h⟩

end CoreLang

end -- public section

end Core
