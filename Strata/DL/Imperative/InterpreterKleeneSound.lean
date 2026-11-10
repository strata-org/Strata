/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CallAwareSemantics
public import Strata.DL.Imperative.InterpreterKleene
public import Strata.DL.Imperative.InterpreterKleeneProps
public import Strata.DL.Imperative.InterpreterKleeneCall
public import Strata.DL.Imperative.KleeneStmtSemantics
public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.DL.Imperative.InterpreterObs
public import Strata.DL.Imperative.InterpreterCallSound
import all Strata.DL.Imperative.InterpreterKleene
import all Strata.DL.Imperative.InterpreterKleeneCall
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay

/-! # Soundness of the monadic Kleene interpreter against `StepKleeneE`

A successful monad-generic `runInterpKleene` run from a tracked interpreter configuration
(`IKleeneConfig.Tracked`) corresponds to a reference `StepKleeneStarE` derivation from the
configuration it stands for (`IKleeneConfig.abs`), emitting *exactly* the run's event list and
reaching the configuration the final interpreter configuration stands for (a failing assert is
an event).

The development is monad-generic in an observation `obs : InterpObs P m` (the same
abstraction the structured engine uses, `InterpreterSemanticsSpec.lean`), and
command-generic: the correspondence between the per-command stepper and the
reference command relation `EvalCmd` is a hypothesis (`hCmd`), discharged for the
call-aware stepper `stepKleeneCmd π` from the structured call-aware command soundness
(`InterpreterCallSound.lean`).  This module's own content is the Kleene control-flow
induction, which also threads a configuration invariant (`EnvOk` on the active env,
`CmdOk` on every command) so `hCmd`'s premises are available at each command step, and keeps
every scope frame exact, which needs every reference command evaluation to define only the names
`CmdDefs` lists (`CmdDefsSound`).

Key theorems: `runInterpKleene_soundE` (command-generic), and its call-aware
instances `runCallInterpKleene_soundE` and `runCallInterpKleene_replay_soundE`. -/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type} {m : Type → Type}
variable [HasBool P] [HasBoolOps P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-! ## Configuration invariant -/

/-- Every command appearing in a Kleene statement satisfies `CmdOk`. -/
@[expose] def KStmtCmdOk (CmdOk : CmdT → Prop) : KleeneStmt P CmdT → Prop
  | .cmd c => CmdOk c
  | .seq s1 s2 => KStmtCmdOk CmdOk s1 ∧ KStmtCmdOk CmdOk s2
  | .choice s1 s2 => KStmtCmdOk CmdOk s1 ∧ KStmtCmdOk CmdOk s2
  | .loop s => KStmtCmdOk CmdOk s
  | .block s => KStmtCmdOk CmdOk s

/-- The invariant a sound Kleene run carries: the active env satisfies the
    env-invariant `EnvOk` (its factory stays fixed, so `EnvOk` is a predicate on
    `(factory, store)`), and every command still to execute satisfies `CmdOk`. -/
@[expose] def KCfgOk (EnvOk : P.Factory → SemanticStore P → Prop) (CmdOk : CmdT → Prop) :
    KleeneConfig P CmdT → Prop
  | .stmt s ρ => EnvOk ρ.factory ρ.store ∧ KStmtCmdOk CmdOk s
  | .seq inner s2 => KCfgOk EnvOk CmdOk inner ∧ KStmtCmdOk CmdOk s2
  | .terminal ρ => EnvOk ρ.factory ρ.store
  | .block _ inner => KCfgOk EnvOk CmdOk inner

/-! ## Per-step soundness -/

/-- **Per-step soundness of `stepInterpKleene`.**  One successful `obs.run` of
    `stepInterpKleene` from a tracked (`IKleeneConfig.Tracked`) non-terminal config whose
    abstraction (`IKleeneConfig.abs`) satisfies the invariant `KCfgOk EnvOk CmdOk` (the active
    store satisfies `EnvOk`, every command still to run satisfies `CmdOk`) is one transition of
    the event-trace Kleene reference relation `StepKleeneE` between the abstractions, emitting
    exactly the recorded events; the next config is tracked and its abstraction satisfies the
    invariant.  It assumes that `EnvOk` survives projecting onto a parent store, that each
    successful command step on a `CmdOk` command from an `EnvOk` store is a reference command
    step preserving `EnvOk`, and that every reference command evaluation defines only the names
    `CmdDefs` lists (`hdefs`). -/
private theorem stepInterpKleene_soundE [CmdDefs P CmdT]
    (obs : InterpObs P m)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (EnvOk : P.Factory → SemanticStore P → Prop) (CmdOk : CmdT → Prop)
    (stepCmd : StepCmdStoreM P CmdT m)
    (hProj : ∀ (fac : P.Factory) (σp σ : SemanticStore P),
        EnvOk fac σ → EnvOk fac (projectStore σp σ))
    (F : P.Factory)
    (hCmd : ∀ (fuel : Nat) (σ : IStore P) (c : CmdT)
        (cfgr : obs.Cfg) (st st' : obs.St) (σ' : IStore P),
        CmdOk c → RStore.Denoting F σ.get → EnvOk F (InterpLang.absStore F σ.get) →
        obs.run (stepCmd fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σ', st') →
        ∃ revs : List (IEvent P), EvalCmd F (InterpLang.absStore F σ.get) c
          (InterpLang.absStore F σ'.get) (revs.map (REvent.abs F)) ∧
          EnvOk F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get
          ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    (hdefs : CmdDefsSound EvalCmd)
    (fuel : Nat) :
    ∀ (start : IKleeneConfig P CmdT), (∀ ρ, start ≠ .terminal ρ) →
    ∀ (next : IKleeneConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (stepInterpKleene stepCmd fuel start) cfgr st = (.ok next, st') →
      start.Denoting F → KCfgOk EnvOk CmdOk (start.abs F) → start.Tracked →
      ∃ revs : List (IEvent P), StepKleeneE P EvalCmd (start.abs F) (revs.map (REvent.abs F))
          (next.abs F)
        ∧ obs.trace st' = revs.reverse ++ obs.trace st
        ∧ next.Denoting F ∧ KCfgOk EnvOk CmdOk (next.abs F) ∧ next.Tracked := by
  have hdlvl : ∀ c : IKleeneConfig P CmdT, c.Denoting F → RStore.Denoting F c.lvl := by
    intro c
    induction c <;> simp_all [IKleeneConfig.Denoting, IKleeneConfig.lvl]
  have hG : ∀ {fuel ρ cfgr st st' b}, obs.run (resolveGuard (P := P) fuel ρ .nondet) cfgr st
      = (.ok b, st') → obs.trace st' = obs.trace st := by
    intro fuel ρ cfgr st st' b h
    simp only [resolveGuard, InterpObs.run_bind] at h
    split at h
    · split at h <;> simp only [InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq,
        Except.ok.injEq, reduceCtorEq, false_and] at h
      all_goals exact h.2 ▸ (obs.choose_sound _ _ _ _ _ _ _ ‹_›).2
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  intro start
  induction start with
  | stmt s ρ =>
    intro _ next cfgr st st' hr hd hok _
    obtain ⟨hds, hfac⟩ := hd
    obtain ⟨henv, hsok⟩ := hok
    cases s with
    | cmd c =>
      simp only [stepInterpKleene, InterpObs.run_bind, InterpObs.run_pure] at hr
      split at hr <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rename_i σ' _ hc
      rw [hfac] at hc
      obtain ⟨revs, he, henv', hd', htr⟩ := hCmd _ _ _ _ _ _ _ hsok hds henv hc
      exact ⟨revs, .step_cmd he, htr, ⟨hd', hfac⟩, henv', trivial⟩
    | _ =>
      simp only [stepInterpKleene, InterpObs.run_bind, InterpObs.run_pure] at hr
      all_goals (repeat' (first
        | split at hr
        | simp only [InterpObs.run_pure, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq,
            false_and] at hr))
      all_goals obtain ⟨rfl, rfl⟩ := hr
      all_goals refine ⟨[], by constructor, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (simp; done)
        | (simp [hG ‹_›]; done)
        | exact ⟨hds, hfac⟩
        | exact ⟨hds, hds, hfac⟩
        | exact henv
        | exact ⟨henv, hsok⟩
        | exact ⟨henv, hsok.1⟩
        | exact ⟨henv, hsok.2⟩
        | exact ⟨⟨henv, hsok.1⟩, hsok.2⟩
        | exact ⟨⟨henv, hsok⟩, hsok⟩
        | exact ⟨ScopeFrame.opened_exact _, trivial⟩
        | trivial
  | terminal ρ => exact fun hnt => (hnt ρ rfl).elim
  | seq inner s2 ih =>
    intro _ next cfgr st st' hr hd hok ht
    cases inner with
    | terminal ρ' =>
      simp only [stepInterpKleene, InterpObs.run_pure, Prod.mk.injEq, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨[], .step_seq_done, by simp, hd, ⟨hok.1, hok.2⟩, trivial⟩
    | _ =>
      unfold stepInterpKleene at hr
      simp only [InterpObs.run_bind, InterpObs.run_pure] at hr
      split at hr <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨revs, hs, htr, hd', hok', ht'⟩ := ih (fun _ => nofun) _ _ _ _ ‹_› hd hok.1 ht
      exact ⟨revs, .step_seq_inner hs, htr, hd', ⟨hok', hok.2⟩, ht'⟩
  | block fr inner ih =>
    intro _ next cfgr st st' hr hd hok ht
    obtain ⟨hdp, hdi⟩ := hd
    obtain ⟨hex, hti⟩ := ht
    cases inner with
    | terminal ρ' =>
      simp only [stepInterpKleene, InterpObs.run_pure, Prod.mk.injEq, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [IKleeneConfig.lvl] at hex
      refine ⟨[], ?_, by simp, ⟨?_, hdi.2⟩, ?_, trivial⟩
      · simp only [IKleeneConfig.abs, IEnv.abs, ScopeFrame.exit_eq hex,
          InterpLang.absStore_project _ hdp]
        exact .step_block_done
      · simp only [ScopeFrame.exit_eq hex]
        exact hdi.1.project _
      · simp only [IKleeneConfig.abs, IEnv.abs, ScopeFrame.exit_eq hex,
          InterpLang.absStore_project _ hdp]
        exact hProj _ _ _ hok
    | _ =>
      unfold stepInterpKleene at hr
      simp only [InterpObs.run_bind, InterpObs.run_pure] at hr
      split at hr <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨revs, hs, htr, hd', hok', ht'⟩ := ih (fun _ => nofun) _ _ _ _ ‹_› hdi hok hti
      refine ⟨revs, ?_, htr, ⟨by simpa using hdp, hd'⟩, hok', ScopeFrame.record_exact hex ?_, ht'⟩
      · simp only [IKleeneConfig.abs, ScopeFrame.record_parent]
        exact .step_block_body hs
      · intro x hx
        have hl := StepKleeneE.lvl_defines hdefs hs x
        simp only [IKleeneConfig.lvl_abs, IKleeneConfig.levelCmd?_abs,
          InterpLang.absStore_isSome (hdlvl _ hd'), InterpLang.absStore_isSome (hdlvl _ hdi)] at hl
        exact hl hx

/-! ## Whole-run soundness -/

/-- **Soundness of the monadic Kleene driver against `StepKleeneStarE`.**  A successful
    `obs.run` of `runInterpKleene` from a tracked (`IKleeneConfig.Tracked`) config whose
    abstraction (`IKleeneConfig.abs`) satisfies the invariant `KCfgOk EnvOk CmdOk` (the active
    store satisfies `EnvOk`, every command still to run satisfies `CmdOk`) is a derivation of
    the multi-step event-trace Kleene reference semantics `StepKleeneStarE` from the start's
    abstraction, emitting exactly the recorded events and reaching the abstraction of the final
    configuration.  It assumes that `EnvOk` survives projecting onto a parent store, that each
    successful command step on a `CmdOk` command from an `EnvOk` store is a reference command
    step preserving `EnvOk`, and that every reference command evaluation defines only the names
    `CmdDefs` lists (`hdefs`). -/
theorem runInterpKleene_soundE [CmdDefs P CmdT]
    (obs : InterpObs P m)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (EnvOk : P.Factory → SemanticStore P → Prop) (CmdOk : CmdT → Prop)
    (stepCmd : StepCmdStoreM P CmdT m)
    (hProj : ∀ (fac : P.Factory) (σp σ : SemanticStore P),
        EnvOk fac σ → EnvOk fac (projectStore σp σ))
    (F : P.Factory)
    (hCmd : ∀ (fuel : Nat) (σ : IStore P) (c : CmdT)
        (cfgr : obs.Cfg) (st st' : obs.St) (σ' : IStore P),
        CmdOk c → RStore.Denoting F σ.get → EnvOk F (InterpLang.absStore F σ.get) →
        obs.run (stepCmd fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σ', st') →
        ∃ revs : List (IEvent P), EvalCmd F (InterpLang.absStore F σ.get) c
          (InterpLang.absStore F σ'.get) (revs.map (REvent.abs F)) ∧
          EnvOk F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get
          ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    (hdefs : CmdDefsSound EvalCmd) :
    ∀ (fuel : Nat) (start final : IKleeneConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (runInterpKleene stepCmd fuel start) cfgr st = (.ok final, st') →
      start.Denoting F → KCfgOk EnvOk CmdOk (start.abs F) → start.Tracked →
      ∃ revs : List (IEvent P), StepKleeneStarE P EvalCmd (start.abs F) (revs.map (REvent.abs F))
          (final.abs F)
        ∧ final.Denoting F ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro fuel c _ _ s _ h hd hi ht
  fun_induction runInterpKleene stepCmd fuel c generalizing s <;>
    simp only [InterpObs.run_pure, InterpObs.run_throw, InterpObs.run_bind, Prod.mk.injEq,
      Except.ok.injEq, reduceCtorEq, false_and] at h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .refl _, hd, by simp⟩
  rename_i hnt ih
  split at h <;> rename_i hs
  · obtain ⟨revs, hstepE, htr, hd', hi', ht'⟩ := stepInterpKleene_soundE obs EvalCmd EnvOk CmdOk
      stepCmd hProj F hCmd hdefs _ _ hnt _ _ _ _ hs hd hi ht
    obtain ⟨revs2, hrest, hdf, htr2⟩ := ih _ _ h hd' hi' ht'
    refine ⟨revs ++ revs2, ?_, hdf, by simp [htr, htr2]⟩
    rw [List.map_append]
    exact .step _ _ _ _ _ hstepE hrest
  · simp at h

/-! ## Call-aware specialization

Discharge the command-generic `runInterpKleene_soundE` for the call-aware Kleene
stepper `Calls.stepKleeneCmd π`, with reference command relation
`EvalCmdExtE π`.  The per-command hypothesis `hCmd` is discharged by the
structured call-aware command soundness (`InterpreterCallSound.lean`), the carried env
invariant is the env-part of the structured `CfgInv`, and `CmdOk` is `CmdCallOk π`. -/

namespace Calls

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
    [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasOldIdent P]
    {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
    {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [HasOldIdent P] in
/-- A Kleene configuration whose active environment satisfies `EnvOk` satisfies it together with
    the condition that the factory is the factory of its active environment (`getEnv`). -/
private theorem kCfgOk_factory {EnvOk : P.Factory → SemanticStore P → Prop}
    {CmdOk : CmdExt P → Prop}
    (c : KleeneConfig P (CmdExt P)) (h : KCfgOk EnvOk CmdOk c) :
    KCfgOk (fun f σ => f = c.getEnv.factory ∧ EnvOk f σ) CmdOk c := by
  induction c <;> simp_all [KCfgOk, KleeneConfig.getEnv]

/-- **Call-aware per-command correspondence.**  On a command with well-formed call sites
    (`CmdCallOk`) and a well-formed, typed store (`CallEnvOk`) at a well-formed factory
    (`FactoryWF`), one successful `obs.run` of `stepKleeneCmd π` is a step of the call-aware
    reference command relation `EvalCmdExtE π`, emitting exactly the recorded events, and the
    resulting store satisfies `CallEnvOk`.  It assumes that every procedure of `π` passes
    `ProcsOk` and that at `F` every value the bounded evaluator commits to denotes the reference
    evaluator's value. -/
private theorem callStepKleeneCmd_sound [CallLangWF P] [InterpLangBool P] [LawfulMonad m]
    (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (d fuel : Nat) (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (σ : IStore P)
    (cmd : CmdExt P)
    (cfgr : obs.Cfg) (st st' : obs.St) (σ' : IStore P) (hfac : FactoryWF (P := P) F)
    (hok : CmdCallOk π cmd = true) (hd : RStore.Denoting F σ.get)
    (henv : CallEnvOk (P := P) F (InterpLang.absStore F σ.get))
    (hrun : obs.run (stepKleeneCmd π d fuel (InterpLang.rfactory F) σ cmd) cfgr st =
        (.ok σ', st')) :
    ∃ revs : List (IEvent P), EvalCmdExtE π F (InterpLang.absStore F σ.get) cmd
        (InterpLang.absStore F σ'.get) (revs.map (REvent.abs F)) ∧
      CallEnvOk (P := P) F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  exact (cfg_stepCmd_store_sound obs π hprocs hEval hfac hok hd henv hrun).imp
    fun _ ⟨hev, hrest⟩ => ⟨hev.1, hrest⟩

/-- **Call-aware soundness of the Kleene driver.**  A successful `obs.run` of
    `runCallInterpKleene` from a tracked (`IKleeneConfig.Tracked`) config whose active factory
    is well-formed (`FactoryWF`) and whose abstraction (`IKleeneConfig.abs`) satisfies the
    Kleene invariant (a well-formed, typed active store; well-formed call sites in every command
    still to run) is a derivation of the call-aware Kleene reference semantics
    `StepKleeneExtStarE π` from the start's abstraction, emitting exactly the recorded events
    and reaching the abstraction of the final configuration.  It assumes that every procedure
    of `π` passes `ProcsOk` and that at `F` every value the bounded evaluator commits to denotes the
    reference evaluator's value. -/
theorem runCallInterpKleene_soundE [CallLangWF P] [InterpLangBool P] [LawfulMonad m]
    (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (fuel d : Nat) (start final : IKleeneConfig P (CmdExt P)) (cfgr : obs.Cfg)
    (st st' : obs.St)
    (hrun : obs.run (runCallInterpKleene π fuel start d) cfgr st = (.ok final, st'))
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : start.Denoting F)
    (hinv : KCfgOk (CallEnvOk (P := P)) (fun c => CmdCallOk π c = true) (start.abs F))
    (htr : start.Tracked) :
    ∃ revs : List (IEvent P), StepKleeneExtStarE π (start.abs F) (revs.map (REvent.abs F))
        (final.abs F)
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  exact (runInterpKleene_soundE obs _ _ _ _ callEnvOk_projectStore F
    (fun _ _ _ _ _ _ _ hok hd henv hc =>
      callStepKleeneCmd_sound obs π hprocs _ _ F hEval _ _ _ _ _ _ hfac hok hd henv hc)
    (evalCmdExtE_cmdDefsSound π) _ _ _ _ _ _ hrun hd hinv htr).imp fun _ ⟨hstar, _, htr⟩ =>
    ⟨hstar, htr⟩

/-- **Call-aware soundness over the replay monad.**  From an empty start trace and a tracked
    (`IKleeneConfig.Tracked`) config whose active factory is well-formed (`FactoryWF`) and whose
    abstraction (`IKleeneConfig.abs`) satisfies the Kleene invariant (a well-formed, typed
    active store; well-formed call sites in every command still to run), a successful
    `replayRun` of the monadic Kleene interpreter records exactly the events of a derivation of the
    call-aware Kleene reference semantics `StepKleeneExtStarE π` from the start's abstraction
    to `final`'s, most recent first.  It assumes that every procedure of `π` passes `ProcsOk`
    and that at `F` every value the bounded evaluator commits to denotes the reference evaluator's
    value. -/
theorem runCallInterpKleene_replay_soundE [CallLangWF P] [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (fuel d : Nat) (start final : IKleeneConfig P (CmdExt P))
    (cfg : ReplayCfg P) (oracle : List P.Expr) (st' : ReplayState P)
    (hrun : replayRun (runCallInterpKleene (m := ReplayM P) π fuel start d) cfg
        { remaining := oracle }
      = (.ok final, st'))
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : start.Denoting F)
    (hinv : KCfgOk (CallEnvOk (P := P)) (fun c => CmdCallOk π c = true) (start.abs F))
    (htr : start.Tracked) :
    ∃ revs : List (IEvent P), StepKleeneExtStarE π (start.abs F) (revs.map (REvent.abs F))
        (final.abs F) ∧ st'.traceRev = revs.reverse := by
  exact (runCallInterpKleene_soundE obsReplay _ hprocs _ _ _ _ _ _ _ hrun F hEval hfac hd hinv
    htr).imp fun _ ⟨hstar, htr⟩ => ⟨hstar, htr.trans (List.append_nil _)⟩

end Calls

end -- public section

end Imperative
