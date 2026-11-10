/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterSound
public import Strata.DL.Imperative.InterpreterSemanticsSpec
public import Strata.DL.Imperative.InterpreterProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.InterpreterTypesProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps
public import Strata.DL.Imperative.InterpreterConfigProps
import all Strata.DL.Imperative.InterpreterConfig
import Strata.DL.Imperative.InterpreterTowerProps

/-! # Monad-generic engine soundness

For any observation `obs : InterpObs P m`, a run of the monadic interpreter from a tracked
configuration (`IConfig.Tracked`) is an execution of the reference event-trace semantics
(`StepStmtStarE`) between the configurations the interpreter configurations stand for
(`IConfig.abs`), carrying exactly the events it emitted. The whole-run statement reduces, by the
fuel recursion of `runInterp`, to a per-step obligation: one `stepInterp` step is a single
`StepStmtE` transition carrying its emitted events, and it keeps the configuration tracked.

Key definitions: `StepInterpSoundGeneric` (the per-step obligation for a successful step),
`StepInterpErrSound` and `StepInterpErrSoundInto` (its counterparts for a step that throws).

Key theorems:
* `runInterp_sound_tracked`, `runInterp_sound_generic`: whole-run soundness from a tracked
  configuration, and `RunInterpSound`, from `StepInterpSoundGeneric`;
* `runInterp_traceSound_generic`, `runInterp_trace_sound_generic`: the trace of a run with any
  outcome is accounted for by a reference execution;
* `obs_stepBaseCmdStore_sound`: a successful base-command step is an `EvalCmdE` evaluation;
* `stepInterpSoundGeneric_of_arms`, `stepInterpSoundGeneric_of_laws`: the per-step obligation from
  the command arms, and for the base-command engine from the `InterpObs` laws. -/

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp

open Imperative

public section

variable {P : PureExpr} {CmdT : Type}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-! ## Per-step soundness, and the whole-run reduction to it

`StepInterpSoundGeneric obs` is the per-step obligation; `runInterp_sound_generic` derives
`RunInterpSound` from it. -/

variable [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Ident]

/-- Per-step soundness over an abstract observation: from a successful `obs.run` of one `stepInterp`
    step at a non-terminal, non-exiting tracked configuration (`IConfig.Tracked`) whose stores
    denote under `F` (`IConfig.Denoting`), whose semantic image satisfies `Inv`, with `F`
    well-formed (`FactoryWF`) and the bounded evaluator sound up to denotation at `F`
    (`BoundedEvalSoundAt`), exhibit the single `StepStmtE` transition it realizes between the
    semantic images (with the trace extended by exactly its emitted runtime events, which denote
    the transition's events), and that the resulting configuration is tracked, denotes, and its
    image satisfies `Inv`. -/
def StepInterpSoundGeneric (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop) : Prop :=
  ∀ (F : P.Factory) (fuel : Nat) (cfg cfg' : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St),
    obs.run (stepInterp stepCmd fuel cfg) cfgr st = (.ok cfg', st') →
    (∀ e, cfg ≠ .terminal e) → (∀ l e, cfg ≠ .exiting l e) →
    FactoryWF (P := P) F → BoundedEvalSoundAt P F → cfg.Denoting F → Inv (cfg.abs F) →
    cfg.Tracked →
    (∃ revs : List (IEvent P), StepStmtE (P := P) EvalCmd (cfg.abs F) (revs.map (REvent.abs F))
        (cfg'.abs F) ∧ obs.trace st' = revs.reverse ++ obs.trace st) ∧
      cfg'.Denoting F ∧ Inv (cfg'.abs F) ∧ cfg'.Tracked

/-- **Whole-run soundness from a tracked configuration, given the per-step obligation.**  For
    any observation `obs` satisfying `StepInterpSoundGeneric`, an interpreter run from a tracked
    configuration (`IConfig.Tracked`) whose stores denote under a well-formed factory `F` and
    whose image satisfies `Inv`, to `final`, is an execution of the reference event-trace
    semantics (`StepStmtStarE`) from the start's image to `final`'s image, carrying the
    denotations of exactly the emitted runtime trace; `final` denotes as well. -/
theorem runInterp_sound_tracked (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop)
    (hstep : StepInterpSoundGeneric obs stepCmd EvalCmd Inv) :
    ∀ (F : P.Factory) (fuel : Nat) (start final : IConfig P CmdT) (cfg : obs.Cfg)
      (st st' : obs.St),
      obs.run (runInterp stepCmd fuel start) cfg st = (.ok final, st') →
      FactoryWF (P := P) F → BoundedEvalSoundAt P F → start.Denoting F → Inv (start.abs F) →
        start.Tracked →
      ∃ revs : List (IEvent P), StepStmtStarE (P := P) EvalCmd (start.abs F)
          (revs.map (REvent.abs F)) (final.abs F)
        ∧ final.Denoting F ∧ final.Tracked ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro F fuel c _ _ s _ h hf hE hd hi ht
  fun_induction runInterp stepCmd fuel c generalizing s <;>
    simp only [InterpObs.run_pure, InterpObs.run_throw, InterpObs.run_bind, Prod.mk.injEq,
      Except.ok.injEq, reduceCtorEq, false_and] at h
  iterate 2
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .refl _, hd, ht, by simp⟩
  rename_i hterm hexit ih
  split at h <;> rename_i hs
  · obtain ⟨⟨revs, hstepE, htr⟩, hd', hinv, htr'⟩ :=
      hstep _ _ _ _ _ _ _ hs hterm hexit hf hE hd hi ht
    obtain ⟨revs2, hrest, hdf, htf, htr2⟩ := ih _ _ h hd' hinv htr'
    refine ⟨revs ++ revs2, ?_, hdf, htf, by simp [htr, htr2]⟩
    rw [List.map_append]
    exact .step _ _ _ _ _ hstepE hrest
  · simp at h

/-- **Monad-generic whole-run soundness, given the per-step obligation.**  For any
    observation `obs` satisfying `StepInterpSoundGeneric`, whole-run soundness
    (`RunInterpSound`) holds. -/
theorem runInterp_sound_generic (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop)
    (hstep : StepInterpSoundGeneric obs stepCmd EvalCmd Inv) :
    RunInterpSound P m obs stepCmd EvalCmd Inv := by
  intro _ F start istart final _ _ _ ⟨hd, ht, habs⟩ h hf hE hi
  subst habs
  obtain ⟨revs, hrun, hdf, htf, htr⟩ :=
    runInterp_sound_tracked obs stepCmd EvalCmd Inv hstep _ _ _ _ _ _ _ h hf hE hd hi ht
  exact ⟨_, revs, _, hrun, ⟨hdf, htf, rfl⟩, htr, rfl⟩

/-- **Per-step soundness for a step that throws.**  The dual of
    `StepInterpSoundGeneric` on the error branch: whatever runtime events a failing step
    emitted before throwing denote the events of a reference execution out of the step's own
    configuration's image. -/
def StepInterpErrSound (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop) : Prop :=
  ∀ (F : P.Factory) (fuel : Nat) (cfg : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St)
      (r : StopReason),
    obs.run (stepInterp stepCmd fuel cfg) cfgr st = (.error r, st') →
    (∀ e, cfg ≠ .terminal e) → (∀ l e, cfg ≠ .exiting l e) →
    FactoryWF (P := P) F → BoundedEvalSoundAt P F → cfg.Denoting F → Inv (cfg.abs F) →
    cfg.Tracked →
    ∃ (mid : Config P CmdT) (revs : List (IEvent P)), StepStmtStarE (P := P) EvalCmd (cfg.abs F)
        (revs.map (REvent.abs F)) mid
        ∧ obs.trace st' = revs.reverse ++ obs.trace st

/-- **Per-step soundness for a throwing step, into a parametric certificate.**  The
    generalization of `StepInterpErrSound`: instead of demanding a flat
    `StepStmtStarE` for a step's pre-throw events, it demands only that their denotations
    satisfy an instance-supplied `TraceSound`. -/
def StepInterpErrSoundInto (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (Inv : Config P CmdT → Prop)
    (TraceSound : P.Factory → Config P CmdT → List (Event P) → Prop) : Prop :=
  ∀ (F : P.Factory) (fuel : Nat) (cfg : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St)
      (r : StopReason),
    obs.run (stepInterp stepCmd fuel cfg) cfgr st = (.error r, st') →
    (∀ e, cfg ≠ .terminal e) → (∀ l e, cfg ≠ .exiting l e) →
    FactoryWF (P := P) F → BoundedEvalSoundAt P F → cfg.Denoting F → Inv (cfg.abs F) →
    cfg.Tracked →
    ∃ revs : List (IEvent P), TraceSound F (cfg.abs F) (revs.map (REvent.abs F))
      ∧ obs.trace st' = revs.reverse ++ obs.trace st

/-- **Whole-run soundness into a parametric certificate, any outcome.**  Suppose every
    successful engine step is sound (`StepInterpSoundGeneric`) and the events a throwing step
    emits satisfy an instance-supplied certificate `TraceSound` (`StepInterpErrSoundInto`).  If
    `TraceSound` holds of the trace of every reference execution (`hclean`) and is preserved by
    prepending one reference event step (`hstepThen`), then the denotations of the trace an
    interpreter run records from a tracked, denoting configuration whose image satisfies `Inv`,
    whether the run succeeds or throws, satisfy `TraceSound` at the start's image. -/
theorem runInterp_traceSound_generic (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop)
    (TraceSound : P.Factory → Config P CmdT → List (Event P) → Prop)
    (hclean : ∀ (F : P.Factory) (start : Config P CmdT) (evs : List (Event P))
        (mid : Config P CmdT),
        StepStmtStarE (P := P) EvalCmd start evs mid → TraceSound F start evs)
    (hstepThen : ∀ (F : P.Factory) (cfg : Config P CmdT) (evs : List (Event P))
        (cfg' : Config P CmdT) (rest : List (Event P)),
        StepStmtE (P := P) EvalCmd cfg evs cfg' → TraceSound F cfg' rest →
          TraceSound F cfg (evs ++ rest))
    (hstep : StepInterpSoundGeneric obs stepCmd EvalCmd Inv)
    (herr : StepInterpErrSoundInto obs stepCmd Inv TraceSound) :
    ∀ (F : P.Factory) (fuel : Nat) (start : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St)
        (res : Except StopReason (IConfig P CmdT)),
      obs.run (runInterp stepCmd fuel start) cfgr st = (res, st') →
      FactoryWF (P := P) F → BoundedEvalSoundAt P F → start.Denoting F → Inv (start.abs F) →
        start.Tracked →
      ∃ revs : List (IEvent P), TraceSound F (start.abs F) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro F fuel c _ s _ _ h hf hE hd hi ht
  fun_induction runInterp stepCmd fuel c generalizing s
  iterate 3 exact ⟨[], hclean _ _ _ _ (.refl _), by grind⟩
  rename_i hterm hexit ih
  rw [obs.run_bind] at h
  split at h <;> rename_i hs
  · obtain ⟨⟨revs, hstepE, htr⟩, hd', hinv, htr'⟩ :=
      hstep _ _ _ _ _ _ _ hs hterm hexit hf hE hd hi ht
    obtain ⟨rest, hr, htr2⟩ := ih _ _ h hd' hinv htr'
    refine ⟨revs ++ rest, ?_, by simp [*]⟩
    rw [List.map_append]
    exact hstepThen _ _ _ _ _ hstepE hr
  · cases h
    exact herr _ _ _ _ _ _ _ hs hterm hexit hf hE hd hi ht

/-- When every successful engine step is sound (`StepInterpSoundGeneric`) and every throwing step is
    sound (`StepInterpErrSound`), the denotations of the trace an interpreter run records from a
    tracked, denoting configuration `start` whose image satisfies `Inv`, whether the run succeeds
    or throws, are the trace of a reference execution from `start`'s image. -/
theorem runInterp_trace_sound_generic (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop)
    (hstep : StepInterpSoundGeneric obs stepCmd EvalCmd Inv)
    (herr : StepInterpErrSound obs stepCmd EvalCmd Inv) :
    ∀ (F : P.Factory) (fuel : Nat) (start : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St)
        (res : Except StopReason (IConfig P CmdT)),
      obs.run (runInterp stepCmd fuel start) cfgr st = (res, st') →
      FactoryWF (P := P) F → BoundedEvalSoundAt P F → start.Denoting F → Inv (start.abs F) →
        start.Tracked →
      ∃ (mid : Config P CmdT) (revs : List (IEvent P)), StepStmtStarE (P := P) EvalCmd (start.abs F)
          (revs.map (REvent.abs F)) mid
          ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro _ _ _ _ _ _ _ hrun hf hE hd hinv htk
  obtain ⟨revs, ⟨mid, hstar⟩, htr⟩ := runInterp_traceSound_generic obs _ _ _
    (fun _ c evs => ∃ m, StepStmtStarE P EvalCmd c evs m) (fun _ _ _ m => (⟨m, ·⟩))
    (fun _ _ _ _ _ h ⟨m, r⟩ => ⟨m, .step _ _ _ _ _ h r⟩) hstep
    (fun _ _ _ _ _ _ _ h a b c d e g i => (herr _ _ _ _ _ _ _ h a b c d e g i).elim
      fun mid ⟨revs, hs, ht⟩ => ⟨revs, ⟨mid, hs⟩, ht⟩)
    _ _ _ _ _ _ _ hrun hf hE hd hinv htk
  exact ⟨mid, revs, hstar, htr⟩

/-! ## Per-step soundness, proved once from the `InterpObs` laws

`StepInterpSoundGeneric` for every observation satisfying the `InterpObs` laws. The base-command
arm runs on typed stores (`Config.storeTyped`), with the engine's executable value checks tied to
the reference's typed-value premises by `[InterpLangTyped P]`. -/

section StepGeneric

variable {P : PureExpr} {m : Type → Type} {CmdT : Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr]
    [DecidableEq P.Ident] [InterpLang P] [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]

/-! ### Base-command inversions -/

omit [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- On a runtime store that denotes under `F`, a runtime value the bounded evaluator commits for
    `e` denotes the `P.eval` value of `e` on the store's image, when the evaluator is sound up to
    denotation at `F` (`BoundedEvalSoundAt`). -/
theorem BoundedEvalSoundAt.atAbs {F : P.Factory} (hEval : BoundedEvalSoundAt P F)
    {σr : RStore P} (hd : RStore.Denoting F σr) {n : Nat} {e r : P.Expr}
    (h : InterpLang.boundedEval (P := P) n (InterpLang.rfactory F) σr e = some r) :
    ∃ v, P.eval F (InterpLang.absStore F σr) e = some v ∧ InterpLang.Denotes F r v :=
  hEval n σr _ e r (storeDenotes_absStore hd) h

omit [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- The runtime events a base command emits denote the events it emits on the image of its
    store. -/
theorem Cmd.rEmittedEvents_abs (F : P.Factory) (c : Cmd P) (σr : RStore P) :
    (Cmd.rEmittedEvents (P := P) c (InterpLang.rfactory F) σr).map (REvent.abs F)
      = Cmd.emittedEvents (P := P) c F (InterpLang.absStore F σr) := by
  cases c <;> rfl

omit [HasBoolOps P] [HasFvars P] [LawfulMonad m] in
/-- **Base-command step soundness, generically**: when the bounded evaluator is sound up to
    denotation, a successful `obs.run` of one `stepBaseCmdStore` from a runtime store that denotes
    under `F` and whose image is typed is a reference command evaluation (`EvalCmdE`) between the
    images, carrying the denotations of exactly the runtime events it emitted, and the resulting
    store denotes.  The typed-value premises of the reference `init`/`set` rules come from the
    engine's executable checks through `InterpLangTyped`; the `set` rules additionally read the
    old value's type off the typed image `hσ`. -/
theorem obs_stepBaseCmdStore_sound [InterpLangTyped P] (obs : InterpObs P m)
    (fuel : Nat) (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (store : IStore P) (cmd : Cmd P)
    (cfgr : obs.Cfg) (st st' : obs.St) (store' : IStore P)
    (hwfVar : WellFormedSemanticEvalVar (P := P) F)
    (hd : RStore.Denoting F store.get)
    (hσ : StoreTyped F (InterpLang.absStore F store.get))
    (h : obs.run (stepBaseCmdStore (m := m) fuel (InterpLang.rfactory F) store cmd) cfgr st
      = (.ok store', st')) :
    ∃ revs : List (IEvent P), EvalCmdE (P := P) F (InterpLang.absStore F store.get) cmd
        (InterpLang.absStore F store'.get) (revs.map (REvent.abs F))
      ∧ RStore.Denoting F store'.get ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  have hTyped := (‹InterpLangTyped P›).ops_typed
  have hnone : ∀ x, store.get x = none → InterpLang.absStore F store.get x = none :=
    fun x hx => by simp [InterpLang.absStore, hx]
  have hsome : ∀ x old, store.get x = some old →
      ∃ vo, InterpLang.absStore F store.get x = some vo ∧ InterpLang.denote F old = some vo :=
    fun x old hx => (hd x old hx).elim fun vo hvo =>
      ⟨vo, by simpa [InterpLang.absStore, hx, InterpLang.Denotes] using hvo, hvo⟩
  rcases cmd with ⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _ <;>
    (repeat' (first
      | split at h
      | simp only [stepBaseCmdStore, Bool.and_eq_true, List.forM_eq_forM,
          InterpObs.run_bind, InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq,
          Except.ok.injEq, reduceCtorEq, false_and] at h))
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rename_i hnd _ v hb hchk
    obtain ⟨w, hw, hdw⟩ := hEval.atAbs hd hb
    obtain ⟨w', hdw', hty⟩ := hTyped.hasType F v _ hchk.1 hchk.2
    cases Option.some.inj (hdw'.symm.trans hdw)
    refine ⟨[], ?_, by rw [IStore.get_update]; exact hd.update _ hdw, by simp⟩
    rw [IStore.get_update, InterpLang.absStore_update _ _ hdw]
    exact .eval_init hw (InitState.of_update (hnone _ (by simpa using hnd))) hty hwfVar
  · rename_i hnd _ r _ hc
    obtain ⟨⟨hv, ht⟩, htr⟩ := obs.choose_sound _ _ _ _ _ _ _ hc
    obtain ⟨w, hdw, hty⟩ := hTyped.hasType F r _ hv ht
    refine ⟨[], ?_, by rw [IStore.get_update]; exact hd.update _ hdw, by simpa using htr⟩
    rw [IStore.get_update, InterpLang.absStore_update _ _ hdw]
    exact .eval_init_unconstrained (InitState.of_update (hnone _ (by simpa using hnd))) hty hwfVar
  · rename_i _ old hold _ v hb hchk
    obtain ⟨vo, habs, hdo⟩ := hsome _ _ hold
    obtain ⟨w, hw, hdw⟩ := hEval.atAbs hd hb
    obtain ⟨w', hdw', hst⟩ := hTyped.storedTy hσ habs hdo hchk.1 hchk.2
    cases Option.some.inj (hdw'.symm.trans hdw)
    refine ⟨[], ?_, by rw [IStore.get_update]; exact hd.update _ hdw, by simp⟩
    rw [IStore.get_update, InterpLang.absStore_update _ _ hdw]
    exact .eval_set hw (UpdateState.of_update habs) hst hwfVar
  · rename_i _ old hold _ _ _ _ r _ hc hchk
    obtain ⟨vo, habs, hdo⟩ := hsome _ _ hold
    obtain ⟨-, htr⟩ := obs.choose_sound _ _ _ _ _ _ _ hc
    obtain ⟨w, hdw, hst⟩ := hTyped.storedTy hσ habs hdo hchk.1 hchk.2
    refine ⟨[], ?_, by rw [IStore.get_update]; exact hd.update _ hdw, by simpa using htr⟩
    rw [IStore.get_update, InterpLang.absStore_update _ _ hdw]
    exact .eval_set_nondet (UpdateState.of_update habs) hst hwfVar
  all_goals rename_i hrun
  all_goals refine ⟨_, ?_, hd, obs_forM_emit _ _ _ _ _ _ hrun⟩
  all_goals rw [Cmd.rEmittedEvents_abs]
  all_goals constructor

omit [HasBoolOps P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] in
/-- A reference base-command evaluation (`EvalCmdE`) defines only the binder of an `init`. -/
theorem evalCmdE_cmdDefsSound : CmdDefsSound (@EvalCmdE P _ _) := by
  intro _ _ c _ _ h x hx
  cases h <;> simp only [CmdDefs.defs, Cmd.definedVars, List.mem_cons, List.not_mem_nil,
    or_false]
  all_goals first
    | exact .inl hx
    | grind [cases InitState, cases UpdateState, Option.isSome_iff_exists]

/-! ### Per-step soundness, assembled -/

/-! #### Per-step soundness with the command arms as parameters

The statement-level arms of a `stepInterp` step are sound for an arbitrary stepper, command
relation and carried invariant `Inv`, given the command arm `hcmdarm`. `Inv` is only a
precondition; re-establishing it on the
successor is left to each instance. -/

omit [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
  [InterpLang P] in
/-- `j` sequence contexts with no remaining statements under `k` more are `k + j` of them. -/
private theorem Config.wrapSeqs_add (c : Config P CmdT) (j k : Nat) :
    (c.wrapSeqs j).wrapSeqs k = c.wrapSeqs (k + j) := by
  induction k <;> simp_all [Config.wrapSeqs, Nat.succ_add]

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- On a denoting runtime store, a runtime guard value the bounded evaluator commits that is the
    literal `HasBool.tt` (respectively `HasBool.ff`) up to metadata (`InterpLang.boolLit?`)
    denotes `ttVal F` (`ffVal F`), the value of `P.eval` on the image. -/
theorem BoundedEvalSoundAt.guard [InterpLangBool P] {F : P.Factory}
    (hEval : BoundedEvalSoundAt P F) {σr : RStore P} (hd : RStore.Denoting F σr) {n : Nat}
    {c r : P.Expr} (hb : InterpLang.boundedEval (P := P) n (InterpLang.rfactory F) σr c = some r) :
    (InterpLang.boolLit? r = some true →
      P.eval F (InterpLang.absStore F σr) c = some (HasBool.ttVal F)) ∧
    (InterpLang.boolLit? r = some false →
      P.eval F (InterpLang.absStore F σr) c = some (HasBool.ffVal F)) := by
  obtain ⟨v, hv, hden⟩ := hEval.atAbs hd hb
  exact ⟨fun hl => hv.trans (congrArg some (InterpLang.denote_of_boolLit? hl hden)),
    fun hl => hv.trans (congrArg some (InterpLang.denote_of_boolLit? hl hden))⟩

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [LawfulMonad m] in
/-- A successful run of `resolveGuard` from a denoting environment leaves the trace unchanged,
    and a deterministic guard it resolves to `true` (respectively `false`) evaluates under
    `P.eval` on the image to `ttVal F` (`ffVal F`). -/
private theorem obs_resolveGuard_sound [InterpLangBool P] (obs : InterpObs P m) {F : P.Factory}
    (hEval : BoundedEvalSoundAt P F) {env : IEnv P} (hds : RStore.Denoting F env.store.get)
    (hfac : env.factory = InterpLang.rfactory F) {fuel : Nat} {g : ExprOrNondet P}
    {cfgr : obs.Cfg} {st st' : obs.St} {b : Bool}
    (h : obs.run (resolveGuard fuel env g) cfgr st = (.ok b, st')) :
    obs.trace st' = obs.trace st ∧ ∀ c, g = .det c →
      P.eval F (InterpLang.absStore F env.store.get) c =
        some (if b then HasBool.ttVal F else HasBool.ffVal F) := by
  cases g with
  | det c =>
    simp only [resolveGuard] at h
    split at h
    · rename_i r hr
      have hg := hEval.guard hds (hfac ▸ hr)
      split at h <;> simp only [InterpObs.run_pure, InterpObs.branch_stuck, Prod.mk.injEq,
        Except.ok.injEq, reduceCtorEq, false_and] at h
      all_goals obtain ⟨rfl, rfl⟩ := h
      · exact ⟨rfl, fun _ hc => by cases hc; exact hg.1 ‹_›⟩
      · exact ⟨rfl, fun _ hc => by cases hc; exact hg.2 ‹_›⟩
    · simp only [InterpObs.run_throw, Prod.mk.injEq, reduceCtorEq, false_and] at h
  | nondet =>
    simp only [resolveGuard, InterpObs.run_bind] at h
    split at h
    · rename_i hc
      refine ⟨?_, nofun⟩
      split at h <;> simp only [InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq,
        Except.ok.injEq, reduceCtorEq, false_and] at h
      all_goals obtain ⟨-, rfl⟩ := h
      all_goals exact (obs.choose_sound _ _ _ _ _ _ _ hc).2
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h

omit [LawfulMonad m] in
/-- Per-step soundness (`StepInterpSoundGeneric`) for an arbitrary stepper, command relation and
    invariant `Inv`, given that a successful `stepInterp` step of a `.cmd` statement from a
    denoting configuration whose image satisfies `Inv`, under a well-formed factory, is one
    reference `StepStmtE` step recording the denotations of exactly its runtime events and ends
    in a denoting configuration when the bounded evaluator is sound up to denotation at the
    factory (`hcmdarm`), that `Inv` projects into the inner configuration of a `.seq`/`.block`
    (`hseq`, `hblk`) and is preserved by every reference step (`hInvStep`), and that every command
    evaluation defines only the names `CmdDefs` lists (`hdefs`), which keeps the frames exact. -/
theorem stepInterpSoundGeneric_of_arms [InterpLangBool P] [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop)
    (hseq : ∀ (inner : Config P CmdT) (ss : List (Stmt P CmdT)), Inv (.seq inner ss) → Inv inner)
    (hblk : ∀ (l : Option String) (σ : SemanticStore P) (inner : Config P CmdT),
        Inv (.block l σ inner) → Inv inner)
    (hcmdarm : ∀ (F : P.Factory) (fuel : Nat) (cmd : CmdT) (env : IEnv P)
        (cfg' : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepInterp stepCmd fuel (.stmt (.cmd cmd) env)) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → BoundedEvalSoundAt P F →
        (IConfig.stmt (.cmd cmd) env).Denoting F → Inv (.stmt (.cmd cmd) (env.abs F)) →
        (∃ revs : List (IEvent P), StepStmtE (P := P) EvalCmd (.stmt (.cmd cmd) (env.abs F))
          (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st) ∧ cfg'.Denoting F)
    (hInvStep : ∀ (c c' : Config P CmdT) (evs : List (Event P)),
        StepStmtE (P := P) EvalCmd c evs c' → Inv c → Inv c')
    (hdefs : CmdDefsSound EvalCmd) :
    StepInterpSoundGeneric obs stepCmd EvalCmd Inv := by
  intro F
  suffices h : BoundedEvalSoundAt P F →
      ∀ (fuel : Nat) (cfg cfg' : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (stepInterp stepCmd fuel cfg) cfgr st = (.ok cfg', st') →
      (∀ e, cfg ≠ .terminal e) → (∀ l e, cfg ≠ .exiting l e) →
      FactoryWF (P := P) F → cfg.Denoting F → Inv (cfg.abs F) → cfg.Tracked →
      (∃ revs : List (IEvent P), StepStmtE (P := P) EvalCmd (cfg.abs F) (revs.map (REvent.abs F))
        (cfg'.abs F) ∧ obs.trace st' = revs.reverse ++ obs.trace st) ∧
        cfg'.Denoting F ∧ cfg'.Tracked by
    intro _ _ _ _ _ _ hr hnt hne hf hEval hd hi ht
    obtain ⟨⟨revs, hs, htr⟩, hd', ht'⟩ := h hEval _ _ _ _ _ _ hr hnt hne hf hd hi ht
    exact ⟨⟨revs, hs, htr⟩, hd', hInvStep _ _ _ hs hi, ht'⟩
  intro hEval fuel c
  induction c with
  | stmt s env =>
    intro c' cfgr st st' hr _ _ hf hd hi _
    cases s with
    | cmd cmd =>
      obtain ⟨⟨revs, hs, htr⟩, hd'⟩ := hcmdarm _ _ _ _ _ _ _ _ hr hf hEval hd hi
      obtain ⟨ρ', hρ'⟩ := hs.cmd_terminal
      obtain ⟨_, rfl, -⟩ := (IConfig.abs_eq_terminal _ _ _).1 hρ'
      exact ⟨⟨revs, hs, htr⟩, hd', trivial⟩
    | _ =>
      obtain ⟨hds, hfac⟩ := hd
      (try cases ‹ExprOrNondet _›) <;> simp only [stepInterp, InterpObs.run_bind] at hr
      all_goals first
        | (split at hr
           rename_i b st1 hrg
           obtain ⟨htr, hev⟩ := obs_resolveGuard_sound obs hEval hds hfac hrg
           cases b)
        | skip
      all_goals (repeat' (first
        | split at hr
        | simp only [InterpObs.run_pure, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq,
            false_and] at hr))
      all_goals (try obtain ⟨rfl, rfl⟩ := hr)
      all_goals (try subst_vars)
      all_goals refine ⟨⟨[], ?_, ?_⟩, ?_, ?_⟩
      all_goals (try simp only [IConfig.abs, IEnv.abs, ScopeFrame.opened, IConfig.Denoting,
        IConfig.Tracked, IConfig.lvl])
      all_goals first
        | (constructor <;> exact hev _ rfl)
        | (simp; done)
        | simpa using htr
        | exact ⟨hds, hds, hfac⟩
        | exact ⟨⟨hds, hds, hfac⟩, by simpa using hds⟩
        | exact ⟨hds, hfac⟩
        | (simp [ScopeFrame.Exact]; done)
        | trivial
  | stmts ss env =>
    intro c' cfgr st st' hr _ _ _ hd _ _
    rcases ss with _ | ⟨_, _ | _⟩ <;> simp only [stepInterp, InterpObs.run_pure] at hr
    all_goals cases hr
    all_goals exact ⟨⟨[], (by constructor), by simp⟩, hd, trivial⟩
  | terminal => exact fun _ _ _ _ _ hnt => (hnt _ rfl).elim
  | exiting => exact fun _ _ _ _ _ _ hne => (hne _ _ rfl).elim
  | seq inner ss ih =>
    intro c' cfgr st st' hr hnt hne hf hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> simp only [stepInterp, InterpObs.run_pure] at hr
      all_goals cases hr
      all_goals exact ⟨⟨[], (by constructor), by simp⟩, hd, trivial⟩
    · simp only [not_or, not_exists] at hdone
      simp only [stepInterp_seq_unfold_gen _ _ _ _ hdone.1 hdone.2, InterpObs.run_bind,
        InterpObs.run_pure] at hr
      split at hr <;> cases hr
      obtain ⟨⟨evs, hs, htr⟩, hd', ht'⟩ :=
        ih _ _ _ _ ‹_› hdone.1 hdone.2 hf hd (hseq _ _ hi) ht
      exact ⟨⟨evs, .step_seq_inner hs, htr⟩, hd', ht'⟩
  | seqs inner k ih =>
    intro c' cfgr st st' hr hnt hne hf hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> cases k <;>
        simp only [stepInterp, InterpObs.run_pure] at hr
      all_goals cases hr
      all_goals refine ⟨⟨[], ?_, by simp⟩, hd, trivial⟩
      all_goals rw [IConfig.abs.eq_7, ← Config.wrapSeqs_add _ 1]
      all_goals exact StepStmtE.wrapSeqs (by constructor) _
    · simp only [not_or, not_exists] at hdone
      simp only [stepInterp] at hr
      split at hr
      · exact absurd rfl (hdone.1 _)
      · exact absurd rfl (hdone.2 _ _)
      simp only [InterpObs.run_bind] at hr
      split at hr <;> try simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hr
      have hi' : Inv (inner.abs F) := Nat.rec (motive := fun j => Inv ((inner.abs F).wrapSeqs j) → _)
        id (fun _ ihj h => ihj (hseq _ _ h)) (k + 1) hi
      obtain ⟨⟨evs, hs, htr⟩, hd', ht'⟩ := ih _ _ _ _ ‹_› hdone.1 hdone.2 hf hd hi' ht
      split at hr <;> simp only [InterpObs.run_pure, Prod.mk.injEq, Except.ok.injEq] at hr <;>
        obtain ⟨rfl, rfl⟩ := hr
      · rename_i c j _
        refine ⟨⟨evs, ?_, htr⟩, hd', ht'⟩
        show StepStmtE P EvalCmd _ _ ((c.abs F).wrapSeqs (j + k + 1 + 1))
        rw [show j + k + 1 + 1 = k + 1 + (j + 1) by omega, ← Config.wrapSeqs_add]
        exact hs.wrapSeqs _
      · exact ⟨⟨evs, hs.wrapSeqs _, htr⟩, hd', ht'⟩
  | block l fr inner ih =>
    intro c' cfgr st st' hr hnt hne hf hd hi ht
    obtain ⟨hex, hti⟩ := ht
    obtain ⟨hdp, hdi⟩ := hd
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l', e, rfl⟩ <;> simp only [IConfig.lvl] at hex <;>
        simp only [stepInterp] at hr
      all_goals (try split at hr) <;> simp only [InterpObs.run_pure] at hr
      all_goals cases hr
      all_goals refine ⟨⟨[], ?_, by simp⟩, ⟨?_, hdi.2⟩, trivial⟩
      all_goals first
        | (simp only [ScopeFrame.exit_eq hex]; exact hdi.1.project _)
        | simp only [IConfig.abs, IEnv.abs, ScopeFrame.exit_eq hex,
            InterpLang.absStore_project _ hdp]
      · exact .step_block_done
      · exact .step_block_exit_match ‹_›
      · exact .step_block_exit_mismatch ‹_›
    · simp only [not_or, not_exists] at hdone
      simp only [stepInterp_block_unfold_gen _ _ _ _ _ hdone.1 hdone.2, InterpObs.run_bind,
        InterpObs.run_pure] at hr
      split at hr <;> cases hr
      obtain ⟨⟨evs, hs, htr⟩, hd', ht'⟩ :=
        ih _ _ _ _ ‹_› hdone.1 hdone.2 hf hdi (hblk _ _ _ hi) hti
      refine ⟨⟨evs, ?_, htr⟩, ⟨by simpa using hdp, hd'⟩, ScopeFrame.record_exact hex ?_, ht'⟩
      · simp only [IConfig.abs, ScopeFrame.record_parent]
        exact .step_block_body hs
      · intro x hx
        have hl := StepStmtE.lvl_defines hdefs hs x
        simp only [IConfig.lvl_abs, IConfig.levelCmd?_abs, InterpLang.absStore_isSome hd'.lvl,
          InterpLang.absStore_isSome hdi.lvl] at hl
        exact hl hx

/-! ### The base-command instance -/

omit [LawfulMonad m] in
/-- Per-step soundness of the base-command engine (`baseStepCmd` against `EvalCmdE`) on typed
    stores (`Config.storeTyped`), for every observation. -/
theorem stepInterpSoundGeneric_of_laws [InterpLangTyped P] [InterpLangBool P]
    (obs : InterpObs P m) :
    StepInterpSoundGeneric obs (baseStepCmd (m := m)) (@EvalCmdE P _ _)
        (Config.storeTyped (P := P) (CmdT := Cmd P)) := by
  refine stepInterpSoundGeneric_of_arms obs _ (@EvalCmdE P _ _)
    (Config.storeTyped (P := P) (CmdT := Cmd P)) (fun _ _ hs => by exact hs)
    (fun _ _ _ hs => by exact hs.2) ?_ ?_ ?_
  · intro F _ _ env _ _ _ _ h hf hEval hd hst
    obtain ⟨hds, hfac⟩ := hd
    simp only [stepInterp_stmt_cmd, baseStepCmd, InterpObs.run_bind, InterpObs.run_pure] at h
    split at h <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i hrun
    rw [hfac] at hrun
    obtain ⟨revs, he, hd', ht⟩ :=
      obs_stepBaseCmdStore_sound obs _ _ hEval _ _ _ _ _ _ hf.2.1 hds hst hrun
    exact ⟨⟨revs, .step_cmd he, ht⟩, hd', hfac⟩
  · exact fun _ _ _ h => Config.storeTyped_stepE evalCmdE_storeTyped h
  · exact evalCmdE_cmdDefsSound

end StepGeneric

end -- public section

end Imperative
