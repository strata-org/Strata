/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.DL.Imperative.StmtSemanticsDeterminism
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemanticsDeterminismProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps
public import Strata.DL.Imperative.InterpreterConfigProps

/-! # Monad-generic engine completeness

The converse direction of `InterpreterSoundGeneric.lean`: a reference derivation
is *reproduced* by an engine run.  The development mirrors the soundness one —
a per-step obligation (`StepInterpCompleteGeneric`), discharged once from the
`InterpObs` laws, and a whole-run induction (`runInterp_complete_generic`) — but
the induction is over the **derivation**, not over fuel, because the fuel is an
output of completeness rather than an input.

## Which derivations an engine run can reproduce

Not every `StepStmtStarE` derivation of the reference semantics is reproducible, for
three independent reasons, none of which is about the monad:

1. **Stopping.**  `runInterp` stops only at a `.terminal`/`.exiting`
   configuration, so a run can only ever return such a configuration.  A
   reference derivation may end anywhere — `StepStmtStarE start [] start` holds by
   `ReflTransTrace.refl` for a non-terminal `start`.  Everything below therefore
   requires the derivation's final configuration to be *done* (`Config.Done`).
2. **Engine-side value checks.**  On `.init x ty (.det e)` the engine additionally
   demands `InterpLang.ops.isValue` and `InterpLang.ops.hasType f v ty`, and on
   `.set x (.det e)` `isValue` and `sameType f old v`; the reference constructors
   `EvalCmdE.eval_init`/`eval_set` demand neither.  A derivation of
   `init x : Bool := ⟨an integer literal⟩` exists in the reference and is rejected
   by the engine at every fuel and config.  `EvalCmdEngE` is the reference command
   relation *plus* those checks, and it is what completeness takes as input.
3. **Choice resolution.**  A nondeterministic rule requires the engine's `choose`
   to resolve the way the derivation did.  That is a property of the derivation,
   not of the monad — see `ChooseResolves`.

The relations these reasons lead to — `Config.Done`, `ChoiceRecord`, `EvalCmdEngE`,
`StepEngE`/`StepEngStarE`, `EngineChecksAgree`, `ValidChoices` — are declared next to
the contract `RunInterpComplete` that is stated against them.

## The two hypotheses on the observation

Neither is an `InterpObs` law; both are the completeness duals of laws that
soundness only needed in the guarded direction.

* `EmitTotalOn obs cfgr Q` — `emit` succeeds on every event satisfying `Q`.
  `InterpObs.emit_trace` is success-*guarded* because an instance's `emit` may throw
  instead of recording (Core's `EvalM` on an `assert` whose recorded condition does
  not reduce to a Boolean literal); completeness needs the event actually to be
  recorded, so it must assume the emit goes through.  The unrestricted form
  `EmitTotal` (`Q := fun _ => True`) is what `ReplayM` satisfies, its
  `emit` being an infallible state update; it is *unsatisfiable* for Core's `EvalM`,
  because `Event P` is a bare structure ranging over assertion events with an
  arbitrary recorded condition.  Restricting to the events a given derivation emits
  is what makes the hypothesis dischargeable there.
* `ChooseResolves obs cfgr F R` — under the reader config `cfgr`, `choose`
  resolves exactly as the choice record `R` says, without touching the trace.
  This is the dual of `InterpObs.choose_sound`, and it is stated *relative to the
  derivation* (through `R`) on purpose: the unconditional reading — "for every
  valid value some config makes `choose` produce it" — is false for Core's
  `EvalM`, whose `choose` always throws.  Relative to `R`, a derivation
  that resolves no choice (`R := fun _ _ _ _ => False`) imposes no requirement, and
  every observation satisfies it (`chooseResolves_bot`).  It is also false for
  `ReplayM` at any non-empty `R`, since `ReplayM`'s `choose` answers from the oracle
  tail in the state it is run from; completeness along a choice sequence therefore
  uses the state-dependent `ChooseFollows` instead, which threads the oracle
  explicitly.

## The evaluator facts

Each engine-realizable rule that evaluates an expression carries that `InterpLang.boundedEval`
reaches, at *some* fuel, a value denoting the reference value (`EngEval`, its `EngEvalReach`
part).  The hypothesis `hMono` (`BoundedEvalMono`: `boundedEval` is upward fuel-monotone) turns
this into an engine-side `boundedEval` fact at all sufficiently large fuel.  The theorems that
start from a bare reference derivation (`runInterp_complete_of_deterministic*`) take
`hEvalComplete` (`BoundedEvalComplete`: the global form of the reach fact, the converse of
`RunInterpSound`'s `hEval`) to make that derivation engine-realizable.

## Shape of the conclusions

Every per-step and whole-run statement below concludes

    ∃ f0 st', (∀ fuel, f0 ≤ fuel → obs.run … cfgr st = (.ok …, st')) ∧ obs.trace st' = …

— "succeeds at every sufficiently large fuel", not merely "at some fuel".  The
driver spends one fuel per step and passes the *remainder* to the next step, so a
whole-run induction cannot compose per-step results that hold at one fuel only;
carrying the upward-closure through the statement is what makes the induction
compose, and it subsumes a separate whole-run fuel-monotonicity lemma.

## Key definitions and theorems

* `EmitTotal`, `EmitTotalOn`, `ChooseResolves`, `ChooseFollows`: the hypotheses on the
  observation; `ChoiceRecord.bot`: the empty choice record, which every observation resolves
  (`chooseResolves_bot`); `chooseFollows_nil`: every observation follows the empty choice
  sequence;
  `obs_forM_emit_complete`: under `EmitTotal`, emitting a list of events succeeds and prepends
  exactly that list to the trace;
* `StepInterpCompleteGeneric`, `StepInterpCompleteParam`, `StepInterpCompleteFam`: the
  per-step obligations, for base commands, for an arbitrary stepper, and for a stepper family;
* `runInterp_complete_generic`, `runInterp_complete_param`, `runInterp_complete_fam`: whole-run
  completeness from the per-step obligation; `runInterp_complete_generic_of_agree`,
  `runInterp_complete_param_of_agree`: the same against the reference semantics, under
  `EngineAgreesFrom`;
* `obs_stepBaseCmdStore_complete`, `stepInterpCompleteFam_of_arms`: the per-step obligation
  discharged from the `InterpObs` laws;
* `OracleStepParamE`, `RunChoicesParam`, `CmdFollowsFam`: oracle-reading reference steps and
  the choice sequence of a run over any command type, and the per-command law along it;
  `runInterp_follows_prefix_fam`, `runInterp_complete_follows_fam`,
  `runInterp_complete_follows_param`: whole-run completeness along a choice sequence
  (`ChooseFollows`), for a stepper family and for one stepper;
* `OracleCmdEngE`, `oracleCmdEngE_follows`, `runInterp_complete_follows`: the base-command
  instance; `runChoicesParam_of_stepEngStarE`: every engine-realizable run has a choice sequence;
* `runInterp_complete_of_deterministic_from`, `runInterp_complete_of_deterministic`,
  `runInterp_complete_on_of_deterministic`: whole-run completeness for a syntactically
  deterministic program; `runInterp_complete_on_of_agree`: whole-run completeness on a class of
  events against the reference semantics, under `EngineAgreesFrom`. -/

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp

public section

universe u

/-! ## The hypotheses on the observation -/

section ObsHyp

variable {P : PureExpr} {m : Type → Type}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- **`emit` totality**: recording an event succeeds.  The completeness dual of the
success-guarded law `InterpObs.emit_trace`. -/
@[expose] def EmitTotal (obs : InterpObs P m) (cfgr : obs.Cfg) : Prop :=
  ∀ (ev : IEvent P) (st : obs.St),
    ∃ st', obs.run (InterpEffects.emit (P := P) ev) cfgr st = (.ok ⟨⟩, st')

/-- **`emit` totality on a class of events**: under the reader config `cfgr`, recording an
event that satisfies `Q` succeeds from every state.  `EmitTotal` is the `Q := fun _ => True`
case. -/
@[expose] def EmitTotalOn (obs : InterpObs P m) (cfgr : obs.Cfg) (Q : Event P → Prop) : Prop :=
  ∀ (F : P.Factory) (ev : IEvent P) (st : obs.St), Q (ev.abs F) →
    ∃ st', obs.run (InterpEffects.emit (P := P) ev) cfgr st = (.ok ⟨⟩, st')

/-- Unrestricted `emit` totality restricts to any event class. -/
private theorem EmitTotal.toOn {obs : InterpObs P m} {cfgr : obs.Cfg} (h : EmitTotal obs cfgr)
    (Q : Event P → Prop) : EmitTotalOn obs cfgr Q := by
  exact fun _ _ _ _ => h _ _

/-- **Emitting a list of events succeeds**: if `emit` always succeeds under `cfgr`, emitting
a list of events succeeds from every state and prepends exactly that list (reversed) to the
trace.  The completeness dual of `obs_forM_emit`. -/
theorem obs_forM_emit_complete (obs : InterpObs P m) (cfgr : obs.Cfg)
    (hemit : EmitTotal obs cfgr) :
    ∀ (evs : List (IEvent P)) (st : obs.St),
      ∃ st', obs.run (evs.forM (InterpEffects.emit (P := P))) cfgr st = (.ok ⟨⟩, st')
        ∧ obs.trace st' = evs.reverse ++ obs.trace st := by
  intro evs
  induction evs <;> intro st <;>
    simp_all only [List.forM_eq_forM, List.forM_nil, List.forM_cons, InterpObs.run_pure,
      InterpObs.run_bind, Prod.mk.injEq, true_and, List.reverse_nil, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append, exists_eq_left']
  rename_i ih
  have ⟨s1, h1⟩ := hemit ‹_› st
  grind [ih s1]

/-- **Choice resolution, relative to a derivation.**  Under the reader config
`cfgr`, `choose` produces exactly the value the choice record `R` prescribes, and
leaves the trace alone.  The completeness dual of `InterpObs.choose_sound`. -/
@[expose] def ChooseResolves (obs : InterpObs P m) (cfgr : obs.Cfg) (f : P.Factory)
    (R : ChoiceRecord P) : Prop :=
  ∀ (σr : RStore P) (σ : SemanticStore P) (ty : P.Ty) (v : P.Val)
    (st : obs.St),
    StoreDenotes f σr σ → R f σ ty v →
    ∃ r st', obs.run (InterpEffects.choose (P := P) (InterpLang.rfactory f) σr ty) cfgr st
               = (.ok r, st')
             ∧ InterpLang.Denotes f r v
             ∧ (v = HasBool.ttVal f → InterpLang.boolLit? r = some true)
             ∧ (v = HasBool.ffVal f → InterpLang.boolLit? r = some false)
             ∧ obs.trace st' = obs.trace st

/-- The empty choice record. -/
@[expose] def ChoiceRecord.bot (P : PureExpr) : ChoiceRecord P := fun _ _ _ _ => False

/-- **Choice resolution is free for a choice-free derivation.**  Every observation resolves
the empty choice record, at every reader config: a record that prescribes no value puts no
requirement on `choose`. -/
theorem chooseResolves_bot (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory} :
    ChooseResolves obs cfgr F (ChoiceRecord.bot P) := nofun

/-- **Choice resolution along a choice sequence.**  `Pending st cs` says that a run from the
state `st` resolves its next choices as `cs`.  Under the reader config `cfgr`, `choose` from a
state with `Pending st (v :: cs)` returns `v` when `R` allows it, leaves the trace alone and
leaves `Pending st' cs`; a successful `emit` keeps `Pending`.  The state-dependent counterpart
of `ChooseResolves`. -/
structure ChooseFollows (obs : InterpObs P m) (cfgr : obs.Cfg) (f : P.Factory) (R : ChoiceRecord P)
    (Pending : obs.St → List P.Val → Prop) : Prop where
  /-- `choose` returns a runtime value denoting the next pending choice and pops it. -/
  choose : ∀ (σr : RStore P) (σ : SemanticStore P) (ty : P.Ty) (v : P.Val)
    (cs : List P.Val) (st : obs.St), StoreDenotes f σr σ → Pending st (v :: cs) → R f σ ty v →
    ∃ r st', obs.run (InterpEffects.choose (P := P) (InterpLang.rfactory f) σr ty) cfgr st
        = (.ok r, st')
      ∧ InterpLang.Denotes f r v
      ∧ (v = HasBool.ttVal f → InterpLang.boolLit? r = some true)
      ∧ (v = HasBool.ffVal f → InterpLang.boolLit? r = some false)
      ∧ obs.trace st' = obs.trace st ∧ Pending st' cs
  /-- A successful `emit` keeps the pending choices. -/
  emit : ∀ (ev : IEvent P) (cs : List P.Val) (st st' : obs.St) (u : Unit),
    obs.run (InterpEffects.emit (P := P) ev) cfgr st = (.ok u, st') → Pending st cs →
    Pending st' cs

/-- **No pending choice is free.**  Every observation follows the empty choice sequence. -/
theorem chooseFollows_nil (obs : InterpObs P m) (cfgr : obs.Cfg) (R : ChoiceRecord P) :
    ChooseFollows obs cfgr F R (fun _ cs => cs = []) := ⟨nofun, fun _ _ _ _ _ _ h => h⟩

end ObsHyp

/-! ## Per-step completeness, and the whole-run induction over the derivation -/

section Complete

variable {P : PureExpr} {m : Type → Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]

/-- **The per-step completeness obligation**, dual to `StepInterpSoundGeneric`:
every engine-realizable step out of the abstraction of a tracked configuration `cfg` is
performed by one `stepInterp` step, at every sufficiently large fuel, from every state, under the
reader config `cfgr`, reaching a tracked configuration that stands for the step's successor and
extending the trace by exactly the step's events. -/
def StepInterpCompleteGeneric (obs : InterpObs P m) (cfgr : obs.Cfg) (F : P.Factory)
    (R : ChoiceRecord P) : Prop :=
  ∀ (cfg : IConfig P (Cmd P)) (cfg' : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St),
    cfg.Tracked → cfg.Denoting F → StepEngE P R (cfg.abs F) evs cfg' →
    ∃ (f0 : Nat) (c' : IConfig P (Cmd P)) (st' : obs.St),
      (∀ fuel, f0 ≤ fuel →
        obs.run (stepInterp (baseStepCmd (m := m)) fuel cfg) cfgr st = (.ok c', st'))
      ∧ c'.abs F = cfg' ∧ c'.Denoting F ∧ c'.Tracked ∧ obs.TraceExt F st st' evs

/-- **The per-step completeness obligation on a class of events**: as
`StepInterpCompleteGeneric`, but only for steps all of whose emitted events satisfy
`Q`.  This is what an observation whose `emit` is partial (Core's `EvalM`) can
provide. -/
def StepInterpCompleteGenericOn (obs : InterpObs P m) (cfgr : obs.Cfg) (F : P.Factory)
    (R : ChoiceRecord P) (Q : Event P → Prop) : Prop :=
  ∀ (cfg : IConfig P (Cmd P)) (cfg' : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St),
    cfg.Tracked → cfg.Denoting F → StepEngE P R (cfg.abs F) evs cfg' →
    (∀ ev ∈ evs, Q ev) →
    ∃ (f0 : Nat) (c' : IConfig P (Cmd P)) (st' : obs.St),
      (∀ fuel, f0 ≤ fuel →
        obs.run (stepInterp (baseStepCmd (m := m)) fuel cfg) cfgr st = (.ok c', st'))
      ∧ c'.abs F = cfg' ∧ c'.Denoting F ∧ c'.Tracked ∧ obs.TraceExt F st st' evs

omit [LawfulMonad m] [HasBoolOps P] in
/-- The unrestricted per-step obligation restricts to any event class. -/
private theorem StepInterpCompleteGeneric.toOn {F : P.Factory} {obs : InterpObs P m} {cfgr : obs.Cfg}
    {R : ChoiceRecord P} (h : StepInterpCompleteGeneric obs cfgr F R) (Q : Event P → Prop) :
    StepInterpCompleteGenericOn obs cfgr F R Q := by
  exact fun a b c d e f g _ => h a b c d e f g

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] [LawfulMonad m] in
/-- An engine-realizable step does not leave a terminal or exiting configuration. -/
private theorem StepEngParamE.not_done' {CmdT : Type} {R : ChoiceRecord P}
    {EvalCmd : EvalCmdParamE P CmdT (Event P)} {c c' : Config P CmdT} {evs : List (Event P)}
    (h : StepEngParamE P R EvalCmd c evs c') :
    (∀ e, c ≠ .terminal e) ∧ (∀ l e, c ≠ .exiting l e) := by cases h <;> simp

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] [LawfulMonad m] in
/-- A reference run from `c` whose every step from a configuration it reaches is
    engine-realizable (`EngineAgreesFrom`) is an engine-realizable run with the same events. -/
private theorem StepStmtStarE.toStepEngParamStarE' {CmdT : Type} {R : ChoiceRecord P}
    {EvalCmd EvalCmdEng : EvalCmdParamE P CmdT (Event P)}
    {c c' : Config P CmdT} {evs : List (Event P)} (h : StepStmtStarE P EvalCmd c evs c')
    (hag : EngineAgreesFrom (P := P) R EvalCmd EvalCmdEng c) :
    StepEngParamStarE P R EvalCmdEng c evs c' := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hs _ ih =>
    exact .step _ _ _ _ _ (hag _ _ _ _ (.refl _) hs)
      (ih fun _ _ _ _ r => hag _ _ _ _ (.step _ _ _ _ _ hs r))

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] [LawfulMonad m] in
/-- An engine-realizable step is a reference step over any command relation containing its own,
    with the same events and successor. -/
private theorem StepEngParamE.toStepStmtE' {CmdT : Type} {R : ChoiceRecord P}
    {EvalCmdEng EvalCmd : EvalCmdParamE P CmdT (Event P)}
    (hcmd : ∀ f σ σ' cmd evs, EvalCmdEng f σ cmd σ' evs → EvalCmd f σ cmd σ' evs)
    {c c' : Config P CmdT} {evs : List (Event P)} (h : StepEngParamE P R EvalCmdEng c evs c') :
    StepStmtE P EvalCmd c evs c' := by
  induction h with
  | step_cmd h => exact .step_cmd (hcmd _ _ _ _ _ h)
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_block_body _ ih => exact .step_block_body ih
  | step_ite_nondet => split <;> constructor
  | step_loop_nondet => split <;> constructor
  | _ => constructor <;> assumption

omit [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- A name the semantic image of a denoting runtime store leaves undefined is undefined. -/
private theorem absStore_eq_none {F : P.Factory} {σ : RStore P} (hd : RStore.Denoting F σ)
    (x : P.Ident) (hx : InterpLang.absStore F σ x = none) : σ x = none := by
  simpa [hx] using (InterpLang.absStore_isSome hd x).symm

omit [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- A name bound in the semantic image of a runtime store is bound to a runtime value denoting
    its image value. -/
private theorem absStore_eq_some {F : P.Factory} {σ : RStore P} (x : P.Ident) (old : P.Val)
    (hx : InterpLang.absStore F σ x = some old) :
    ∃ ro, σ x = some ro ∧ InterpLang.Denotes F ro old := by
  simp only [InterpLang.absStore, Option.bind_eq_some_iff] at hx
  exact hx

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] [LawfulMonad m] in
/-- A state's trace extends itself by no events. -/
private theorem traceExt_nil (obs : InterpObs P m) (F : P.Factory) (st : obs.St) :
    obs.TraceExt F st st [] := ⟨[], rfl, rfl⟩

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] [LawfulMonad m] in
/-- A state whose trace is that of `st` extends `st`'s trace by no events. -/
private theorem traceExt_of_eq {obs : InterpObs P m} {F : P.Factory} {st st' : obs.St}
    (h : obs.trace st' = obs.trace st) : obs.TraceExt F st st' [] := ⟨[], rfl, h⟩

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] [LawfulMonad m] in
/-- A state whose trace is that of `st` with the runtime event `ev` prepended extends `st`'s
    trace by the event `ev` stands for. -/
private theorem traceExt_single {obs : InterpObs P m} {F : P.Factory} {st st' : obs.St}
    {ev : IEvent P} (h : obs.trace st' = ev :: obs.trace st) :
    obs.TraceExt F st st' [ev.abs F] := ⟨[ev], rfl, h⟩

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] [LawfulMonad m] in
/-- Trace extensions compose: extending by `e1` and then by `e2` extends by `e1 ++ e2`. -/
private theorem InterpObs.TraceExt.append {obs : InterpObs P m} {F : P.Factory}
    {st s s' : obs.St} {e1 e2 : List (Event P)} (h1 : obs.TraceExt F st s e1)
    (h2 : obs.TraceExt F s s' e2) : obs.TraceExt F st s' (e1 ++ e2) := by
  obtain ⟨r1, rfl, t1⟩ := h1
  obtain ⟨r2, rfl, t2⟩ := h2
  exact ⟨r1 ++ r2, by simp, by simp [t1, t2]⟩

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- `runInterp` returns a configuration standing for a terminal or exiting configuration
    unchanged, at every fuel. -/
private theorem runInterp_of_abs_done {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (fuel : Nat) {F : P.Factory} {c : IConfig P CmdT}
    (h : (c.abs F).Done) :
    runInterp stepCmd fuel c = pure c := by
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩
  · obtain ⟨_, rfl, -⟩ := (IConfig.abs_eq_terminal ..).1 h
    exact runInterp_terminal ..
  · obtain ⟨_, rfl, -⟩ := (IConfig.abs_eq_exiting ..).1 h
    exact runInterp_exiting ..

omit [LawfulMonad m] [HasBoolOps P] in
/-- Monad-generic whole-run completeness on a class of events: given the per-step obligation on the
    events satisfying `Q` (`StepInterpCompleteGenericOn`), every engine-realizable run from the
    abstraction of a tracked configuration `start`, ending in a configuration `final` the
    monadic interpreter stops at and emitting only events satisfying `Q`, is reproduced by
    `runInterp baseStepCmd` from `start` to a configuration denoting `final` at every sufficiently
    large fuel, from every state, prepending runtime events that stand for exactly the run's events
    to the trace. -/
private theorem runInterp_complete_on (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop}
    (hstep : StepInterpCompleteGenericOn obs cfgr F R Q) :
    ∀ (start : IConfig P (Cmd P)) (final : Config P (Cmd P))
      (evs : List (Event P)),
      start.Tracked → start.Denoting F →
      StepEngStarE P R (start.abs F) evs final →
      Config.Done final →
      (∀ ev ∈ evs, Q ev) →
      ∀ (st : obs.St),
      ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
        (∀ fuel, f0 ≤ fuel →
          obs.run (runInterp (baseStepCmd (m := m)) fuel start) cfgr st
            = (.ok final', st'))
        ∧ obs.TraceExt F st st' evs := by
  intro start _ _ ht hd h hdone
  generalize hx : start.abs F = x at h
  induction h generalizing start with
  | refl =>
    subst hx
    exact fun _ st => ⟨0, start, st, ⟨hd, ht, rfl⟩,
      fun _ _ => by simp [runInterp_of_abs_done _ _ hdone], traceExt_nil ..⟩
  | step _ _ _ _ _ hs _ ih =>
    subst hx
    intro hq st
    obtain ⟨hq1, hq2⟩ := List.forall_mem_append.1 hq
    obtain ⟨a, c1, s, h1, ha, hd1, ht1, t1⟩ := hstep _ _ _ st ht hd hs hq1
    obtain ⟨b, cf, s', hf, h2, t2⟩ := ih c1 ht1 hd1 hdone ha hq2 s
    refine ⟨a + b + 1, cf, s', hf, fun | 0, _ => by omega | k + 1, _ => ?_, t1.append t2⟩
    have hnd := IConfig.not_done_of_abs hs.not_done'
    rw [runInterp_succ_nonterminal _ _ _ hnd.1 hnd.2]
    simp [h1 (k + 1) (by omega), h2 k (by omega)]

omit [LawfulMonad m] [HasBoolOps P] in
/-- **Monad-generic whole-run completeness, given the per-step obligation.** If every
    engine-realizable base-command step is performed by one `stepInterp` step
    (`StepInterpCompleteGeneric`), then every engine-realizable run `StepEngStarE` from the
    abstraction of a tracked configuration `start`, ending in a configuration `final` the
    monadic interpreter stops at (`Config.Done`), is reproduced by `runInterp baseStepCmd` from
    `start` to a configuration denoting `final` at every sufficiently large fuel, from every state,
    prepending runtime events that stand for exactly the run's events to the trace. -/
theorem runInterp_complete_generic (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} (hstep : StepInterpCompleteGeneric obs cfgr F R) :
    ∀ (start : IConfig P (Cmd P)) (final : Config P (Cmd P))
      (evs : List (Event P)),
      start.Tracked → start.Denoting F →
      StepEngStarE P R (start.abs F) evs final →
      Config.Done final →
      ∀ (st : obs.St),
      ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
        (∀ fuel, f0 ≤ fuel →
          obs.run (runInterp (baseStepCmd (m := m)) fuel start) cfgr st
            = (.ok final', st'))
        ∧ obs.TraceExt F st st' evs := by
  intros
  apply runInterp_complete_on _ _ (hstep.toOn fun _ => True) <;> grind

omit [LawfulMonad m] [HasBoolOps P] in
/-- **Monad-generic whole-run completeness against the reference semantics.** Assume every
engine-realizable base-command step is performed by one `stepInterp` step
(`StepInterpCompleteGeneric`), and every reference step from a configuration a reference derivation
reaches from `start` is an engine-realizable step with the same events and successor
(`EngineAgreesFrom`). Then a reference derivation from `start` ending at a configuration the
monadic interpreter stops at is reproduced by an engine run from every configuration `istart`
denoting `start` to a configuration denoting `final`, at every sufficiently large fuel, from every
state, prepending runtime events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_generic_of_agree (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} (hstep : StepInterpCompleteGeneric obs cfgr F R)
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := P) R (@EvalCmdE P _ _)
      (EvalCmdEngE P R) start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
      start evs final)
    (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  exact runInterp_complete_generic _ _ hstep _ _ _ ht hd (hrun.toStepEngParamStarE' hag) hdone st

/-! ## The arm-parametric completeness obligation and whole-run completeness

The per-step completeness obligation and whole-run completeness over an arbitrary command
type, stepper and engine-realizable command relation. -/

/-- **The per-step completeness obligation for a *family* of steppers.**  Every
engine-realizable step out of `cfg` is performed by one `stepInterp (stepOf i j)` step,
from every state, with a threshold uniform in all three indices: the step succeeds at
every pair of stepper indices `i ≥ f0`, `j ≥ f0` and every driver fuel `fuel ≥ f0`.

The indices are separate because a stepper that executes a nested run bakes its
own indices into the inner stepper: a procedure-call arm at call-depth budget `i + 1` and
command fuel `j + 1` runs the callee body with the stepper at indices `i`, `j` and driver
fuel `j`, so the inner run's second stepper index and driver fuel move together while the
outer driver fuel does not, and the first index moves on its own.  A threshold uniform in all
three is what lets them be identified. -/
def StepInterpCompleteFam {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m) (cfgr : obs.Cfg) (F : P.Factory) (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P)) : Prop :=
  ∀ (cfg : IConfig P CmdT) (cfg' : Config P CmdT) (evs : List (Event P)) (st : obs.St),
    cfg.Tracked → cfg.Denoting F → StepEngParamE P R EvalCmd (cfg.abs F) evs cfg' →
    ∃ (f0 : Nat) (c' : IConfig P CmdT) (st' : obs.St),
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (stepInterp (stepOf i j) fuel cfg) cfgr st = (.ok c', st'))
      ∧ c'.abs F = cfg' ∧ c'.Denoting F ∧ c'.Tracked ∧ obs.TraceExt F st st' evs

omit [HasFvar P] [LawfulMonad m] [HasBoolOps P] in
/-- **Whole-run completeness for a family of steppers.**  If every engine-realizable step is
performed by one `stepInterp (stepOf i j)` step at every pair of stepper indices `i`, `j` and
fuel above a common threshold (`StepInterpCompleteFam`), then every engine-realizable run ending
at a configuration the driver stops at is reproduced by `runInterp (stepOf i j)` at every large
enough stepper indices `i`, `j` and fuel, from every state, with exactly the run's events
prepended to the trace.  The stepper indices stay fixed along the run while the driver fuel
decreases, and the conclusion is uniform in all three, so instantiating it at `j = fuel`
reproduces a run whose stepper is baked at its own fuel. -/
theorem runInterp_complete_fam {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {EvalCmd : EvalCmdParamE P CmdT (Event P)}
    (hstep : StepInterpCompleteFam obs stepOf cfgr F R EvalCmd) :
    ∀ (start : IConfig P CmdT) (final : Config P CmdT) (evs : List (Event P)),
      start.Tracked → start.Denoting F →
      StepEngParamStarE P R EvalCmd (start.abs F) evs final →
      Config.Done final →
      ∀ (st : obs.St),
      ∃ (f0 : Nat) (final' : IConfig P CmdT) (st' : obs.St), final'.Denotes F final ∧
        (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
          obs.run (runInterp (stepOf i j) fuel start) cfgr st = (.ok final', st'))
        ∧ obs.TraceExt F st st' evs := by
  intro start _ _ ht hd h hdone
  generalize hx : start.abs F = x at h
  induction h generalizing start with
  | refl =>
    subst hx
    exact fun st => ⟨0, start, st, ⟨hd, ht, rfl⟩,
      fun _ _ _ _ _ _ => by simp [runInterp_of_abs_done _ _ hdone], traceExt_nil ..⟩
  | step _ _ _ _ _ hs _ ih =>
    subst hx
    intro st
    obtain ⟨a, c1, s, h1, ha, hd1, ht1, t1⟩ := hstep _ _ _ st ht hd hs
    obtain ⟨b, cf, s', hf, h2, t2⟩ := ih c1 ht1 hd1 hdone ha s
    refine ⟨a + b + 1, cf, s', hf,
      fun | _, _, 0, _, _, _ => by omega | i, j, k + 1, _, _, _ => ?_, t1.append t2⟩
    have hnd := IConfig.not_done_of_abs hs.not_done'
    rw [runInterp_succ_nonterminal _ _ _ hnd.1 hnd.2]
    simp [h1 i j (k + 1) (by omega) (by omega) (by omega),
      h2 i j k (by omega) (by omega) (by omega)]

/-- **The per-step completeness obligation, arm-parametrically.**  Every
engine-realizable step out of `cfg` is performed by one `stepInterp stepCmd` step,
at every sufficiently large fuel, from every state. -/
def StepInterpCompleteParam {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepCmd : StepCmdM P CmdT m) (cfgr : obs.Cfg) (F : P.Factory) (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P)) : Prop :=
  ∀ (cfg : IConfig P CmdT) (cfg' : Config P CmdT) (evs : List (Event P)) (st : obs.St),
    cfg.Tracked → cfg.Denoting F → StepEngParamE P R EvalCmd (cfg.abs F) evs cfg' →
    ∃ (f0 : Nat) (c' : IConfig P CmdT) (st' : obs.St),
      (∀ fuel, f0 ≤ fuel →
        obs.run (stepInterp stepCmd fuel cfg) cfgr st = (.ok c', st'))
      ∧ c'.abs F = cfg' ∧ c'.Denoting F ∧ c'.Tracked ∧ obs.TraceExt F st st' evs

omit [HasFvar P] [LawfulMonad m] [HasBoolOps P] in
/-- **Whole-run completeness, arm-parametrically**: if every engine-realizable step is
    performed by one `stepInterp stepCmd` step at every sufficiently large fuel
    (`StepInterpCompleteParam`), then every engine-realizable run `StepEngParamStarE` ending in a
    configuration the driver stops at is reproduced by `runInterp stepCmd` at every sufficiently
    large fuel, from every start state, prepending runtime events that stand for exactly the run's
    events to the trace. -/
theorem runInterp_complete_param {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepCmd : StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {EvalCmd : EvalCmdParamE P CmdT (Event P)}
    (hstep : StepInterpCompleteParam obs stepCmd cfgr F R EvalCmd) :
    ∀ (start : IConfig P CmdT) (final : Config P CmdT) (evs : List (Event P)),
      start.Tracked → start.Denoting F →
      StepEngParamStarE P R EvalCmd (start.abs F) evs final →
      Config.Done final →
      ∀ (st : obs.St),
      ∃ (f0 : Nat) (final' : IConfig P CmdT) (st' : obs.St), final'.Denotes F final ∧
        (∀ fuel, f0 ≤ fuel →
          obs.run (runInterp stepCmd fuel start) cfgr st = (.ok final', st'))
        ∧ obs.TraceExt F st st' evs := by
  intro _ _ _ ht hd h hdone st
  have hfam : StepInterpCompleteFam obs (fun _ _ => stepCmd) cfgr F R EvalCmd :=
    fun _ _ _ st ht hd h => (hstep _ _ _ st ht hd h).imp fun _ ⟨c, s, a, b⟩ =>
      ⟨c, s, fun _ _ f _ _ => a f, b⟩
  exact (runInterp_complete_fam _ _ _ hfam _ _ _ ht hd h hdone st).imp
    fun _ ⟨c, s, hc, a, b⟩ => ⟨c, s, hc, fun f h => a f f f h h h, b⟩

omit [HasFvar P] [LawfulMonad m] [HasBoolOps P] in
/-- **Whole-run completeness against the reference semantics, arm-parametrically.**  Assume
    every engine-realizable step over `EvalCmdEng` is performed by one `stepInterp stepCmd` step
    at every sufficiently large fuel (`StepInterpCompleteParam`), and every reference step over
    `EvalCmd` from a configuration a reference derivation reaches from `start` is an
    engine-realizable step with the same events and successor (`EngineAgreesFrom`).  Then a
    reference derivation over `EvalCmd` from `start` ending at a configuration the driver stops
    at is reproduced by `runInterp stepCmd` from every configuration `istart` denoting `start` to a
    configuration denoting `final` at every sufficiently large fuel, from every state, prepending
    runtime events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_param_of_agree {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepCmd : StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {EvalCmd EvalCmdEng : EvalCmdParamE P CmdT (Event P)}
    (hstep : StepInterpCompleteParam obs stepCmd cfgr F R EvalCmdEng)
    (start final : Config P CmdT) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P CmdT) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := P) R EvalCmd EvalCmdEng start)
    (hrun : StepStmtStarE P EvalCmd start evs final) (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P CmdT) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp stepCmd fuel istart) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  exact runInterp_complete_param _ _ _ hstep _ _ _ ht hd (hrun.toStepEngParamStarE' hag) hdone st

/-! ### Per-step completeness, discharged once from the `InterpObs` laws

Each engine-realizable rule is performed by `stepInterp`, given `BoundedEvalMono`, `EmitTotal`
and `ChooseResolves`. -/

omit [HasBoolOps P] in
/-- An engine-realizable command evaluation whose events satisfy `Q` is performed by
    `stepBaseCmdStore` from a denoting runtime store at every sufficiently large fuel, from every
    state, reaching a denoting runtime store that stands for its store and prepending runtime events
    that stand for exactly its events to the trace, given that `emit` succeeds on the events
    satisfying `Q`, that `choose` resolves `R`, and that the bounded evaluator is fuel-monotone
    (the evaluation carries that some fuel reaches its values, `EngEval`). -/
private theorem obs_stepBaseCmdStore_complete_on (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitTotalOn obs cfgr Q) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    {σ : IStore P} {σ' : SemanticStore P} {cmd : Cmd P} {evs : Trace P}
    (hd : RStore.Denoting F σ.get)
    (h : EvalCmdEngE P R F (InterpLang.absStore F σ.get) cmd σ' evs) (hQ : ∀ ev ∈ evs, Q ev)
    (st : obs.St) :
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (stepBaseCmdStore (m := m) fuel (InterpLang.rfactory F) σ cmd) cfgr st
          = (.ok σi, st'))
      ∧ obs.TraceExt F st st' evs := by
  have hsd := storeDenotes_absStore hd
  have hn := absStore_eq_none hd
  have hs := @absStore_eq_some _ _ F σ.get
  cases h with
  | @eval_init _ _ _ _ _ x _ hx he hok =>
    obtain ⟨n, r, hb, hr⟩ := hok.1 σ.get _ hsd he
    obtain ⟨hv, ht⟩ := hok.2 σ.get n r hsd hb
    refine ⟨n, σ.update x r, st, by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr,
      fun k hk => ?_, traceExt_nil ..⟩
    simp [stepBaseCmdStore, hn _ hx, hMono _ _ _ _ _ _ hk hb, hv, ht]
  | @eval_set _ _ _ _ x _ _ hx he hok =>
    obtain ⟨ro, hro, -⟩ := hs _ _ hx
    obtain ⟨n, r, hb, hr⟩ := hok.1 σ.get _ hsd he
    obtain ⟨hv, ht⟩ := hok.2 σ.get n r hsd hb ro hro
    refine ⟨n, σ.update x r, st, by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr,
      fun k hk => ?_, traceExt_nil ..⟩
    simp [stepBaseCmdStore, hro, hMono _ _ _ _ _ _ hk hb, hv, ht]
  | @eval_init_nondet _ _ _ _ x _ hx hR =>
    obtain ⟨r, s, h1, hr, -, -, h2⟩ := hchoose σ.get _ _ _ st hsd hR
    refine ⟨0, σ.update x r, s, by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr,
      fun k hk => ?_, traceExt_of_eq h2⟩
    simp [stepBaseCmdStore, hn _ hx, h1]
  | @eval_set_nondet _ _ x _ _ _ _ hx hty hR _ hok =>
    obtain ⟨ro, hro, -⟩ := hs _ _ hx
    obtain ⟨r, s, h1, hr, -, -, h2⟩ := hchoose σ.get _ _ _ st hsd hR
    obtain ⟨hv, ht⟩ := hok σ.get ro r hsd hro hr
    refine ⟨0, σ.update x r, s, by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr,
      fun k hk => ?_, traceExt_of_eq h2⟩
    simp [stepBaseCmdStore, hro, hty σ.get ro hsd hro, h1, hv, ht]
  | _ =>
    obtain ⟨s, h1⟩ := (by first
      | exact hemit F (.assert ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st (hQ _ (.head _))
      | exact hemit F (.assume ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st (hQ _ (.head _))
      | exact hemit F (.cover ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st (hQ _ (.head _)))
    exact ⟨0, σ, s, rfl, hd, fun _ _ => by simp [*, Cmd.rEmittedEvents],
      traceExt_single (obs.emit_trace _ _ _ _ _ h1)⟩

omit [HasBoolOps P] in
/-- **Base-command completeness, generically**: for an observation whose `emit` always succeeds and
    whose `choose` resolves `R`, and a fuel-monotone bounded evaluator, every engine-realizable
    command evaluation
    `EvalCmdEngE P R F σ cmd σ' evs` from the semantic image `σ` of a denoting runtime store is
    performed by `stepBaseCmdStore` at every sufficiently large fuel, from every state, reaching a
    denoting runtime store that stands for `σ'` and prepending runtime events that stand for exactly
    `evs` to the trace. -/
theorem obs_stepBaseCmdStore_complete (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    {σ : IStore P} {σ' : SemanticStore P} {cmd : Cmd P} {evs : Trace P}
    (hd : RStore.Denoting F σ.get)
    (h : EvalCmdEngE P R F (InterpLang.absStore F σ.get) cmd σ' evs) (st : obs.St) :
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (stepBaseCmdStore (m := m) fuel (InterpLang.rfactory F) σ cmd) cfgr st
          = (.ok σi, st'))
      ∧ obs.TraceExt F st st' evs := by
  apply obs_stepBaseCmdStore_complete_on _ _ (hemit.toOn fun _ => True) hchoose <;> grind

omit [HasBoolOps P] [HasFvar P] in
/-- A sequence tower `.seqs c k` has a configuration standing for `c` under `k` contexts
    `.seq · []`, tracked exactly when `c` is, whose interpreter step, put under one more such
    context, is the step of the tower, whenever `c` under `k` contexts is neither terminal nor
    exiting. -/
private theorem IConfig.seqs_peel {CmdT : Type} [CmdDefs P CmdT] (F : P.Factory)
    (c : IConfig P CmdT) (k : Nat) :
    ∃ c0 : IConfig P CmdT, c0.abs F = (c.abs F).wrapSeqs k ∧ c0.Tracked = c.Tracked ∧
      c0.Denoting F = c.Denoting F ∧
      ∀ (stepCmd : StepCmdM P CmdT m) (fuel : Nat),
        ((∀ e, (c.abs F).wrapSeqs k ≠ .terminal e) ∧
          (∀ l e, (c.abs F).wrapSeqs k ≠ .exiting l e)) →
        stepInterp stepCmd fuel (.seqs c k) = IConfig.seqNil <$> stepInterp stepCmd fuel c0 := by
  cases k with
  | zero =>
    refine ⟨c, rfl, rfl, rfl, fun _ _ h => ?_⟩
    have hnd := IConfig.not_done_of_abs h
    rw [stepInterp.eq_19 _ _ _ _ hnd.1 hnd.2, map_eq_pure_bind]
    congr 1
    funext i
    cases i <;> rfl
  | succ k =>
    refine ⟨.seqs c k, rfl, rfl, rfl, fun _ _ _ => ?_⟩
    by_cases hd : (∃ e, c = .terminal e) ∨ ∃ l e, c = .exiting l e
    · rcases hd with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> cases k <;> simp [stepInterp, IConfig.seqNil]
    have hnt : ∀ e, c ≠ .terminal e := fun e h => hd (.inl ⟨e, h⟩)
    have hex : ∀ l e, c ≠ .exiting l e := fun l e h => hd (.inr ⟨l, e, h⟩)
    rw [stepInterp.eq_19 _ _ _ _ hnt hex, stepInterp.eq_19 _ _ _ _ hnt hex, map_bind]
    congr 1
    funext i
    cases i <;> simp [IConfig.seqNil, Nat.add_assoc]

omit [HasFvar P] in
/-- A reference step that runs no command and resolves no choice, out of the abstraction of a
    tracked configuration `cx`, is performed by one `stepInterp (stepOf i j)` step at every large
    enough stepper indices `i`, `j` and fuel, from every state and leaving it unchanged, reaching a
    tracked configuration that stands for the step's successor; such a step emits no event. -/
private theorem stepInterp_admin_complete {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory}
    (hMono : BoundedEvalMono P)
    {x y : Config P CmdT} {evs : List (Event P)}
    (h : StepEngParamE P (ChoiceRecord.bot P) (fun _ _ _ _ _ => False) x evs y) :
    ∀ (cx : IConfig P CmdT), cx.abs F = x → cx.Denoting F → cx.Tracked →
    ∃ (f0 : Nat) (cy : IConfig P CmdT), cy.abs F = y ∧ cy.Denoting F ∧ cy.Tracked ∧ evs = [] ∧
      ∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel → ∀ st,
        obs.run (stepInterp (stepOf i j) fuel cx) cfgr st = (.ok cy, st) := by
  intro c hx hd ht
  induction h generalizing c with
  | step_cmd hc | step_ite_nondet hc | step_loop_nondet hc => exact hc.elim
  | @step_seq_inner _ _ _ ss hs ih =>
    rcases (IConfig.abs_eq_seq ..).1 hx with ⟨ci, rfl, hci⟩ | ⟨rfl, ci, k, rfl, hci⟩
    · obtain ⟨n, c', ha, hd', ht', he, h1⟩ := ih ci hci hd ht
      have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done')
      refine ⟨n, .seq c' ss, by simp [IConfig.abs, ha], hd', ht', he, fun i j k hi hj hk st => ?_⟩
      simp [stepInterp_seq_unfold_gen _ _ _ _ hnd.1 hnd.2, h1 i j k hi hj hk]
    · obtain ⟨c0, ha0, ht0, hd0, hs0⟩ := IConfig.seqs_peel (m := m) F ci k
      obtain ⟨n, c', ha, hd', ht', he, h1⟩ := ih c0 (ha0.trans hci) (hd0 ▸ hd) (ht0 ▸ ht)
      refine ⟨n, c'.seqNil, by simp [ha], by simpa using hd', by simpa using ht', he,
        fun i j f hi hj hf st => ?_⟩
      simp [hs0 _ _ (hci ▸ hs.not_done'), map_eq_pure_bind, h1 i j f hi hj hf]
  | @step_block_body _ _ _ l _ hs ih =>
    obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IConfig.abs_eq_block ..).1 hx
    obtain ⟨n, c', ha, hd', ht', he, h1⟩ := ih ci hci hd.2 ht.2
    have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done')
    have hl := StepStmtE.lvl_defines (EvalCmd := fun _ _ _ _ _ => False) (fun _ _ _ _ _ h => h.elim)
      (hs.toStepStmtE' fun _ _ _ _ _ h => h)
    refine ⟨n, .block l (fr.record ci.levelCmd?) c', by simp [IConfig.abs, ha, hfr],
      ⟨by simpa using hd.1, hd'⟩, ⟨ScopeFrame.record_exact ht.1 (by
        simpa [← hci, ← ha, InterpLang.absStore_isSome hd'.lvl,
          InterpLang.absStore_isSome hd.2.lvl] using hl), ht'⟩, he,
      fun i j k hi hj hk st => ?_⟩
    simp [stepInterp_block_unfold_gen _ _ _ _ _ hnd.1 hnd.2, h1 i j k hi hj hk]
  | step_block_done | step_block_exit_match _ =>
    obtain ⟨fr, ci, rfl, rfl, hci⟩ := (IConfig.abs_eq_block ..).1 hx
    first
      | obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_terminal ..).1 hci
      | obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_exiting ..).1 hci
    have hex := ScopeFrame.exit_eq ht.1
    exact ⟨0, .terminal { ie with store := fr.exit ie.store }, by
      simp_all [IConfig.abs, IEnv.abs, InterpLang.absStore_project _ hd.1],
      ⟨hex ▸ hd.2.1.project _, hd.2.2⟩, trivial, rfl,
      fun _ _ _ _ _ _ _ => by simp_all [stepInterp]⟩
  | @step_block_exit_mismatch _ _ l _ _ =>
    obtain ⟨fr, ci, rfl, rfl, hci⟩ := (IConfig.abs_eq_block ..).1 hx
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_exiting ..).1 hci
    have hex := ScopeFrame.exit_eq ht.1
    exact ⟨0, .exiting l { ie with store := fr.exit ie.store }, by
      simp_all [IConfig.abs, IEnv.abs, InterpLang.absStore_project _ hd.1],
      ⟨hex ▸ hd.2.1.project _, hd.2.2⟩, trivial, rfl,
      fun _ _ _ _ _ _ _ => by simp_all [stepInterp]⟩
  | step_seq_done =>
    rcases (IConfig.abs_eq_seq ..).1 hx with ⟨ci, rfl, hci⟩ | ⟨rfl, ci, (_ | k), rfl, hci⟩
    all_goals simp only [Config.wrapSeqs, IConfig.abs_eq_terminal, reduceCtorEq] at hci
    all_goals
      obtain ⟨ie, rfl, rfl⟩ := hci
      exact ⟨0, .stmts _ ie, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp [stepInterp]⟩
  | step_seq_exit =>
    rcases (IConfig.abs_eq_seq ..).1 hx with ⟨ci, rfl, hci⟩ | ⟨rfl, ci, (_ | k), rfl, hci⟩
    all_goals simp only [Config.wrapSeqs, IConfig.abs_eq_exiting, reduceCtorEq] at hci
    all_goals
      obtain ⟨ie, rfl, rfl⟩ := hci
      exact ⟨0, .exiting _ ie, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp [stepInterp]⟩
  | step_stmts_nil =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmts ..).1 hx
    exact ⟨0, .terminal ie, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp⟩
  | @step_stmts_cons s ss =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmts ..).1 hx
    cases ss
    · exact ⟨0, .seqs (.stmt s ie) 0, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp⟩
    · exact ⟨0, .seq (.stmt s ie) _, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp⟩
  | step_exit =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, .exiting _ ie, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp [stepInterp]⟩
  | step_typeDecl =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, .terminal ie, rfl, hd, trivial, rfl, fun _ _ _ _ _ _ _ => by simp [stepInterp]⟩
  | @step_ite_true g tss ess md ρ hc hok | @step_ite_false g tss ess md ρ hc hok =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨n, r, hb, -⟩ := hok.1 _ _ (storeDenotes_absStore hd.1) hc
    have hr := hok.2 _ _ _ (storeDenotes_absStore hd.1) hb
    dsimp only [IEnv.abs] at hb hr
    first
      | exact ⟨n, .block .none (.opened ie.store) (.stmts tss ie), rfl, ⟨hd.1, hd⟩,
          by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ k _ _ hk _ => by
          simp [stepInterp, resolveGuard, hd.2, hMono _ _ _ _ _ _ hk hb, hr]⟩
      | exact ⟨n, .block .none (.opened ie.store) (.stmts ess ie), rfl, ⟨hd.1, hd⟩,
          by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ k _ _ hk _ => by
          simp [stepInterp, resolveGuard, hd.2, hMono _ _ _ _ _ _ hk hb, hr]⟩
  | @step_loop_enter g mm inv body md ρ hc hok =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨n, r, hb, -⟩ := hok.1 _ _ (storeDenotes_absStore hd.1) hc
    have hr := hok.2 _ _ _ (storeDenotes_absStore hd.1) hb
    dsimp only [IEnv.abs] at hb hr
    exact ⟨n,
      .seq (.block .none (.opened ie.store) (.stmts body ie)) [.loop (.det g) mm inv body md], rfl,
      ⟨hd.1, hd⟩, by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ k _ _ hk _ => by
      simp [stepInterp, resolveGuard, hd.2, hMono _ _ _ _ _ _ hk hb, hr]⟩
  | @step_loop_exit g mm inv body md ρ hc hok =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨n, r, hb, -⟩ := hok.1 _ _ (storeDenotes_absStore hd.1) hc
    have hr := hok.2 _ _ _ (storeDenotes_absStore hd.1) hb
    dsimp only [IEnv.abs] at hb hr
    exact ⟨n, .terminal ie, rfl, hd, trivial, rfl, fun _ _ k _ _ hk _ => by
      simp [stepInterp, resolveGuard, hd.2, hMono _ _ _ _ _ _ hk hb, hr]⟩
  | @step_block l ss md ρ =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, .block (some l) (.opened ie.store) (.stmts ss ie), rfl, ⟨hd.1, hd⟩,
      by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ _ _ _ _ _ => by simp [stepInterp]⟩

omit [HasFvar P] in
/-- **The per-step completeness obligation for a stepper family, arm-parametrically.** Every
    engine-realizable step `StepEngParamE P R EvalCmd` is performed by one
    `stepInterp (stepOf i j)` step at every large enough stepper indices `i`, `j` and fuel
    (`StepInterpCompleteFam`), given that every `EvalCmd` command evaluation is so performed
    (`hcmdarm`), that `choose` resolves `R`, and that the bounded evaluator is fuel-monotone. -/
theorem stepInterpCompleteFam_of_arms {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {EvalCmd : EvalCmdParamE P CmdT (Event P)}
    (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (hcmdarm : ∀ (ρ : IEnv P) (cmd : CmdT) (σ' : SemanticStore P)
        (evs : List (Event P)) (st : obs.St), (IConfig.stmt (.cmd cmd) ρ).Denoting F →
        EvalCmd F (InterpLang.absStore F ρ.store.get) cmd σ' evs →
      ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
        RStore.Denoting F σi.get ∧
        (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
          obs.run (stepInterp (stepOf i j) fuel (.stmt (.cmd cmd) ρ)) cfgr st
            = (.ok (.terminal { ρ with store := σi }), st'))
        ∧ obs.TraceExt F st st' evs)
    (hdefs : CmdDefsSound EvalCmd) :
    StepInterpCompleteFam obs stepOf cfgr F R EvalCmd := by
  intro c _ _ st ht hd h
  generalize hx : c.abs F = x at h
  induction h generalizing c st with
  | step_cmd hc =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨n, σi, s, hσ, hdσ, h1, h2⟩ := hcmdarm _ _ _ _ st hd hc
    exact ⟨n, _, s, h1, by simp [IConfig.abs, IEnv.abs, hσ], ⟨hdσ, hd.2⟩, trivial, h2⟩
  | @step_seq_inner _ _ _ ss hs ih =>
    rcases (IConfig.abs_eq_seq ..).1 hx with ⟨ci, rfl, hci⟩ | ⟨rfl, ci, k, rfl, hci⟩
    · obtain ⟨n, c', s, h1, ha, hd', ht', h2⟩ := ih ci st ht hd hci
      have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done')
      refine ⟨n, .seq c' ss, s, fun i j k hi hj hk => ?_, by simp [IConfig.abs, ha], hd', ht', h2⟩
      simp [stepInterp_seq_unfold_gen _ _ _ _ hnd.1 hnd.2, h1 i j k hi hj hk]
    · obtain ⟨c0, ha0, ht0, hd0, hs0⟩ := IConfig.seqs_peel (m := m) F ci k
      obtain ⟨n, c', s, h1, ha, hd', ht', h2⟩ := ih c0 st (ht0 ▸ ht) (hd0 ▸ hd) (ha0.trans hci)
      refine ⟨n, c'.seqNil, s, fun i j f hi hj hf => ?_, by simp [ha], by simpa using hd',
        by simpa using ht', h2⟩
      simp [hs0 _ _ (hci ▸ hs.not_done'), map_eq_pure_bind, h1 i j f hi hj hf]
  | @step_block_body _ _ _ l _ hs ih =>
    obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IConfig.abs_eq_block ..).1 hx
    obtain ⟨n, c', s, h1, ha, hd', ht', h2⟩ := ih ci st ht.2 hd.2 hci
    have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done')
    have hl := StepStmtE.lvl_defines hdefs
      (hs.toStepStmtE' (EvalCmd := EvalCmd) fun _ _ _ _ _ h => h)
    refine ⟨n, .block l (fr.record ci.levelCmd?) c', s, fun i j k hi hj hk => ?_,
      by simp [IConfig.abs, ha, hfr], ⟨by simpa using hd.1, hd'⟩,
      ⟨ScopeFrame.record_exact ht.1 (by
        simpa [← hci, ← ha, InterpLang.absStore_isSome hd'.lvl,
          InterpLang.absStore_isSome hd.2.lvl] using hl), ht'⟩, h2⟩
    simp [stepInterp_block_unfold_gen _ _ _ _ _ hnd.1 hnd.2, h1 i j k hi hj hk]
  | @step_ite_nondet v tss ess _ ρ hR hv =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨r, s, h1, -, htt, hff, h2⟩ :=
      hchoose ie.store.get _ _ _ st (storeDenotes_absStore hd.1) hR
    rcases hv with rfl | rfl
    · refine ⟨0, .block .none (.opened ie.store) (.stmts tss ie), s, fun _ _ _ _ _ _ => ?_,
        by simp [IConfig.abs, IEnv.abs, ScopeFrame.opened], ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], traceExt_of_eq h2⟩
      simp [stepInterp, resolveGuard, hd.2, h1, htt rfl]
    · refine ⟨0, .block .none (.opened ie.store) (.stmts ess ie), s, fun _ _ _ _ _ _ => ?_,
        by simp [IConfig.abs, IEnv.abs, ScopeFrame.opened, (HasBool.ttVal_ne_ffVal F).symm],
        ⟨hd.1, hd⟩, by simp [IConfig.Tracked, IConfig.lvl], traceExt_of_eq h2⟩
      simp [stepInterp, resolveGuard, hd.2, h1, hff rfl]
  | @step_loop_nondet v mm inv body md ρ hR hv =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨r, s, h1, -, htt, hff, h2⟩ :=
      hchoose ie.store.get _ _ _ st (storeDenotes_absStore hd.1) hR
    rcases hv with rfl | rfl
    · refine ⟨0,
        .seq (.block .none (.opened ie.store) (.stmts body ie)) [.loop .nondet mm inv body md], s,
        fun _ _ _ _ _ _ => ?_, by simp [IConfig.abs, ScopeFrame.opened, IEnv.abs], ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], traceExt_of_eq h2⟩
      simp [stepInterp, resolveGuard, hd.2, h1, htt rfl]
    · refine ⟨0, .terminal ie, s, fun _ _ _ _ _ _ => ?_,
        by simp [IConfig.abs, IEnv.abs, (HasBool.ttVal_ne_ffVal F).symm], hd, trivial,
        traceExt_of_eq h2⟩
      simp [stepInterp, resolveGuard, hd.2, h1, hff rfl]
  | _ =>
    exact (stepInterp_admin_complete obs stepOf cfgr hMono (evs := [])
      (by constructor <;> assumption) _ hx hd ht).elim fun n ⟨cy, ha, hd', ht', _, h1⟩ =>
      ⟨n, cy, st, fun i j k hi hj hk => h1 i j k hi hj hk st, ha, hd', ht', traceExt_nil ..⟩

/-- **`StepInterpCompleteGenericOn` from the `InterpObs` laws**: given a fuel-monotone bounded
evaluator, every observation
whose `emit` succeeds on the events satisfying `Q` and whose `choose` resolves `R` performs every
engine-realizable base-command step emitting only such events by one `stepInterp` step, at
every sufficiently large fuel. -/
private theorem stepInterpCompleteGenericOn_of_laws (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitTotalOn obs cfgr Q) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P) :
    StepInterpCompleteGenericOn obs cfgr F R Q := by
  intro c c' evs s ht hd h q
  have hq : StepEngParamE P R (fun f σ c τ e => EvalCmdEngE P R f σ c τ e ∧ ∀ v ∈ e, Q v)
      (c.abs F) evs c' := by
    generalize c.abs F = x at h
    induction h <;> constructor <;> grind
  refine (stepInterpCompleteFam_of_arms _ (fun _ _ => baseStepCmd) _
    (EvalCmd := fun f σ c τ e => EvalCmdEngE P R f σ c τ e ∧ ∀ v ∈ e, Q v)
    hchoose hMono
    (fun ρ _ _ _ s hdρ ⟨c, q⟩ =>
      (obs_stepBaseCmdStore_complete_on _ _ hemit hchoose hMono hdρ.1 c q s).elim
        fun n ⟨σi, s, hσ, hdσ, a, b⟩ => ⟨n, σi, s, hσ, hdσ, fun _ _ k _ _ h =>
          obs_stepInterp_cmd_fwd _ _ _ _ _ _ _ _ (hdρ.2 ▸ a k h), b⟩)
    (fun _ _ _ _ _ h => evalCmdE_cmdDefsSound _ _ _ _ _ h.1.toEvalCmdE)
    _ _ _ s ht hd hq).elim fun n ⟨c, s, a, b⟩ => ⟨n, c, s, fun k h => a k k k h h h, b⟩

/-- Given a fuel-monotone bounded evaluator, every observation whose `emit` always succeeds and
    whose `choose` resolves `R` performs every engine-realizable base-command step by one `stepInterp` step, at every
    sufficiently large fuel (`StepInterpCompleteGeneric`). -/
private theorem stepInterpCompleteGeneric_of_laws (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P) :
    StepInterpCompleteGeneric obs cfgr F R := by
  intro _ _ _ _ _ _ _
  apply stepInterpCompleteGenericOn_of_laws _ _ (hemit.toOn fun _ => True) hchoose <;> grind

/-! ### Completeness along a choice sequence, for any command type

A reference run *reads its choices off an oracle*: each nondeterministic choice it resolves
(the value a nondeterministic `.init`/`.set` writes, or the Boolean a `.nondet` guard is read
as) is popped off the front of an oracle list, in execution order.  An observation follows such
a run when its `choose` returns the pending choices (`ChooseFollows`). -/

/-- A command relation over the command type `CmdT` that reads choices off an oracle:
    `E f σ c σ' evs o o'` says that `c` runs from store `σ` to `σ'` emitting `evs` and turns the
    oracle `o` into `o'`. -/
abbrev OracleCmdParamRel (P : PureExpr.{u}) (CmdT : Type) : Type u :=
  P.Factory → SemanticStore P → CmdT → SemanticStore P → Trace P →
    List P.Val → List P.Val → Prop

/-- One reference statement step over the oracle-reading command relation `E`, on a
    configuration paired with an oracle.  A step that resolves no choice and runs no command
    leaves the oracle alone; a `.nondet` guard pops the Boolean it is read as, which the choice
    record `R` allows: `tt` for the then-branch or loop entry, `ff` for the else-branch or loop
    exit. -/
inductive OracleStepParamE {CmdT : Type} (R : ChoiceRecord P) (E : OracleCmdParamRel P CmdT)
    :
    Config P CmdT × List P.Val → List (Event P) → Config P CmdT × List P.Val → Prop where
  /-- A step that resolves no choice and runs no command. -/
  | step_det {c c' : Config P CmdT} {evs : List (Event P)} {o : List P.Val} :
      StepEngParamE P (ChoiceRecord.bot P) (fun _ _ _ _ _ => False) c evs c' →
      OracleStepParamE R E (c, o) evs (c', o)
  /-- A nondeterministic `ite` reads `tt` to take the then-branch. -/
  | step_ite_then :
      R ρ.factory ρ.store HasBool.boolTy (HasBool.ttVal ρ.factory) →
      OracleStepParamE R E (.stmt (.ite .nondet tss ess md) ρ, HasBool.ttVal ρ.factory :: o) []
        (.block .none ρ.store (.stmts tss ρ), o)
  /-- A nondeterministic `ite` reads `ff` to take the else-branch. -/
  | step_ite_else :
      R ρ.factory ρ.store HasBool.boolTy (HasBool.ffVal ρ.factory) →
      OracleStepParamE R E (.stmt (.ite .nondet tss ess md) ρ, HasBool.ffVal ρ.factory :: o) []
        (.block .none ρ.store (.stmts ess ρ), o)
  /-- A nondeterministic `loop` reads `tt` to enter its body. -/
  | step_loop_enter :
      R ρ.factory ρ.store HasBool.boolTy (HasBool.ttVal ρ.factory) →
      OracleStepParamE R E (.stmt (.loop .nondet meas inv body md) ρ, HasBool.ttVal ρ.factory :: o) []
        (.seq (.block .none ρ.store (.stmts body ρ)) [.loop .nondet meas inv body md], o)
  /-- A nondeterministic `loop` reads `ff` to exit. -/
  | step_loop_exit :
      R ρ.factory ρ.store HasBool.boolTy (HasBool.ffVal ρ.factory) →
      OracleStepParamE R E (.stmt (.loop .nondet meas inv body md) ρ, HasBool.ffVal ρ.factory :: o) []
        (.terminal ρ, o)
  /-- Execute one command through `E`. -/
  | step_cmd :
      E ρ.factory ρ.store cmd σ' evs o o' →
      OracleStepParamE R E (.stmt (.cmd cmd) ρ, o) evs (.terminal { ρ with store := σ' }, o')
  /-- Lift one inner sequence step. -/
  | step_seq_inner :
      OracleStepParamE R E (inner, o) evs (inner', o') →
      OracleStepParamE R E (.seq inner ss, o) evs (.seq inner' ss, o')
  /-- Lift one inner block step. -/
  | step_block_body :
      OracleStepParamE R E (inner, o) evs (inner', o') →
      OracleStepParamE R E (.block label σp inner, o) evs (.block label σp inner', o')

/-- **The choice sequence of a reference run, for any command type.**
    `RunChoicesParam R E c evs c' cs`: a run of oracle-reading steps over `E` from `c` to `c'`
    emitting `evs` resolves its choices, in execution order, as the values `cs`.  Read off the
    front of any oracle `cs ++ rest`, they leave `rest`. -/
@[expose] def RunChoicesParam {CmdT : Type} (R : ChoiceRecord P) (E : OracleCmdParamRel P CmdT)
    (c : Config P CmdT) (evs : List (Event P)) (c' : Config P CmdT)
    (cs : List P.Val) : Prop :=
  ∀ rest, ReflTransTrace (OracleStepParamE R E) (c, cs ++ rest) evs (c', rest)

omit [HasFvar P] [DecidableEq P.Ident] [HasBoolOps P] [DecidableEq P.Expr] in
/-- The configuration an oracle-reading step leaves is not one the driver stops at. -/
private theorem OracleStepParamE.not_done {CmdT : Type} {R : ChoiceRecord P}
    {E : OracleCmdParamRel P CmdT} {x y : Config P CmdT × List P.Val}
    {evs : List (Event P)} (h : OracleStepParamE R E x evs y) :
    (∀ e, x.1 ≠ .terminal e) ∧ (∀ l e, x.1 ≠ .exiting l e) := by
  cases h with
  | step_det h => exact h.not_done'
  | _ => simp

omit [HasFvar P] [DecidableEq P.Ident] [DecidableEq P.Expr] in
/-- An oracle-reading step defines at the level of its configuration only names of the command it
    runs there, when every command evaluation of `E` defines only the names `CmdDefs` lists. -/
private theorem OracleStepParamE.lvl_defines {CmdT : Type} [CmdDefs P CmdT] {R : ChoiceRecord P}
    {E : OracleCmdParamRel P CmdT}
    (hdefs : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → DefinesWithin σ σ' (CmdDefs.defs c))
    {x y : Config P CmdT × List P.Val} {evs : List (Event P)} (h : OracleStepParamE R E x evs y) :
    ∀ v, (y.1.lvl v).isSome →
      (x.1.lvl v).isSome ∨ ∃ cmd, x.1.levelCmd? = some cmd ∧ v ∈ CmdDefs.defs (P := P) cmd := by
  induction h with
  | step_det h =>
    exact StepStmtE.lvl_defines (EvalCmd := fun _ _ _ _ _ => False) (fun _ _ _ _ _ h => h.elim)
      (h.toStepStmtE' fun _ _ _ _ _ h => h)
  | step_cmd hc => exact fun v hv => (hdefs _ _ _ _ _ _ _ hc v hv).imp_right fun h => ⟨_, rfl, h⟩
  | step_seq_inner _ ih => exact ih
  | step_block_body => exact fun _ hv => .inl hv
  | _ => exact fun _ hv => .inl (by simpa [Config.lvl] using hv)

/-- **The per-command law along a choice sequence, for a family of steppers.**  Every command
    evaluation `E ρ.factory ρ.store cmd σ' evs o o'` whose events satisfy `Q` is performed by one
    `stepInterp (stepOf i j)` step from every state `st` with `Pending st o`, under the reader
    config `cfgr`, at every stepper indices `i`, `j` and fuel above a common threshold, recording
    exactly `evs` and leaving a state `st'` with `Pending st' o'`. -/
def CmdFollowsFam {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m)
    (cfgr : obs.Cfg) (F : P.Factory) (Pending : obs.St → List P.Val → Prop) (Q : Event P → Prop)
    (E : OracleCmdParamRel P CmdT) : Prop :=
  ∀ (ρ : IEnv P) (cmd : CmdT) (σ' : SemanticStore P) (evs : List (Event P))
    (o o' : List P.Val), (IConfig.stmt (.cmd cmd) ρ).Denoting F →
    E F (InterpLang.absStore F ρ.store.get) cmd σ' evs o o' → (∀ ev ∈ evs, Q ev) →
    ∀ st, Pending st o →
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (stepInterp (stepOf i j) fuel (.stmt (.cmd cmd) ρ)) cfgr st
          = (.ok (.terminal { ρ with store := σi }), st'))
      ∧ Pending st' o' ∧ obs.TraceExt F st st' evs

omit [HasFvar P] in
/-- **Following a choice sequence, up to a prefix, for a family of steppers.**  If an oracle-reading
    run over the command relation `E` goes from `x.1` with oracle `x.2` to `y.1` with oracle `y.2`
    and emits events satisfying `Q`, then for every tracked configuration `cx` standing for `x.1`
    and every state `st` with `Pending st x.2` there are `k`, a tracked configuration `cy` standing
    for `y.1` and a state `st'` with `Pending st' y.2`, whose trace is that of `st` with runtime
    events standing for the run's events prepended, such that at every large enough stepper
    indices `i`, `j` and fuel, the run of `runInterp (stepOf i j)` at fuel `fuel + k` from `cx` is
    its run at fuel `fuel` from `cy` from `st'`.  The run may stop anywhere.  Hypotheses:
    `choose` follows the pending choices that `R` allows (`hf`); the bounded evaluator is
    fuel-monotone; every command evaluation of `E` whose events satisfy `Q` is performed by one
    step that consumes its oracle segment (`hcmd`) and defines only the names `CmdDefs` lists
    (`hdefs`). -/
theorem runInterp_follows_prefix_fam {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {Q : Event P → Prop} {E : OracleCmdParamRel P CmdT} (Pending : obs.St → List P.Val → Prop)
    (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hcmd : CmdFollowsFam obs stepOf cfgr F Pending Q E)
    (hdefs : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → DefinesWithin σ σ' (CmdDefs.defs c))
    {x y : Config P CmdT × List P.Val} {evs : List (Event P)}
    (hrun : ReflTransTrace (OracleStepParamE R E) x evs y)
    (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st x.2)
    (cx : IConfig P CmdT) (hcx : cx.abs F = x.1) (hdx : cx.Denoting F)
    (htx : cx.Tracked) :
    ∃ (k f0 : Nat) (cy : IConfig P CmdT) (st' : obs.St),
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (runInterp (stepOf i j) (fuel + k) cx) cfgr st
        = obs.run (runInterp (stepOf i j) fuel cy) cfgr st')
      ∧ cy.abs F = y.1 ∧ cy.Denoting F ∧ cy.Tracked ∧ Pending st' y.2
      ∧ obs.TraceExt F st st' evs := by
  have hstep : ∀ x evs y, OracleStepParamE R E x evs y →
      (∀ ev ∈ evs, Q ev) → ∀ st, Pending st x.2 → ∀ cx : IConfig P CmdT, cx.abs F = x.1 →
      cx.Denoting F → cx.Tracked → ∃ (f0 : Nat) (cy : IConfig P CmdT) (st' : obs.St),
        (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
          obs.run (stepInterp (stepOf i j) fuel cx) cfgr st = (.ok cy, st'))
        ∧ cy.abs F = y.1 ∧ cy.Denoting F ∧ cy.Tracked ∧ Pending st' y.2
        ∧ obs.TraceExt F st st' evs := by
    intro x evs y h hq st hst c hx hd ht
    induction h generalizing st c with
    | step_det h =>
      obtain ⟨n, cy, ha, hd', ht', rfl, h1⟩ := stepInterp_admin_complete obs stepOf cfgr
        hMono h c hx hd ht
      exact ⟨n, cy, st, fun i j k hi hj hk => h1 i j k hi hj hk st, ha, hd', ht', hst,
        traceExt_nil ..⟩
    | @step_ite_then tss ess md ρ o hR =>
      obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
      obtain ⟨r, s, h1, -, htt, -, h2, h3⟩ :=
        hf.choose ie.store.get _ _ _ _ st (storeDenotes_absStore hd.1) hst hR
      exact ⟨0, .block .none (.opened ie.store) (.stmts tss ie), s, fun _ _ _ _ _ _ => by
        simp [stepInterp, resolveGuard, hd.2, h1, htt rfl], rfl, ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], h3, traceExt_of_eq h2⟩
    | @step_ite_else tss ess md ρ o hR =>
      obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
      obtain ⟨r, s, h1, -, -, hff, h2, h3⟩ :=
        hf.choose ie.store.get _ _ _ _ st (storeDenotes_absStore hd.1) hst hR
      exact ⟨0, .block .none (.opened ie.store) (.stmts ess ie), s, fun _ _ _ _ _ _ => by
        simp [stepInterp, resolveGuard, hd.2, h1, hff rfl], rfl, ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], h3, traceExt_of_eq h2⟩
    | @step_loop_enter mm inv body md ρ o hR =>
      obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
      obtain ⟨r, s, h1, -, htt, -, h2, h3⟩ :=
        hf.choose ie.store.get _ _ _ _ st (storeDenotes_absStore hd.1) hst hR
      exact ⟨0,
        .seq (.block .none (.opened ie.store) (.stmts body ie)) [.loop .nondet mm inv body md], s,
        fun _ _ _ _ _ _ => by simp [stepInterp, resolveGuard, hd.2, h1, htt rfl], rfl, ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], h3, traceExt_of_eq h2⟩
    | @step_loop_exit mm inv body md ρ o hR =>
      obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
      obtain ⟨r, s, h1, -, -, hff, h2, h3⟩ :=
        hf.choose ie.store.get _ _ _ _ st (storeDenotes_absStore hd.1) hst hR
      exact ⟨0, .terminal ie, s, fun _ _ _ _ _ _ => by
        simp [stepInterp, resolveGuard, hd.2, h1, hff rfl], rfl, hd, trivial, h3,
        traceExt_of_eq h2⟩
    | step_cmd hc =>
      obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
      obtain ⟨n, σi, s, hσ, hdσ, h1, h2, h3⟩ := hcmd _ _ _ _ _ _ hd hc hq st hst
      exact ⟨n, _, s, h1, by simp [IConfig.abs, IEnv.abs, hσ], ⟨hdσ, hd.2⟩, trivial, h2, h3⟩
    | @step_seq_inner _ _ _ _ _ ss hs ih =>
      rcases (IConfig.abs_eq_seq ..).1 hx with ⟨ci, rfl, hci⟩ | ⟨rfl, ci, k, rfl, hci⟩
      · obtain ⟨n, c', s, h1, ha, hd', ht', h2⟩ := ih hq st hst ci hci hd ht
        have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done)
        refine ⟨n, .seq c' ss, s, fun i j k hi hj hk => ?_, by simp [IConfig.abs, ha], hd', ht',
          h2⟩
        simp [stepInterp_seq_unfold_gen _ _ _ _ hnd.1 hnd.2, h1 i j k hi hj hk]
      · obtain ⟨c0, ha0, ht0, hd0, hs0⟩ := IConfig.seqs_peel (m := m) F ci k
        obtain ⟨n, c', s, h1, ha, hd', ht', h2⟩ :=
          ih hq st hst c0 (ha0.trans hci) (hd0 ▸ hd) (ht0 ▸ ht)
        refine ⟨n, c'.seqNil, s, fun i j f hi hj hf => ?_, by simp [ha], by simpa using hd',
          by simpa using ht', h2⟩
        simp [hs0 _ _ (hci ▸ hs.not_done), map_eq_pure_bind, h1 i j f hi hj hf]
    | @step_block_body _ _ _ _ _ l _ hs ih =>
      obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IConfig.abs_eq_block ..).1 hx
      obtain ⟨n, c', s, h1, ha, hd', ht', h2⟩ := ih hq st hst ci hci hd.2 ht.2
      simp only at ha hci
      have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done)
      have hl := OracleStepParamE.lvl_defines hdefs hs
      refine ⟨n, .block l (fr.record ci.levelCmd?) c', s, fun i j k hi hj hk => ?_,
        by simp [IConfig.abs, ha, hfr], ⟨by simpa using hd.1, hd'⟩,
        ⟨ScopeFrame.record_exact ht.1 (by
          simpa [← hci, ← ha, InterpLang.absStore_isSome hd'.lvl,
            InterpLang.absStore_isSome hd.2.lvl] using hl), ht'⟩, h2⟩
      simp [stepInterp_block_unfold_gen _ _ _ _ _ hnd.1 hnd.2, h1 i j k hi hj hk]
  induction hrun generalizing st cx with
  | refl => exact ⟨0, 0, cx, st, fun _ _ _ _ _ _ => rfl, hcx, hdx, htx, hst, traceExt_nil ..⟩
  | step _ _ _ _ _ hs _ ih =>
    obtain ⟨hq1, hq2⟩ := List.forall_mem_append.1 hq
    obtain ⟨a, c1, s, h1, ha, hd1, ht1, r1, t1⟩ := hstep _ _ _ hs hq1 st hst cx hcx hdx htx
    obtain ⟨k, b, cy, s', h2, hy, hdy, hty, r2, t2⟩ := ih hq2 s r1 c1 ha hd1 ht1
    refine ⟨k + 1, a + b, cy, s', fun i j F hi hj hF => ?_, hy, hdy, hty, r2, t1.append t2⟩
    have hnd := IConfig.not_done_of_abs (hcx ▸ hs.not_done)
    rw [← Nat.add_assoc, ← h2 i j F (by omega) (by omega) (by omega),
      runInterp_succ_nonterminal _ _ _ hnd.1 hnd.2]
    simp [h1 i j (F + k + 1) (by omega) (by omega) (by omega)]

omit [HasFvar P] in
/-- **Whole-run completeness along a choice sequence, for a family of steppers.** If an
    oracle-reading run over the command relation `E` goes from `x` to a configuration `y.1` the
    driver stops at, emitting events `evs` that satisfy `Q`, then for every tracked configuration
    `cx` standing for `x.1` and every state `st` with `Pending st x.2`, `runInterp (stepOf i j)`
    from `cx` reaches a configuration denoting `y.1` at every large enough stepper indices `i`, `j`
    and fuel, prepending runtime events that stand for exactly `evs` to the trace and leaving a
    state `st'` with `Pending st' y.2`.
    Hypotheses: `choose` follows the pending choices that `R` allows (`hf`); the bounded evaluator
    is fuel-monotone; every command evaluation of `E` whose events satisfy `Q` is
    performed by one `stepOf` step that consumes its oracle segment (`hcmd`) and defines only the
    names `CmdDefs` lists (`hdefs`). -/
theorem runInterp_complete_follows_fam {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepOf : Nat → Nat → StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {Q : Event P → Prop} {E : OracleCmdParamRel P CmdT} (Pending : obs.St → List P.Val → Prop)
    (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hcmd : CmdFollowsFam obs stepOf cfgr F Pending Q E)
    (hdefs : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → DefinesWithin σ σ' (CmdDefs.defs c))
    {x y : Config P CmdT × List P.Val} {evs : List (Event P)}
    (hrun : ReflTransTrace (OracleStepParamE R E) x evs y)
    (hdone : Config.Done y.1) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st x.2)
    (cx : IConfig P CmdT) (hcx : cx.abs F = x.1) (hdx : cx.Denoting F)
    (htx : cx.Tracked) :
    ∃ (f0 : Nat) (cy : IConfig P CmdT) (st' : obs.St), cy.Denotes F y.1 ∧
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (runInterp (stepOf i j) fuel cx) cfgr st = (.ok cy, st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs := by
  obtain ⟨k, f0, cy, st', h, hy, hdy, hty, hp, ht⟩ := runInterp_follows_prefix_fam obs stepOf cfgr
    Pending hf hMono hcmd hdefs hrun hq st hst cx hcx hdx htx
  refine ⟨f0 + k, cy, st', ⟨hdy, hty, hy⟩, fun i j fuel hi hj hfuel => ?_, hp, ht⟩
  rw [← Nat.sub_add_cancel (by omega : k ≤ fuel), h i j _ (by omega) (by omega) (by omega),
    runInterp_of_abs_done _ _ (hy ▸ hdone)]
  simp

omit [HasFvar P] in
/-- **Whole-run completeness along a choice sequence, arm-parametrically.** If an oracle-reading run
    over the command relation `E` from the abstraction of a tracked configuration `start` resolves
    its choices as `cs` (`RunChoicesParam`), ends at a configuration `final` the monadic interpreter
    stops at and emits events satisfying `Q`, then from every state `st` with `Pending st cs` the
    monadic interpreter `runInterp stepCmd` reaches a configuration denoting `final` from `start` at
    every large enough fuel, prepending runtime events that stand for exactly the run's events to
    the trace. Hypotheses: `choose`
    follows the pending choices that `R` allows (`hf`); the bounded evaluator is fuel-monotone;
    every command evaluation of `E` whose events satisfy `Q` is performed by one
    `stepCmd` step that consumes its oracle segment (`hcmd`) and defines only the names `CmdDefs`
    lists (`hdefs`). -/
theorem runInterp_complete_follows_param {CmdT : Type} [CmdDefs P CmdT] (obs : InterpObs P m)
    (stepCmd : StepCmdM P CmdT m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {Q : Event P → Prop} {E : OracleCmdParamRel P CmdT} (Pending : obs.St → List P.Val → Prop)
    (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hcmd : CmdFollowsFam obs (fun _ _ => stepCmd) cfgr F Pending Q E)
    (hdefs : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → DefinesWithin σ σ' (CmdDefs.defs c))
    {start : IConfig P CmdT} {final : Config P CmdT} {evs : List (Event P)}
    {cs : List P.Val} (hrun : RunChoicesParam R E (start.abs F) evs final cs)
    (hds : start.Denoting F) (htr : start.Tracked)
    (hdone : Config.Done final) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (f0 : Nat) (final' : IConfig P CmdT) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp stepCmd fuel start) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact (runInterp_complete_follows_fam obs _ cfgr Pending hf hMono hcmd hdefs
    (List.append_nil cs ▸ hrun []) hdone hq st hst start rfl hds htr).imp
    fun _ ⟨c, s, hc, a, _, b⟩ => ⟨c, s, hc, fun f h => a f f f h h h, b⟩

/-! ### The base-command instance -/

/-- The oracle-reading base-command relation: an engine-realizable evaluation of a base command
    under the choice record `R`.  A deterministic command leaves the oracle alone; a
    nondeterministic `.init`/`.set` of `x` pops the value it writes. -/
@[expose] def OracleCmdEngE (R : ChoiceRecord P) : OracleCmdParamRel P (Cmd P) :=
  fun f σ c σ' evs o o' => EvalCmdEngE P R f σ c σ' evs ∧
    ((CmdDeterministic c = true ∧ o' = o) ∨ ∃ x v, o = v :: o' ∧ σ' x = some v ∧
      ((∃ ty md, c = .init x ty .nondet md) ∨ ∃ md, c = .set x .nondet md))

omit [HasBoolOps P] in
/-- An oracle-reading base-command evaluation whose events satisfy `Q` is performed by
    `stepBaseCmdStore` at every large enough fuel from every state `st` with `Pending st o`,
    recording exactly its events and leaving a state `st'` with `Pending st' o'`, given that
    `emit` succeeds on the events satisfying `Q`, that `choose` follows the pending choices `R`
    allows, and that the bounded evaluator is fuel-monotone. -/
theorem oracleCmdEngE_follows (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    {σ : IStore P} {σ' : SemanticStore P} {c : Cmd P} {evs : List (Event P)}
    {o o' : List P.Val} (hd : RStore.Denoting F σ.get)
    (h : OracleCmdEngE R F (InterpLang.absStore F σ.get) c σ' evs o o') (hq : ∀ ev ∈ evs, Q ev)
    (st : obs.St) (hst : Pending st o) :
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (stepBaseCmdStore (m := m) fuel (InterpLang.rfactory F) σ c) cfgr st
          = (.ok σi, st'))
      ∧ Pending st' o' ∧ obs.TraceExt F st st' evs := by
  have hsd := storeDenotes_absStore hd
  have hn := absStore_eq_none hd
  have hs := @absStore_eq_some _ _ F σ.get
  obtain ⟨he, ⟨hdet, rfl⟩ | ⟨x, v, rfl, hx, hk⟩⟩ := h
  · cases he with
    | @eval_init _ _ _ _ _ x _ hx he hok =>
      obtain ⟨n, r, hb, hr⟩ := hok.1 σ.get _ hsd he
      obtain ⟨hv, ht⟩ := hok.2 σ.get n r hsd hb
      refine ⟨n, σ.update x r, st, by simp [InterpLang.absStore_update _ _ hr],
        by simpa using hd.update _ hr, fun k hk => ?_, hst, traceExt_nil ..⟩
      simp [stepBaseCmdStore, hn _ hx, hMono _ _ _ _ _ _ hk hb, hv, ht]
    | @eval_set _ _ _ _ x _ _ hx he hok =>
      obtain ⟨ro, hro, -⟩ := hs _ _ hx
      obtain ⟨n, r, hb, hr⟩ := hok.1 σ.get _ hsd he
      obtain ⟨hv, ht⟩ := hok.2 σ.get n r hsd hb ro hro
      refine ⟨n, σ.update x r, st, by simp [InterpLang.absStore_update _ _ hr],
        by simpa using hd.update _ hr, fun k hk => ?_, hst, traceExt_nil ..⟩
      simp [stepBaseCmdStore, hro, hMono _ _ _ _ _ _ hk hb, hv, ht]
    | eval_init_nondet | eval_set_nondet =>
      simp [CmdDeterministic, ExprOrNondet.isDet] at hdet
    | _ =>
      obtain ⟨s, h1⟩ := (by first
        | exact hemit F (.assert ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st (hq _ (.head _))
        | exact hemit F (.assume ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st (hq _ (.head _))
        | exact hemit F (.cover ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st (hq _ (.head _)))
      exact ⟨0, σ, s, rfl, hd, fun _ _ => by simp [*, Cmd.rEmittedEvents],
        hf.emit _ _ _ _ _ h1 hst, traceExt_single (obs.emit_trace _ _ _ _ _ h1)⟩
  · rcases hk with ⟨ty, md, rfl⟩ | ⟨md, rfl⟩
    · cases he with | eval_init_nondet hx0 hR =>
      obtain rfl : _ = v := by simpa [SemanticStore.update] using hx
      obtain ⟨r, s, h1, hr, -, -, h2, h3⟩ := hf.choose σ.get _ _ _ _ st hsd hst hR
      refine ⟨0, σ.update x r, s, by simp [InterpLang.absStore_update _ _ hr],
        by simpa using hd.update _ hr, fun _ _ => ?_, h3, traceExt_of_eq h2⟩
      simp [stepBaseCmdStore, hn x hx0, h1]
    · cases he with | eval_set_nondet hx0 hty hR _ hok =>
      obtain rfl : _ = v := by simpa [SemanticStore.update] using hx
      obtain ⟨ro, hro, -⟩ := hs _ _ hx0
      obtain ⟨r, s, h1, hr, -, -, h2, h3⟩ := hf.choose σ.get _ _ _ _ st hsd hst hR
      obtain ⟨hv, ht⟩ := hok σ.get ro r hsd hro hr
      refine ⟨0, σ.update x r, s, by simp [InterpLang.absStore_update _ _ hr],
        by simpa using hd.update _ hr, fun _ _ => ?_, h3, traceExt_of_eq h2⟩
      simp [stepBaseCmdStore, hro, hty σ.get ro hsd hro, h1, hv, ht]

/-- **Whole-run completeness along a choice sequence, for base commands.**  If an oracle-reading run
    of the base-command semantics from the abstraction of a tracked configuration `start` resolves
    its choices as `cs` (`RunChoicesParam` over `OracleCmdEngE R`), ends at a configuration
    `final` the monadic interpreter stops at and emits events satisfying `Q`, then from every state
    `st` with `Pending st cs` the monadic interpreter `runInterp baseStepCmd` reaches a
    configuration denoting `final` from `start` at every large enough fuel, prepending runtime events
    that stand for exactly the run's events to the trace. Hypotheses: `emit` succeeds on the events
    satisfying `Q` (`hemit`); `choose` follows the pending choices that `R` allows (`hf`); the
    bounded evaluator is fuel-monotone. -/
theorem runInterp_complete_follows (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    {start : IConfig P (Cmd P)} {final : Config P (Cmd P)} {evs : List (Event P)}
    {cs : List P.Val} (hrun : RunChoicesParam R (OracleCmdEngE R) (start.abs F) evs final cs)
    (hds : start.Denoting F) (htr : start.Tracked)
    (hdone : Config.Done final) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel start) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact runInterp_complete_follows_param obs _ cfgr Pending hf hMono
    (fun _ _ _ _ _ _ hdρ h hq st hst =>
      (oracleCmdEngE_follows obs cfgr Pending hemit hf hMono hdρ.1 h hq st hst).imp
        fun _ ⟨σi, s, hσ, hdσ, a, b⟩ => ⟨σi, s, hσ, hdσ, fun _ _ k _ _ hk =>
          obs_stepInterp_cmd_fwd _ _ _ _ _ _ _ _ (hdρ.2 ▸ a k hk), b⟩)
    (fun _ _ _ _ _ _ _ h => evalCmdE_cmdDefsSound _ _ _ _ _ h.1.toEvalCmdE)
    hrun hds htr hdone hq st hst

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- **Every engine-realizable run has a choice sequence**: a run of `StepEngStarE R` resolves its
    choices as some `cs` over `OracleCmdEngE R` (`RunChoicesParam`). -/
theorem runChoicesParam_of_stepEngStarE {R : ChoiceRecord P}
    {c c' : Config P (Cmd P)} {evs : List (Event P)} (h : StepEngStarE P R c evs c') :
    ∃ cs, RunChoicesParam R (OracleCmdEngE R) c evs c' cs := by
  induction h with
  | refl => exact ⟨[], fun _ => .refl _⟩
  | step x e y _ _ hs hr ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨a, ha⟩ : ∃ cs, ∀ rest,
        OracleStepParamE R (OracleCmdEngE R) (x, cs ++ rest) e (y, rest) := by
      clear hb hr
      induction hs with
      | step_cmd h =>
        cases h <;> first
        | exact ⟨[], fun _ => .step_cmd ⟨by constructor <;> assumption, .inl ⟨rfl, rfl⟩⟩⟩
        | exact ⟨[_], fun _ => .step_cmd ⟨by constructor <;> assumption,
            .inr ⟨_, _, rfl, ite_eq_left rfl, by simp⟩⟩⟩
      | step_ite_nondet hR hv | step_loop_nondet hR hv =>
        rcases hv with rfl | rfl <;>
          simp only [↓reduceIte, ite_eq_right (HasBool.ttVal_ne_ffVal _).symm]
        all_goals exact ⟨[_], fun _ => by constructor; exact hR⟩
      | step_seq_inner _ ih | step_block_body _ ih =>
        exact ih.imp fun _ H r => by constructor; exact H r
      | _ => exact ⟨[], fun _ => .step_det (by constructor <;> assumption)⟩
    exact ⟨a ++ b, fun r => List.append_assoc a b r ▸ .step _ _ _ _ _ (ha _) (hb r)⟩

/-! ### Whole-run completeness on a syntactically deterministic program

The restriction is on the program (`start.deterministic`), not on the derivation. -/

/-- **Monad-generic whole-run completeness for a deterministic program.**  For an observation
whose `emit` always succeeds, a bounded evaluator that reaches every reference value at some
fuel and keeps it at every larger fuel, and a start configuration from which every reachable
deterministic base-command evaluation passes the engine's value checks
(`EngineChecksAgreeFrom`), every reference derivation out of the syntactically deterministic
`start` and ending at a configuration the driver stops at is reproduced by an engine run, at
every sufficiently large fuel from every configuration denoting `start` to a configuration denoting
`final`, prepending runtime events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_of_deterministic_from (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    (hemit : EmitTotal obs cfgr)
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hg : EngineGuardsAgree P)
    (hchk : EngineChecksAgreeFrom (P := P) (ChoiceRecord.bot P)
              start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
              start evs final)
    (hdet : start.deterministic = true)
    (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  exact runInterp_complete_generic _ _
    (stepInterpCompleteGeneric_of_laws _ _ hemit (chooseResolves_bot _ _) hMono)
    _ _ _ ht hd (hrun.toStepEngStarEFrom hEvalComplete hg hdet hchk) hdone st

/-- **Monad-generic whole-run completeness for a deterministic program.** For an observation whose
    `emit` always succeeds, a bounded evaluator that reaches every reference value at some fuel
    and keeps it at every larger fuel, and a language where every deterministic base-command
    evaluation the reference admits passes the engine's value checks (`EngineChecksAgree`), every
    reference derivation out of a syntactically deterministic configuration and ending at a
    configuration the driver stops at is reproduced by an engine run, at every sufficiently large
    fuel, prepending runtime events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_of_deterministic (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    (hemit : EmitTotal obs cfgr)
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (hg : EngineGuardsAgree P) (hchk : EngineChecksAgree (P := P) (ChoiceRecord.bot P))
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
              start evs final)
    (hdet : start.deterministic = true)
    (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact runInterp_complete_of_deterministic_from _ _ hemit hEvalComplete hMono _ _ _ st _ hstart hg
    (hchk.toFrom _) hrun hdet hdone

/-- Whole-run completeness for a deterministic program on a class of events: for an observation
    whose `emit` succeeds on the events satisfying `Q`, a bounded evaluator that reaches every
    reference value at some fuel and keeps it at every larger fuel, and a start configuration from
    which every reachable deterministic base-command evaluation passes the engine's value checks
    (`EngineChecksAgreeFrom`), every reference derivation out of the syntactically deterministic
    `start`, ending at a configuration the driver stops at and emitting only events satisfying
    `Q`, is reproduced by an engine run at every sufficiently large fuel, prepending runtime events
    that stand for exactly the derivation's events to the trace. -/
private theorem runInterp_complete_on_of_deterministic_from (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {Q : Event P → Prop}
    (hemit : EmitTotalOn obs cfgr Q)
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hg : EngineGuardsAgree P)
    (hchk : EngineChecksAgreeFrom (P := P) (ChoiceRecord.bot P)
              start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
              start evs final)
    (hdet : start.deterministic = true)
    (hdone : Config.Done final)
    (hQ : ∀ ev ∈ evs, Q ev) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  exact runInterp_complete_on _ _
    (stepInterpCompleteGenericOn_of_laws _ _ hemit (chooseResolves_bot _ _) hMono)
    _ _ _ ht hd (hrun.toStepEngStarEFrom hEvalComplete hg hdet hchk) hdone hQ st

/-- **Monad-generic whole-run completeness for a deterministic program, on a class of events.** For
    an observation whose `emit` succeeds on the events satisfying `Q`, a bounded evaluator that
    reaches every reference value at some fuel and keeps it at every larger fuel, and a language
    where every deterministic base-command evaluation the reference admits passes the engine's
    value checks (`EngineChecksAgree`), every reference derivation out of a syntactically
    deterministic configuration, ending at a configuration the driver stops at and emitting only
    events satisfying `Q`, is reproduced by an engine run, at every sufficiently large fuel,
    prepending runtime events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_on_of_deterministic (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {Q : Event P → Prop}
    (hemit : EmitTotalOn obs cfgr Q)
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (hg : EngineGuardsAgree P) (hchk : EngineChecksAgree (P := P) (ChoiceRecord.bot P))
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
              start evs final)
    (hdet : start.deterministic = true)
    (hdone : Config.Done final)
    (hQ : ∀ ev ∈ evs, Q ev) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  exact runInterp_complete_on_of_deterministic_from _ _ hemit hEvalComplete hMono _ _ _ st _ hstart
    hg (hchk.toFrom _) hrun hdet hdone hQ

/-- **Whole-run completeness against the reference semantics, on a class of events.** For an
    observation whose `emit` succeeds on the events satisfying `Q` and a fuel-monotone bounded
    evaluator, if every reference step from a configuration a reference derivation reaches from
    `start` is an engine-realizable step under the empty choice record with the same events and
    successor (`EngineAgreesFrom`), then a reference derivation from `start` ending at a
    configuration the driver stops at and emitting only events satisfying `Q` is reproduced by an
    engine run from every configuration `istart` denoting `start` to a configuration denoting
    `final`, at every sufficiently large fuel, prepending runtime events that stand for exactly the
    derivation's events to the trace. -/
theorem runInterp_complete_on_of_agree (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {Q : Event P → Prop}
    (hemit : EmitTotalOn obs cfgr Q) (hMono : BoundedEvalMono P)
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : obs.St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := P) (ChoiceRecord.bot P) (@EvalCmdE P _ _)
      (EvalCmdEngE P (ChoiceRecord.bot P)) start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _) start evs final)
    (hdone : Config.Done final)
    (hQ : ∀ ev ∈ evs, Q ev) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  exact runInterp_complete_on _ _
    (stepInterpCompleteGenericOn_of_laws _ _ hemit (chooseResolves_bot _ _) hMono)
    _ _ _ ht hd (hrun.toStepEngParamStarE' hag) hdone hQ st

end Complete

end -- public section

end Imperative
