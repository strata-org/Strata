/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.InterpreterCFGProps
import Strata.Languages.Core.InterpreterCFGProps
import Strata.Languages.Core.InterpreterKleeneProps
import Strata.Languages.Core.InterpreterCallComplete
import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterCFG
import all Strata.Languages.Core.InterpreterKleene
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.StmtCFGCallSemantics
import all Strata.DL.Imperative.InterpreterCompleteObs
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.Languages.Core.InterpreterCallSound
import all Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.InterpreterProps
import Strata.DL.Imperative.InterpreterReplayTactics
import Strata.Languages.Core.Logic.FactoryInterp
import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.InterpreterDomainProps

/-! # The completeness and soundness theorems of the CFG and Kleene drivers apply

Two nondeterministic programs with a call, over Core's factory modeled by `Core.factoryInterp`
(`M0`):
- `cfgComplete`, `cfgSound`: the CFG `b0: init b : bool := *; call w(); if true goto b1 else b2`,
  `b1: finish`, `b2: finish`, whose callee
  `w` has the CFG body `e: finish`, run with the oracle `[ff]`; every premise of
  `Core.runCoreInterpCFG_complete_follows` (at `ReplayM`) and of the call-aware CFG soundness
  theorem `Calls.runInterpCFG_callSoundE` is discharged.  The Core soundness theorem
  `Core.runCoreInterpCFG_soundE_of_evalFactoryWF`, which has the same premises, is that theorem at
  the default call-depth limit, while completeness gives the run at every call-depth limit above
  a bound it does not name, so the generic theorem is applied at that bound;
- `kleeneComplete`, `kleeneSound`: the Kleene loop `loop { call w() }` run with the oracle
  `[tt, ff]` (one iteration, then exit); every premise of
  `Core.runCoreInterpKleene_replayComplete` and of
  `Core.runCoreInterpKleene_replay_soundE_of_evalFactoryWF` is discharged.

The Kleene run decides its loop both ways at the same store, so no observation resolves a choice
record that records its choices (`kleene_not_chooseResolves`), and the completeness theorems
stated with `ChooseResolves` do not apply to it.  `ReplayM` resolves no nonempty record at any
reader config (`replay_not_chooseResolves`).  Those theorems do apply at an observation whose
`choose` answers every recorded choice from the store and type alone: `cfgCompleteE` and
`kleeneCompleteE` discharge every premise of `Core.runCoreInterpCFG_completeE` and
`Core.runCoreInterpKleene_completeE` at `obsFF`, whose `choose` answers `ff`, on `cfgStart` and
on `choice { call w() } { call w() }`. -/

namespace CfgKleeneCompleteSanityTest

open Core Imperative

private def md : MetaData Expression := #[]

/-- Core's factory, modeled by its interpretation `Core.factoryInterp`. -/
private noncomputable def M0 : Expression.Factory :=
  ⟨Core.Factory, Core.factoryInterp, fun _ => .bool⟩

private def bId : Expression.Ident := ⟨"b", ()⟩

/-- The callee's CFG body: one block `e` that finishes. -/
def wCfg : DetCFG Expression Command :=
  { entry := "e", blocks := [("e", ⟨[], .finish md⟩)] }

/-- The callee: no formals, no spec clauses, CFG body `wCfg`. -/
def wProc : Procedure :=
  { header := { name := ⟨"w", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg wCfg }

/-- The procedure table: `"w"` resolves to `wProc`. -/
def wPi : String → Option Procedure := fun n => if n = "w" then some wProc else none

/-- The caller environment: the empty store over Core's factory. -/
def env0 : IEnv Expression := .ofStore (fun _ => none) Core.Factory

/-- The empty caller environment denotes at `M0`. -/
private theorem env0_denoting : RStore.Denoting M0 env0.store.get ∧
    env0.factory = InterpLang.rfactory M0 :=
  ⟨by simp [env0, IEnv.ofStore, RStore.Denoting, IStore.get, IStore.ofStore,
    InterpLang.writesFind?_empty], rfl⟩

/-- No name is defined in the semantic image of the empty caller environment. -/
private theorem env0_abs_none (x : Expression.Ident) : (env0.abs M0).store x = none := by
  simp [env0, IEnv.abs, IEnv.ofStore, InterpLang.absStore, IStore.get, IStore.ofStore,
    InterpLang.writesFind?_empty]

/-! ## A CFG program -/

/-- The literal `true`, the guard of the caller's conditional transfer. -/
private def ttE : Expression.Expr := .boolConst () true

/-- The literal `true` evaluates to `ttVal` on every store. -/
private theorem ttE_denote (F : Expression.Factory) (σ : SemanticStore Expression) :
    Expression.eval F σ ttE = some (HasBool.ttVal F) :=
  Lambda.LExpr.denoteEval_boolConst

/-- The engine's evaluator leaves the literal `true` unchanged at every fuel. -/
private theorem ttE_eval (n : Nat) (F : Lambda.Factory CoreLParams) (σr : RStore Expression) :
    Lambda.LExpr.eval n F σr ttE = (ttE, .value true) :=
  Lambda.eval_value_identity n F σr ttE (Lambda.isValue_const_true ..)

/-- The engine evaluates the guard `true`: it reaches the guard's reference value at fuel `0`,
    and every runtime value it commits is read as `true` (`InterpLang.boolLit?`). -/
private theorem ttE_engEval (σ : SemanticStore Expression) :
    EngEval Expression M0 σ ttE (fun _ r => InterpLang.boolLit? r = some true) :=
  ⟨fun _ _ _ hv => ⟨0, ttE, evalBounded_eq_some_iff.2 ⟨evalTypedDomain_const .., ttE_eval ..,
      typeCheckWith_const .., rfl⟩, denotes_literal ((ttE_denote M0 _).trans
        ((ttE_denote M0 _).symm.trans hv))⟩,
    fun _ _ _ _ h => (Prod.mk.inj ((ttE_eval ..).symm.trans
      (evalBounded_eq_some_iff.1 h).2.1)).1 ▸ boolLit?_boolConst () true⟩

/-- The caller CFG: block `b0` runs `init b : bool := *` and `call w()`, then branches on `true`
    to `b1`, which finishes; `b2` finishes too. -/
def gC : DetCFG Expression Command :=
  { entry := "b0",
    blocks := [("b0", ⟨[.cmd (.init bId HasBool.boolTy .nondet md), .call "w" [] md],
        .condGoto ttE "b1" "b2" md⟩),
      ("b1", ⟨[], .finish md⟩), ("b2", ⟨[], .finish md⟩)] }

/-- The start configuration: at block `b0` of `gC`, in `env0`. -/
def cfgStart : ICFGConfig String Command Expression := .atBlock gC "b0" env0

/-- The oracle-reading reference run of `cfgStart`: `init b` writes `ffVal`, the call runs the
    callee's CFG body, the guard `true` takes `b1`, and `b1` finishes; the only choice it
    resolves is `ffVal`. -/
private theorem cfgRun : ∃ evs final, ReflTransTrace
    (OracleCFGStepE (Calls.OracleCmdAt wPi 1)) (cfgStart.abs M0, [HasBool.ffVal M0]) evs
      (final, []) ∧ final.Done := by
  refine ⟨_, _, .step _ _ _ _ _ (.step_admin (.fetch rfl))
    (.step _ _ _ _ _ (.step_cmd (.inl ⟨_, rfl,
      .eval_init_nondet (v := HasBool.ffVal M0) (env0_abs_none _)
      (HasBool.boolIsValOfTy _).2 (HasBool.boolIsValOfTy _).2
      (coreEvaluator_WellFormedSemanticEvalVar _),
      .inr ⟨bId, HasBool.ffVal M0, rfl, by simp [SemanticStore.update], .inl ⟨_, _, rfl⟩⟩⟩))
    (.step _ _ _ _ _ (.step_cmd (.inr (.inr ⟨"w", wProc, [], md, _, wCfg, _, _, rfl, rfl, rfl,
        ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩,
        .step _ _ _ _ _ (.step_admin (.fetch rfl)) (.step _ _ _ _ _ (.step_admin .finish)
          (.refl _)),
        ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩, rfl, nofun,
        fun _ _ _ _ _ _ h _ => by cases h; rfl⟩)))
    (.step _ _ _ _ _ (.step_admin (.goto_true (ttE_denote _ _) (ttE_engEval _)))
    (.step _ _ _ _ _ (.step_admin (.fetch rfl))
    (.step _ _ _ _ _ (.step_admin .finish) (.refl _)))))), trivial⟩

/-- The pending-choice predicate under which `ReplayM` follows its oracle
    (`Calls.chooseFollows_replay`): the oracle tail begins with a runtime segment that
    witnesses the pending choices and passes `choose`'s type check for typed choices. -/
private def replayPending (st : ReplayState Expression) (cs : List Expression.Val) : Prop :=
  ∃ rs, rs <+: st.remaining ∧ OracleWitness M0 rs cs ∧
    OracleTyped M0 (ChoiceRecord.typed Expression) rs cs

/-- The oracle `[ff]` witnesses the choice `ffVal` and passes `choose`'s type check. -/
private theorem pending_ff : replayPending { remaining := [HasBool.ff] } [HasBool.ffVal M0] := by
  refine ⟨[HasBool.ff], List.prefix_refl _, ⟨rfl, List.forall_mem_cons.2 ⟨?_, nofun⟩⟩,
    List.forall_mem_cons.2 ⟨?_, nofun⟩⟩
  · exact ⟨InterpLangBool.denote_ff M0, Lambda.isValue_const_true ..,
      fun h => (HasBool.ttVal_ne_ffVal (P := Expression) M0 h.symm).elim, fun _ => rfl⟩
  · rintro σ ty ⟨-, hty⟩
    simp only [InterpLang.ops, replayValueOps, valueHasType, hty]
    rfl

/-- **CFG completeness applies.**  `Core.runCoreInterpCFG_complete_follows` at `ReplayM`, with
    the oracle `[ff]` and every premise discharged, reproduces `cfgRun`: the replay of
    `cfgStart` succeeds at every large enough fuel and call-depth limit, reaching a configuration
    that denotes the run's halted configuration and recording exactly the run's events. -/
theorem cfgComplete : ∃ (evs : List (Event Expression)) (final : CFGConfig String Command
      Expression) (f0 : Nat) (final' : ICFGConfig String Command Expression)
      (st' : ReplayState Expression), final'.Denotes M0 final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d → replayRun (runCoreInterpCFG wPi fuel cfgStart d) {}
        { remaining := [HasBool.ff] } = (.ok final', st'))
      ∧ (obsReplay (P := Expression)).TraceExt M0 { remaining := [HasBool.ff] } st' evs := by
  obtain ⟨evs, final, hrun, hdone⟩ := cfgRun
  obtain ⟨f0, st', final', hf, h, -, ht⟩ := runCoreInterpCFG_complete_follows obsReplay wPi {}
    (Q := fun _ => True) replayPending (fun _ _ _ _ => emitTotal_replay {} rfl _ _)
    (Calls.chooseFollows_replay {} M0) (fun _ _ _ _ _ h => h)
    (fun f _ => HasBool.boolIsValOfTy f) 1 (start := cfgStart) env0_denoting hrun hdone
    (fun _ _ => trivial) _
    pending_ff
  exact ⟨evs, final, f0, final', st', hf, h, ht⟩

/-- Every procedure of `wPi` is well-formed for call-aware soundness: it has no formals, and its
    CFG body has no commands. -/
private theorem procsOk_wPi : Calls.ProcsOk wPi := by
  intro n p h
  simp only [wPi] at h
  split at h <;> cases h
  exact ⟨by decide, nofun, fun g hg => by cases hg; exact CFG.allCmds_of_mem (by simp [wCfg])⟩

/-- Every command of the caller CFG `gC` is a well-formed call site. -/
private theorem allCmds_gC : gC.allCmds (Calls.CmdCallOk wPi) := by
  refine CFG.allCmds_of_mem fun lb hlb => ?_
  simp only [gC, List.mem_cons, List.not_mem_nil, or_false] at hlb
  rcases hlb with rfl | rfl | rfl <;> rfl

/-- The empty store over `M0` is well-formed and typed. -/
private theorem env0_callEnvOk : Calls.CallEnvOk M0 (env0.abs M0).store := by
  refine ⟨fun x v h => ?_, fun x v h => ?_⟩ <;> simp [env0_abs_none] at h

/-- **CFG soundness applies.**  The call-aware CFG soundness theorem
    `Calls.runInterpCFG_callSoundE` (of which `Core.runCoreInterpCFG_soundE_of_evalFactoryWF` is
    the instance at the default call-depth limit), with every premise discharged, turns the
    replay run of `cfgComplete` into a derivation of the call-aware CFG reference semantics
    `StepCFGExtStarE wPi` from the semantic image of `cfgStart`. -/
theorem cfgSound : ∃ (fuel d : Nat) (final' : ICFGConfig String Command Expression)
      (st' : ReplayState Expression) (revs : List (IEvent Expression)),
      replayRun (runCoreInterpCFG wPi fuel cfgStart d) {} { remaining := [HasBool.ff] }
        = (.ok final', st')
      ∧ StepCFGExtStarE wPi (cfgStart.abs M0) (revs.map (REvent.abs M0)) (final'.abs M0) := by
  obtain ⟨-, -, f0, final', st', -, h, -⟩ := cfgComplete
  have hrun := h f0 f0 (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨revs, -, hstar, -⟩ := Calls.runInterpCFG_callSoundE (obsReplay (P := Expression)) wPi M0
    procsOk_wPi
    (factoryWF_coreFactory M0 rfl) (boundedEvalSoundAt_of_evalFactoryWF M0
      evalFactoryWF_coreFactory) f0 f0 cfgStart final' {} _ st' env0_denoting
    ⟨env0_callEnvOk, allCmds_gC, rfl⟩ hrun
  exact ⟨f0, f0, final', st', revs, hrun, hstar⟩

/-! ## A Kleene program -/

/-- The start configuration: `loop { call w() }` in `env0`. -/
def kStart : IKleeneConfig Expression Command := .stmt (.loop (.cmd (.call "w" [] md))) env0

/-- The call `call w()` from any caller store `σ`: the callee's CFG body halts at once and the
    call leaves the store unchanged. -/
private theorem wCallArm (σ : SemanticStore Expression) (o : List Expression.Val) :
    Calls.OracleCmdAt wPi 1 M0 σ (.call "w" [] md) σ [] o o :=
  .inr (.inr ⟨"w", wProc, [], md, _, wCfg, _, _, rfl, rfl, rfl,
    ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩,
    .step _ _ _ _ _ (.step_admin (.fetch rfl)) (.step _ _ _ _ _ (.step_admin .finish) (.refl _)),
    ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩, rfl, nofun,
    fun _ _ _ _ _ _ h _ => by cases h; rfl⟩)

/-- The oracle-reading reference run of `kStart`: the loop reads `ttVal` and runs its body (the
    call) once in its own block, then reads `ffVal` and stops; the choices it resolves are
    `[ttVal, ffVal]`, and the loop decides both from the store of `env0`, which the iteration
    leaves unchanged. -/
private theorem kRun : ∃ evs, ReflTransTrace (OracleKleeneStepE (Calls.OracleCmdAt wPi 1))
    (kStart.abs M0, [HasBool.ttVal M0, HasBool.ffVal M0]) evs
    (.terminal { env0.abs M0 with
      store := projectStore (env0.abs M0).store (env0.abs M0).store }, [])
    ∧ projectStore (env0.abs M0).store (env0.abs M0).store = (env0.abs M0).store :=
  ⟨_, .step _ _ _ _ _ .step_loop_step
    (.step _ _ _ _ _ (.step_seq_inner (.step_block_body (.step_cmd (wCallArm _ _))))
    (.step _ _ _ _ _ (.step_seq_inner .step_block_done)
    (.step _ _ _ _ _ .step_seq_done
    (.step _ _ _ _ _ .step_loop_zero (.refl _))))),
    funext fun x => by simp [projectStore, env0_abs_none]⟩

/-- The oracle `[tt, ff]` witnesses the choices `[ttVal, ffVal]` and passes `choose`'s type
    check. -/
private theorem pending_tt_ff :
    replayPending { remaining := [HasBool.tt, HasBool.ff] }
      [HasBool.ttVal M0, HasBool.ffVal M0] := by
  refine ⟨[HasBool.tt, HasBool.ff], List.prefix_refl _, ⟨rfl, ?_⟩, ?_⟩
  · refine List.forall_mem_cons.2 ⟨?_, List.forall_mem_cons.2 ⟨?_, nofun⟩⟩
    · exact ⟨InterpLangBool.denote_tt M0, Lambda.isValue_const_true .., fun _ => rfl,
        fun h => (HasBool.ttVal_ne_ffVal (P := Expression) M0 h).elim⟩
    · exact ⟨InterpLangBool.denote_ff M0, Lambda.isValue_const_true ..,
        fun h => (HasBool.ttVal_ne_ffVal (P := Expression) M0 h.symm).elim, fun _ => rfl⟩
  · refine List.forall_mem_cons.2 ⟨?_, List.forall_mem_cons.2 ⟨?_, nofun⟩⟩
    all_goals rintro σ ty ⟨-, hty⟩
    all_goals simp only [InterpLang.ops, replayValueOps, valueHasType, hty]
    all_goals rfl

/-- **Kleene completeness applies.**  `Core.runCoreInterpKleene_replayComplete`, with the oracle
    `[tt, ff]` and every premise discharged, reproduces `kRun`: the replay of `kStart` succeeds at
    every large enough fuel and call-depth limit, reaching a configuration that stands for the
    run's terminal configuration and recording exactly the run's events. -/
theorem kleeneComplete : ∃ (evs : List (Event Expression))
      (final : KleeneConfig Expression Command) (f0 : Nat)
      (final' : IKleeneConfig Expression Command) (st' : ReplayState Expression),
      final'.abs M0 = final ∧ final'.Denoting M0 ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d → replayRun (runCoreInterpKleene wPi fuel kStart d) {}
        { remaining := [HasBool.tt, HasBool.ff] } = (.ok final', st'))
      ∧ (obsReplay (P := Expression)).TraceExt M0 { remaining := [HasBool.tt, HasBool.ff] } st'
        evs := by
  obtain ⟨evs, hrun, -⟩ := kRun
  obtain ⟨rs, hpre, hrs, hty⟩ := pending_tt_ff
  obtain ⟨f0, final', st', hf, hd, h, ht⟩ := runCoreInterpKleene_replayComplete wPi {} rfl 1
    (start := kStart) env0_denoting trivial hrun ⟨_, rfl⟩ _ rs hpre hrs hty
  exact ⟨evs, _, f0, final', st', hf, hd, h, ht⟩

/-- **Kleene soundness applies.**  `Core.runCoreInterpKleene_replay_soundE_of_evalFactoryWF`,
    with every premise discharged, turns the replay run of `kleeneComplete` into a derivation of
    the call-aware Kleene reference semantics `StepKleeneExtStarE wPi` from the semantic image of
    `kStart`. -/
theorem kleeneSound : ∃ (fuel d : Nat) (final' : IKleeneConfig Expression Command)
      (st' : ReplayState Expression) (revs : List (IEvent Expression)),
      replayRun (runCoreInterpKleene wPi fuel kStart d) {}
        { remaining := [HasBool.tt, HasBool.ff] } = (.ok final', st')
      ∧ StepKleeneExtStarE wPi (kStart.abs M0) (revs.map (REvent.abs M0)) (final'.abs M0) := by
  obtain ⟨-, -, f0, final', st', -, -, h, -⟩ := kleeneComplete
  have hrun := h f0 f0 (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨revs, hstar, -⟩ := runCoreInterpKleene_replay_soundE_of_evalFactoryWF wPi f0 f0 kStart
    final' {} _ st' procsOk_wPi hrun M0 evalFactoryWF_coreFactory (factoryWF_coreFactory M0 rfl)
    env0_denoting ⟨env0_callEnvOk, rfl⟩ trivial
  exact ⟨f0, f0, final', st', revs, hrun, hstar⟩

/-! ## Where `ChooseResolves` fails -/

/-- `kRun` decides its loop as `ttVal` and then as `ffVal`, both at the store of `env0` (`kRun`'s
    second conjunct), so a choice record that records `kRun`'s choices (`StepKleeneEngE`'s
    `step_loop` premises) allows both Booleans at that store.  No observation resolves such a
    record at any reader config, so `ChooseResolves`, the premise of
    `Core.runCoreInterpKleene_completeE`, fails for it. -/
theorem kleene_not_chooseResolves {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (obs : InterpObs Expression m) (cfgr : obs.Cfg) (st : obs.St)
    {R : ChoiceRecord Expression}
    (htt : R M0 (env0.abs M0).store HasBool.boolTy (HasBool.ttVal M0))
    (hff : R M0 (env0.abs M0).store HasBool.boolTy (HasBool.ffVal M0)) :
    ¬ ChooseResolves obs cfgr M0 R :=
  not_chooseResolves_of_tt_ff obs cfgr (storeDenotes_absStore env0_denoting.1) htt hff st

/-- The free variable `b`, a runtime expression that is not a value. -/
private def bE : Expression.Expr := .fvar () bId none

/-- **`ReplayM` resolves no nonempty choice record.**  Whatever the reader config, a replay state
    whose oracle tail starts with the non-value `b` makes `choose` throw, so `ChooseResolves`
    fails at `ReplayM` for every record that allows some value at a denoted store. -/
theorem replay_not_chooseResolves (cfg : ReplayCfg Expression) {R : ChoiceRecord Expression}
    {σr : RStore Expression} {σ : SemanticStore Expression} {ty : Expression.Ty}
    {v : Expression.Val} (hσ : StoreDenotes M0 σr σ) (hR : R M0 σ ty v) :
    ¬ ChooseResolves (obsReplay (P := Expression)) cfg M0 R := fun hc => by
  obtain ⟨r, st', h, -⟩ := hc σr σ ty v { remaining := [bE] } hσ hR
  have hbv : Lambda.LExpr.isValue (InterpLang.rfactory M0) bE = false := by
    rw [Lambda.LExpr.isValue.eq_def]; rfl
  simp only [obsReplay] at h
  eff_inv [InterpLang.ops, replayValueOps, hbv]
  exact Bool.false_ne_true ‹_›

/-! ## The `ChooseResolves` theorems, at an observation whose `choose` answers `ff`

`ChooseResolves` holds at an observation whose `choose` is a function of the store and type that
answers every recorded choice.  `FFM` is such a monad for the record `ffRecord` (the Boolean
`ffVal` at every store): its `choose` returns the literal `ff` at `boolTy`.  With it, every
premise of `Core.runCoreInterpCFG_completeE` is discharged on `cfgStart`, and every premise of
`Core.runCoreInterpKleene_completeE` on the Kleene program `choice { call w() } { call w() }`,
whose choice takes the right arm. -/

/-- The choice record that allows exactly `ffVal`, at `boolTy`, at every store. -/
def ffRecord : ChoiceRecord Expression := fun f _ ty v => ty = HasBool.boolTy ∧ v = HasBool.ffVal f

/-- A monad that fails with a `StopReason` and records the emitted events. -/
abbrev FFM : Type → Type := ExceptT StopReason (StateM (List (IEvent Expression)))

/-- `choose` returns the literal `ff` when it is a value of the requested type, and fails
    otherwise; `emit` records the event. -/
instance : InterpEffects Expression FFM where
  choose factory _ ty :=
    if (InterpLang.ops (P := Expression)).isValue factory HasBool.ff &&
        (InterpLang.ops (P := Expression)).hasType factory HasBool.ff ty then pure HasBool.ff
    else throw .illTypedValue
  emit ev := ExceptT.lift (modify (ev :: ·))

/-- The observation of `FFM`: no reader config, the recorded events as state and trace. -/
def obsFF : InterpObs Expression FFM where
  Cfg := Unit
  St := List (IEvent Expression)
  run x _ st := StateT.run (ExceptT.run x) st
  trace st := st
  run_pure _ _ _ := rfl
  run_throw _ _ _ := rfl
  run_bind ma f _ st := by
    simp only [ExceptT.run_bind, StateT.run_bind]
    rcases StateT.run (ExceptT.run ma) st with ⟨_ | _, _⟩ <;> rfl
  emit_trace _ _ _ _ _ h := (Prod.mk.inj h).2.symm
  choose_sound factory _ ty _ _ v _ h := by
    by_cases hc : ((InterpLang.ops (P := Expression)).isValue factory HasBool.ff &&
        (InterpLang.ops (P := Expression)).hasType factory HasBool.ff ty) = true
    · simp only [InterpEffects.choose, hc] at h
      obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj h
      exact ⟨Bool.and_eq_true_iff.1 hc, rfl⟩
    · simp only [InterpEffects.choose, hc] at h
      cases h
  branch_stuck _ _ _ _ _ := rfl

/-- `FFM`'s `emit` always succeeds. -/
private theorem emitTotal_ff (cfgr : obsFF.Cfg) : EmitTotal obsFF cfgr := fun _ _ => ⟨_, rfl⟩

/-- `FFM` resolves `ffRecord` at `M0`, at every reader config: `choose` at `boolTy` returns the
    literal `ff`, which denotes `ffVal`. -/
private theorem chooseResolves_ff (cfgr : obsFF.Cfg) : ChooseResolves obsFF cfgr M0 ffRecord := by
  rintro _ _ _ _ st - ⟨rfl, rfl⟩
  have hc : ((InterpLang.ops (P := Expression)).isValue (InterpLang.rfactory M0) HasBool.ff &&
      (InterpLang.ops (P := Expression)).hasType (InterpLang.rfactory M0) HasBool.ff
        HasBool.boolTy) = true := by
    simp only [InterpLang.ops, replayValueOps, valueHasType, HasBool.boolTy,
      Lambda.LTy.toMonoType?, Bool.and_eq_true]
    exact ⟨Lambda.isValue_const_true .., rfl⟩
  refine ⟨HasBool.ff, st, by simp only [obsFF, InterpEffects.choose, hc]; rfl,
    InterpLangBool.denote_ff M0,
    fun h => (HasBool.ttVal_ne_ffVal (P := Expression) M0 h.symm).elim, fun _ => rfl, rfl⟩

/-- The engine-realizable run of `cfgStart` with its choice recorded in `ffRecord`: `init b`
    writes `ffVal`, the call runs the callee's CFG body, the guard `true` takes `b1`, and `b1`
    finishes. -/
private theorem cfgRunEng : ∃ evs final, StepCFGEngStarE Expression
    (Calls.EvalCommandEngAtE wPi ffRecord 1) (cfgStart.abs M0) evs final ∧ final.Done :=
  ⟨_, _, .step _ _ _ _ _ (.fetch rfl)
    (.step _ _ _ _ _ (.step_cmd (.inl ⟨_, rfl,
      .eval_init_nondet (v := HasBool.ffVal M0) (env0_abs_none _) ⟨rfl, rfl⟩
      (HasBool.boolIsValOfTy _).2 (coreEvaluator_WellFormedSemanticEvalVar _)⟩))
    (.step _ _ _ _ _ (.step_cmd (.inr ⟨"w", wProc, [], md, _, _, _, rfl, rfl,
        ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩,
        ⟨_, .step _ _ _ _ _ (.fetch rfl) (.step _ _ _ _ _ .finish (.refl _)), rfl⟩,
        ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩, rfl, nofun,
        fun _ _ _ _ _ _ h _ => by cases h; rfl⟩))
    (.step _ _ _ _ _ (.goto_true (ttE_denote _ _) (ttE_engEval _))
    (.step _ _ _ _ _ (.fetch rfl)
    (.step _ _ _ _ _ .finish (.refl _)))))), trivial⟩

/-- **`Core.runCoreInterpCFG_completeE` applies.**  At `obsFF`, with every premise discharged
    (`EmitTotal`, `ChooseResolves` of `ffRecord`, the engine's guard evaluation in the
    `StepCFGEngE` derivation), the run of `cfgStart` is reproduced at every large enough fuel
    and call-depth limit. -/
theorem cfgCompleteE : ∃ (evs : List (Event Expression))
      (final : CFGConfig String Command Expression) (f0 : Nat) (st' : obsFF.St)
      (final' : ICFGConfig String Command Expression), final'.Denotes M0 final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obsFF.run (runCoreInterpCFG wPi fuel cfgStart d) () [] = (.ok final', st'))
      ∧ obsFF.TraceExt M0 [] st' evs := by
  obtain ⟨evs, final, hstar, hdone⟩ := cfgRunEng
  obtain ⟨f0, final', st', ha, hd, h, ht⟩ := runCoreInterpCFG_completeE obsFF wPi M0 ffRecord 1
    () (emitTotal_ff ()) (chooseResolves_ff ()) cfgStart final evs env0_denoting hstar hdone []
  exact ⟨evs, final, f0, st', final', ⟨hd, ha⟩, h, ht⟩

/-- The Kleene start configuration: `choice { call w() } { call w() }` in `env0`. -/
def kChoiceStart : IKleeneConfig Expression Command :=
  .stmt (.choice (.cmd (.call "w" [] md)) (.cmd (.call "w" [] md))) env0

/-- **`Core.runCoreInterpKleene_completeE` applies.**  At `obsFF`, with every premise discharged
    (`EmitTotal`, `ChooseResolves` of `ffRecord`), the engine-realizable run of `kChoiceStart`
    that takes the right arm (the choice `ffVal`) and runs the call is reproduced at every large
    enough fuel and call-depth limit. -/
theorem kleeneCompleteE : ∃ (evs : List (Event Expression))
      (final : KleeneConfig Expression Command) (f0 : Nat)
      (final' : IKleeneConfig Expression Command) (st' : obsFF.St),
      final'.abs M0 = final ∧ final'.Denoting M0 ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obsFF.run (runCoreInterpKleene wPi fuel kChoiceStart d) () [] = (.ok final', st'))
      ∧ obsFF.TraceExt M0 [] st' evs := by
  have hcall : StepKleeneEngStarE ffRecord (Calls.EvalCommandEngAtE wPi ffRecord 1)
      (.stmt (.cmd (.call "w" [] md)) (env0.abs M0)) _ _ :=
    .step _ _ _ _ _ (.step_cmd (Or.inr ⟨"w", wProc, [], md, _, _, _, rfl, rfl,
      ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩,
      ⟨_, .step _ _ _ _ _ (.fetch rfl) (.step _ _ _ _ _ .finish (.refl _)), rfl⟩,
      ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩, rfl, nofun,
      fun _ _ _ _ _ _ h _ => by cases h; rfl⟩)) (.refl _)
  have hstar : StepKleeneEngStarE ffRecord (Calls.EvalCommandEngAtE wPi ffRecord 1)
      (kChoiceStart.abs M0) _ _ :=
    .step _ _ _ _ _ (.step_choice (v := HasBool.ffVal M0) ⟨rfl, rfl⟩ (.inr rfl))
      (by rw [ite_self]; exact hcall)
  obtain ⟨f0, final', st', hf, hd, h, ht⟩ := runCoreInterpKleene_completeE obsFF wPi M0 ffRecord
    1 () (emitTotal_ff ()) (chooseResolves_ff ()) kChoiceStart _ _ env0_denoting trivial hstar
    ⟨_, rfl⟩ []
  exact ⟨_, _, f0, final', st', hf, hd, h, ht⟩

end CfgKleeneCompleteSanityTest
