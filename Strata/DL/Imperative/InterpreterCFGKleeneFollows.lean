/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCFGCallComplete
public import Strata.DL.Imperative.InterpreterKleeneComplete
public import Strata.DL.Imperative.InterpreterCallCompleteProps
import all Strata.DL.Imperative.InterpreterCallCompleteProps
import all Strata.DL.Imperative.InterpreterKleeneCall
import all Strata.DL.Imperative.InterpreterCFGCallSound
import all Strata.DL.Imperative.InterpreterObs
import Strata.DL.Imperative.InterpreterProps

/-! # Call-aware completeness of the CFG and Kleene drivers along an oracle

The call-aware CFG and Kleene drivers reproduce every reference run whose nondeterministic
choices are read off an oracle, at every large enough fuel and call-depth limit.  The run's
choices are arbitrary: a nondeterministic command, a Kleene `.choice` or a Kleene `.loop` may be
resolved differently each time it is reached, from the same store or not, and inside callee bodies
at any depth.  The observation only has to follow the pending choices (`ChooseFollows`), which
`ReplayM` does from an oracle whose prefix witnesses them (`chooseFollows_replay`).

The reference runs are the oracle-reading CFG relation `OracleCFGStepE` and Kleene relation
`OracleKleeneStepE` over the oracle-reading call-aware command relation `OracleCmdAt π n`, the
relation the structured engine's choice sequences (`RunChoices`) are stated with.

Key theorems:
- `not_chooseResolves_of_tt_ff`: no observation resolves (`ChooseResolves`) a choice record that
  allows both Booleans at one store, so the completeness theorems stated with `ChooseResolves`
  do not cover a run that resolves one Boolean choice both ways from the same store;
- `runInterpCFG_callComplete_follows`, `runInterpKleene_callComplete_follows`: monad-generic
  whole-run completeness along an oracle;
- `cfg_replayRun_complete`, `kleene_replayRun_complete`: their `ReplayM` instances. -/

namespace Imperative

public section

section Obstruction

variable {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
  {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- **No observation resolves a record that allows both Booleans at one store.**  If the choice
    record `R` allows both `ttVal` and `ffVal` as the Boolean chosen at a semantic store `σ` that
    a runtime store `σr` denotes, and the observation has a state `st`, then no reader config
    makes the observation resolve `R` (`ChooseResolves`): from `st`, `choose` returns a single
    runtime value, which would have to be read both as `true` and as `false`
    (`InterpLang.boolLit?`).  A run that resolves one
    nondeterministic Boolean both ways from the same store, such as a Kleene `.loop` whose body
    leaves the store unchanged and which then stops, is therefore covered by the completeness
    theorems along an oracle below and not by those stated with `ChooseResolves`. -/
theorem not_chooseResolves_of_tt_ff (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {σr : RStore P} {σ : SemanticStore P} (hσ : StoreDenotes F σr σ)
    (htt : R F σ HasBool.boolTy (HasBool.ttVal F)) (hff : R F σ HasBool.boolTy (HasBool.ffVal F))
    (st : obs.St) : ¬ ChooseResolves obs cfgr F R := fun h => by
  obtain ⟨r, _, h1, -, hrt, -⟩ := h σr σ _ _ st hσ htt
  obtain ⟨r', _, h2, -, -, hrf, -⟩ := h σr σ _ _ st hσ hff
  obtain rfl : r = r' := Except.ok.inj (Prod.mk.inj (h1.symm.trans h2)).1
  exact nomatch (hrt rfl).symm.trans (hrf rfl)

end Obstruction

namespace Calls

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m] [MonadExcept StopReason m]

omit [HasFvars P] [LawfulMonad m] in
/-- A command step of an oracle-reading call-aware run that `stepCmd π i j` performs from the
    environment with store `σ` at the runtime factory of `F`, reaching the store `σi`, is a run of
    the store-stepper `StepCmdM.toStore (stepCmd π i)` (`cfgStepCmd π i`, `stepKleeneCmd π i`)
    reaching `σi`. -/
private theorem storeStep_of_stepInterp (obs : InterpObs P m) (cfgr : obs.Cfg) {F : P.Factory}
    (π : String → Option (Procedure P (CmdExt P) Hdr)) {i j : Nat} {σ σi : IStore P}
    {c : CmdExt P} {st st' : obs.St}
    (h : obs.run (stepInterp (callStepOf (m := m) π i j) j (.stmt (.cmd c)
      ⟨σ, InterpLang.rfactory F⟩)) cfgr st
        = (.ok (.terminal { (⟨σ, InterpLang.rfactory F⟩ : IEnv P) with store := σi }), st')) :
    obs.run (StepCmdM.toStore (stepCmd π i) j (InterpLang.rfactory F) σ c) cfgr st
      = (.ok σi, st') := by
  simp only [stepInterp_stmt_cmd, callStepOf] at h
  simp [obs.run_bind, h, IConfig.getEnv, obs.run_pure, -bind_pure_comp]

/-- **Call-aware completeness of the CFG driver along an oracle.**  An oracle-reading CFG run over
    the call-aware command relation `OracleCmdAt π n` (calls nested at most `n` deep), from the
    semantic image (`ICFGConfig.abs`) of a configuration `start` that denotes at `F`, with oracle
    `o`, to a halted `y.1` with oracle `y.2`, whose events satisfy `Q`, is reproduced, from every
    state `st` with `Pending st o`, by `runInterpCFG (cfgStepCmd π d)` from `start` at every large
    enough fuel and call-depth limit `d`, reaching a configuration that denotes `y.1`, leaving
    `Pending st' y.2` and emitting runtime events whose semantic images are exactly the run's
    events.

    Hypotheses: `emit` succeeds on the events satisfying `Q` (`hemit`); `choose` follows the
    pending choices that `R` allows (`hf`); the bounded evaluator is fuel-monotone (`hMono`);
    every engine-realizable base-command step with typed choices (`EvalCmdEngE` at
    `ChoiceRecord.typed`) is one with choices in `R` (`hlift`); `R` allows `tt` and `ff` as
    Booleans (`hbool`). -/
theorem runInterpCFG_callComplete_follows {l : Type} [BEq l] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    (n : Nat) {start : ICFGConfig l (CmdExt P) P} {o : List P.Val}
    {y : CFGConfig l (CmdExt P) P × List P.Val} {evs : List (Event P)}
    (hden : start.Denoting F)
    (hrun : ReflTransTrace (OracleCFGStepE (OracleCmdAt π n)) (start.abs F, o) evs y)
    (hdone : y.1.Done) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st o) :
    ∃ f0 st', ∃ y1 : ICFGConfig l (CmdExt P) P, y1.Denotes F y.1 ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runInterpCFG (cfgStepCmd π d) fuel start) cfgr st = (.ok y1, st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs :=
  (runInterpCFG_follows_fam obs cfgr F Pending (Q := Q) (E := OracleCmdAt π n)
    (fun d _ => cfgStepCmd π d)
    (fun σ c σ' evs o o' hσ hc hq st hst =>
      (oracleCmdAt_follows obs cfgr Pending π hemit hf hMono hlift hbool n
        ⟨σ, InterpLang.rfactory F⟩ c σ' evs o o' ⟨hσ, rfl⟩ hc hq st hst).imp
        fun _ ⟨σi, s', hσi, hdi, hs, hp, ht⟩ => ⟨s', σi, hσi, hdi, fun i _ k hi _ hk =>
          storeStep_of_stepInterp obs cfgr π (hs i k k hi hk hk), hp, ht⟩)
    hMono hden hrun hdone hq st hst).imp
    fun _ ⟨st', y1, hy, h, hp, ht⟩ => ⟨st', y1, hy, fun fuel d hfu hd => h d fuel fuel hd hfu hfu,
      hp, ht⟩

/-- **Call-aware completeness of the Kleene driver along an oracle.**  An oracle-reading Kleene
    run over the call-aware command relation `OracleCmdAt π n` (calls nested at most `n` deep),
    from the semantic image (`IKleeneConfig.abs`) of a tracked (`IKleeneConfig.Tracked`)
    configuration `start` that denotes at `F`, with oracle `o`, to a terminal `y.1` with oracle
    `y.2`, whose events satisfy `Q`, is reproduced, from every state `st` with `Pending st o`, by
    `runCallInterpKleene π` from `start` at every large enough fuel and call-depth limit, reaching
    a configuration that denotes at `F` and stands for `y.1`, leaving `Pending st' y.2` and
    emitting runtime events whose semantic images are exactly the run's events.

    Hypotheses: `emit` succeeds on the events satisfying `Q` (`hemit`); `choose` follows the
    pending choices that `R` allows (`hf`); the bounded evaluator is fuel-monotone (`hMono`);
    every engine-realizable base-command step with typed choices (`EvalCmdEngE` at
    `ChoiceRecord.typed`) is one with choices in `R` (`hlift`); `R` allows `tt` and `ff` as
    Booleans (`hbool`). -/
theorem runInterpKleene_callComplete_follows (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    (n : Nat) {start : IKleeneConfig P (CmdExt P)} {o : List P.Val}
    {y : KleeneConfig P (CmdExt P) × List P.Val} {evs : List (Event P)}
    (hd : start.Denoting F) (ht : start.Tracked)
    (hrun : ReflTransTrace (OracleKleeneStepE (OracleCmdAt π n)) (start.abs F, o) evs y)
    (hdone : ∃ e, y.1 = .terminal e) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St)
    (hst : Pending st o) :
    ∃ (f0 : Nat) (final' : IKleeneConfig P (CmdExt P)) (st' : obs.St), final'.abs F = y.1 ∧
      final'.Denoting F ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCallInterpKleene π fuel start d) cfgr st = (.ok final', st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs :=
  (runInterpKleene_follows_fam obs cfgr F R Pending (Q := Q) (E := OracleCmdAt π n)
    (fun d => stepKleeneCmd π d) hf hbool
    (fun σ c σ' evs o o' hσ hc hq st hst =>
      (oracleCmdAt_follows obs cfgr Pending π hemit hf hMono hlift hbool n
        ⟨σ, InterpLang.rfactory F⟩ c σ' evs o o' ⟨hσ, rfl⟩ hc hq st hst).imp
        fun _ ⟨σi, s', hσi, hdi, hs, hp, ht⟩ => ⟨σi, s', hσi, hdi, fun i k hi hk =>
          storeStep_of_stepInterp obs cfgr π (hs i k k hi hk hk), hp, ht⟩)
    (oracleCmdAt_defines π n) hd ht hrun hdone hq st hst).imp
    fun _ ⟨c, s, hc, hdc, h, hp, ht⟩ => ⟨c, s, hc, hdc, fun fuel d hfu hd => h d fuel hd hfu,
      hp, ht⟩

/-- **Call-aware `ReplayM` completeness of the CFG driver**, nondeterministic runs included.  If
    an oracle-reading CFG run over `OracleCmdAt π n` from the semantic image of a configuration
    `start` that denotes at `F` reads the choices `cs` and halts at `final` (oracle `cs`
    consumed), then from every replay state whose oracle tail begins with a runtime segment `rs`
    that witnesses `cs` (`OracleWitness`) and passes `choose`'s type check (`OracleTyped`), under
    every config whose stop hook is off, `runInterpCFG (cfgStepCmd π d)` from `start` reaches a
    configuration denoting `final` at every large enough fuel and call-depth limit `d`,
    prepending runtime events denoting exactly the run's events to the trace.

    Hypothesis: the bounded evaluator is fuel-monotone (`hMono`). -/
theorem cfg_replayRun_complete {l : Type} [BEq l]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfg : ReplayCfg P) {F : P.Factory}
    (hcfg : cfg.interruptOn = fun _ => none) (hMono : BoundedEvalMono P) (n : Nat)
    {start : ICFGConfig l (CmdExt P) P} {final : CFGConfig l (CmdExt P) P}
    {evs : List (Event P)} {cs : List P.Val} (hden : start.Denoting F)
    (hrun : ReflTransTrace (OracleCFGStepE (OracleCmdAt π n)) (start.abs F, cs) evs (final, []))
    (hdone : final.Done) (st : ReplayState P) (rs : List P.Expr)
    (hpre : rs <+: st.remaining) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed P) rs cs) :
    ∃ f0 st', ∃ final' : ICFGConfig l (CmdExt P) P, final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        replayRun (runInterpCFG (cfgStepCmd π d) fuel start) cfg st = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs :=
  (runInterpCFG_callComplete_follows obsReplay π cfg (Q := fun _ => True) _
    (fun _ _ _ _ => emitTotal_replay cfg hcfg _ _) (chooseFollows_replay cfg F) hMono
    (fun _ _ _ _ _ h => h) (fun f _ => HasBool.boolIsValOfTy f) n hden hrun hdone
    (fun _ _ => trivial) st ⟨rs, hpre, hrs, hty⟩).imp
    fun _ ⟨st', y1, hy, h, _, ht⟩ => ⟨st', y1, hy, h, ht⟩

/-- **Call-aware `ReplayM` completeness of the Kleene driver**, nondeterministic runs included.
    If an oracle-reading Kleene run over `OracleCmdAt π n` from the semantic image of a tracked
    configuration `start` that denotes at `F` reads the choices `cs` and reaches the terminal
    configuration `final` (oracle `cs` consumed), then from every replay state whose oracle tail
    begins with a runtime segment `rs` that witnesses `cs` (`OracleWitness`) and passes `choose`'s
    type check (`OracleTyped`), under every config whose stop hook is off,
    `runCallInterpKleene π` from `start` reaches a configuration that denotes at `F` and stands
    for `final` at every large enough fuel and call-depth limit, prepending runtime events
    denoting exactly the run's events to the trace.

    Hypothesis: the bounded evaluator is fuel-monotone (`hMono`). -/
theorem kleene_replayRun_complete
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfg : ReplayCfg P) {F : P.Factory}
    (hcfg : cfg.interruptOn = fun _ => none) (hMono : BoundedEvalMono P) (n : Nat)
    {start : IKleeneConfig P (CmdExt P)} {final : KleeneConfig P (CmdExt P)}
    {evs : List (Event P)} {cs : List P.Val} (hd : start.Denoting F) (ht : start.Tracked)
    (hrun : ReflTransTrace (OracleKleeneStepE (OracleCmdAt π n)) (start.abs F, cs) evs
      (final, []))
    (hdone : ∃ e, final = .terminal e) (st : ReplayState P) (rs : List P.Expr)
    (hpre : rs <+: st.remaining) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed P) rs cs) :
    ∃ (f0 : Nat) (final' : IKleeneConfig P (CmdExt P)) (st' : ReplayState P),
      final'.abs F = final ∧ final'.Denoting F ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        replayRun (runCallInterpKleene π fuel start d) cfg st = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs :=
  (runInterpKleene_callComplete_follows obsReplay π cfg (Q := fun _ => True) _
    (fun _ _ _ _ => emitTotal_replay cfg hcfg _ _) (chooseFollows_replay cfg F) hMono
    (fun _ _ _ _ _ h => h) (fun f _ => HasBool.boolIsValOfTy f) n hd ht hrun hdone
    (fun _ _ => trivial) st ⟨rs, hpre, hrs, hty⟩).imp
    fun _ ⟨c, s, hc, hdc, h, _, ht⟩ => ⟨c, s, hc, hdc, h, ht⟩

end Calls

end -- public section

end Imperative
