/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterCallInterrupt
import all Strata.DL.Imperative.InterpreterCompleteGeneric
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.StmtCFGCallSemantics
import all Strata.DL.Imperative.InterpreterCFG
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
public import Strata.DL.Imperative.InterpreterObsProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterCallProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps

/-! # Call-aware replay completeness for reference runs

A reference run of the call-aware semantics that emits a failing assert is reproduced by
replaying its counterexample, when the counterexample's oracle begins with the run's choice
sequence (`RunChoices`).

Key theorems:
- `call_runCallInterp_follows_prefix`, `call_runCallInterp_complete_follows`: monad-generic
  whole-run completeness along a run's choice sequence (`ChooseFollows`), up to a prefix and on
  runs ending at a configuration the driver stops at;
- `call_runCallInterp_complete_follows_chk`: the same from a premise on reference evaluations;
- `chooseFollows_replay`, `call_replayRun_complete`: `ReplayM` follows an oracle whose prefix
  witnesses the choices (`OracleWitness`) and passes its type check (`OracleTyped`), and whole-run
  `ReplayM` completeness, nondeterministic runs included;
- `call_replayComplete`: replay completeness for `CmdExt P`, from a reference run emitting an
  event on which the semantic failure predicate `assertFailureE` holds.
- `runChoices_nil_of_deterministic`: a deterministic program's runs resolve no choice.
- `runChoices_of_stepStmtExtStarE`: every reference run has a choice sequence. -/

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp

public section

namespace Calls

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-! ## Steps of an oracle-reading run -/

omit [HasFvars P] [HasOldIdent P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- An oracle-reading step of the call-aware semantics is an `OracleStepParamE R` step when `R`
    allows `tt` and `ff` as Booleans. -/
private theorem OracleStepE.toParam {R : ChoiceRecord P} {E : OracleCmdRel P}
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    {x y : Config P (CmdExt P) × List P.Val} {evs : List (Event P)}
    (h : OracleStepE E x evs y) : OracleStepParamE R E x evs y := by
  induction h <;> constructor <;> first
    | assumption
    | exact (hbool _ _).1
    | exact (hbool _ _).2

/-! ## Well-formed runtime events -/

/-- A runtime event is *well formed* under the factory `F` when it carries the runtime factory of
    `F` and its store denotes under `F`, as every event the interpreter emits from a denoting
    configuration does. -/
@[expose] def EvGood (F : P.Factory) : IEvent P → Prop
  | .assert a | .assume a | .cover a =>
    a.factory = InterpLang.rfactory F ∧ RStore.Denoting F a.store

/-- `emit` succeeds on every well-formed runtime event whose image under `F` satisfies `Q`. -/
private def EmitGoodOn {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (obs : InterpObs P m) (cfgr : obs.Cfg) (F : P.Factory) (Q : Event P → Prop) : Prop :=
  ∀ (ev : IEvent P) (st : obs.St), EvGood F ev → Q (ev.abs F) →
    ∃ st', obs.run (InterpEffects.emit (P := P) ev) cfgr st = (.ok ⟨⟩, st')

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
  [HasOldIdent P] in
/-- The specification-check events of a call at the runtime factory of `F` from a denoting store
    are well formed. -/
private theorem evGood_rDefault {F : P.Factory} {σ : RStore P} (hd : RStore.Denoting F σ)
    (checks : ListMap String (Check P)) :
    ∀ ev ∈ rDefaultAssertEvents (InterpLang.rfactory F) σ checks, EvGood F ev := by
  simp only [rDefaultAssertEvents, List.mem_filterMap]
  rintro _ ⟨_, -, h⟩
  split at h <;> cases h
  exact ⟨rfl, hd⟩

/-! ## Following the choice sequence of a run, over any observation -/

section Follows

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m] (obs : InterpObs P m) (cfgr : obs.Cfg)
  (Pending : obs.St → List P.Val → Prop)

omit [LawfulMonad m] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- Emitting well-formed events that satisfy `Q` succeeds, keeps the pending choices and prepends
    the events, reversed, to the trace, when `emit` succeeds on such events. -/
private theorem follows_forM_emitG {F : P.Factory} {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitGoodOn obs cfgr F Q) (hf : ChooseFollows obs cfgr F R Pending) (o : List P.Val) :
    ∀ (evs : List (IEvent P)), (∀ ev ∈ evs, EvGood F ev ∧ Q (ev.abs F)) → ∀ st, Pending st o →
      ∃ st', obs.run (evs.forM (InterpEffects.emit (P := P))) cfgr st = (.ok ⟨⟩, st')
        ∧ Pending st' o ∧ obs.trace st' = evs.reverse ++ obs.trace st := by
  intro evs
  induction evs with
  | nil => exact fun _ st h => ⟨st, obs.run_pure .., h, rfl⟩
  | cons ev evs ih =>
    intro hq st h
    obtain ⟨s, hs⟩ := hemit ev st (hq _ (.head _)).1 (hq _ (.head _)).2
    obtain ⟨s', h1, h2, h3⟩ := ih (List.forall_mem_cons.1 hq).2 s (hf.emit _ _ _ _ _ hs h)
    refine ⟨s', ?_, h2, by simp [h3, obs.emit_trace _ _ _ _ _ hs]⟩
    simp only [List.forM_eq_forM, List.forM_cons, obs.run_bind, hs] at h1 ⊢
    exact h1

omit [HasFvars P] [HasOldIdent P] in
/-- An oracle-reading base-command evaluation from a denoting store whose events satisfy `Q` is
    performed by `stepBaseCmdStore` at the runtime factory of `F` at every large enough fuel from
    every state `st` with `Pending st o`, recording exactly its events and leaving a state `st'`
    with `Pending st' o'`, given that `emit` succeeds on the well-formed events satisfying `Q`,
    that `choose` follows the pending choices `R` allows, and that the bounded evaluator is
    fuel-monotone. -/
private theorem oracleCmdEngE_followsG {F : P.Factory} {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitGoodOn obs cfgr F Q) (hf : ChooseFollows obs cfgr F R Pending)
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
  rcases evs with _ | ⟨ev, evs⟩
  · exact oracleCmdEngE_follows obs cfgr (Q := fun _ => False) Pending (fun _ _ _ h => h.elim) hf
      hMono hd h nofun st hst
  obtain ⟨he, ⟨-, rfl⟩ | ⟨_, _, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩⟩ := h
  all_goals cases he
  all_goals
    obtain ⟨s, h1⟩ := (by first
      | exact hemit (.assert ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st ⟨rfl, hd⟩ (hq _ (.head _))
      | exact hemit (.assume ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st ⟨rfl, hd⟩ (hq _ (.head _))
      | exact hemit (.cover ⟨InterpLang.rfactory F, σ.get, _, _, _⟩) st ⟨rfl, hd⟩ (hq _ (.head _)))
    exact ⟨0, σ, s, rfl, hd, fun _ _ => by simp [*, stepBaseCmdStore, Cmd.rEmittedEvents],
      hf.emit _ _ _ _ _ h1 hst, traceExt_single (obs.emit_trace _ _ _ _ _ h1)⟩

omit [HasFvars P] in
/-- A base command of an oracle-reading run, from a denoting environment `ρ`, is performed by one
    `stepCmd π i j` step from every state `st` with `Pending st o`, at every large enough `i`, `j`
    and fuel, reaching a denoting store that stands for `σ'`, recording its events and leaving a
    state `st'` with `Pending st' o'`: a deterministic command keeps the pending choices, a
    nondeterministic `.init`/`.set` consumes the value it writes.  Assumes `emit` succeeds on the
    well-formed events satisfying `Q`, `choose` follows the choices `R` allows, every
    engine-realizable base-command step with typed choices is one with choices in `R`, and the
    bounded evaluator is fuel-monotone. -/
private theorem oracleCmdBase_followsG {F : P.Factory}
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitGoodOn obs cfgr F Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    {ρ : IEnv P} {cmd : CmdExt P} {σ' : SemanticStore P} {evs : List (Event P)}
    {o o' : List P.Val} (hd : (IConfig.stmt (.cmd cmd) ρ).Denoting F)
    (h : OracleCmdBase F (InterpLang.absStore F ρ.store.get) cmd σ' evs o o')
    (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st o) :
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (stepInterp (callStepOf (m := m) π i j) fuel (.stmt (.cmd cmd) ρ)) cfgr st
          = (.ok (.terminal { ρ with store := σi }), st'))
      ∧ Pending st' o' ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hdρ, hfρ⟩ := hd
  obtain ⟨base, rfl, he, hdt⟩ := h
  obtain ⟨f0, σi, s, hσ, hdi, hr, hp, ht⟩ := oracleCmdEngE_followsG obs cfgr Pending hemit hf
    hMono hdρ ⟨hlift _ _ _ _ _ he, hdt⟩ hq st hst
  exact ⟨f0, σi, s, hσ, hdi, fun _ j _ _ hj _ => by simp [hfρ, hr j hj], hp, ht⟩

omit [LawfulMonad m] in
/-- `stepCmd_call_complete` with `emit` required to succeed on well-formed events only: a reference
    `.call` with entry frame `σAO` and write-back from the callee's final store `σf` to `σ'`, from a
    denoting caller environment `ρ` carrying the runtime factory of `F`, is performed by
    `stepCmd π i j` at every large enough `i` and `j` from every state `st` with `Pend st o`,
    reaching a denoting store that stands for `σ'`, leaving a state with `Pend st' o'` and
    recording the call's events, given that: emitting well-formed runtime events whose images
    satisfy `Q` succeeds, keeps `Pend` and prepends the events (`hemit`); the callee body run from
    every denoting runtime frame standing for `σAO` reaches a denoting store standing for `σf`,
    turning `Pend · o` into `Pend · o'` and recording `evB` (`hbody`); the call's events satisfy
    `Q`; the engine reaches the value of every input expression (`hargs`); the engine's typed
    write-back check passes (`hwb`); and the bounded evaluator is fuel-monotone. -/
private theorem stepCmd_call_completeG
    (π : String → Option (Procedure P (CmdExt P) Hdr)) {F : P.Factory}
    (hMono : BoundedEvalMono P)
    {Pend : obs.St → List P.Val → Prop} {Q : Event P → Prop}
    (hemit : ∀ (revs : List (IEvent P)) o st, (∀ ev ∈ revs, EvGood F ev ∧ Q (ev.abs F)) →
      Pend st o → ∃ st', obs.run (revs.forM (InterpEffects.emit (P := P))) cfgr st = (.ok ⟨⟩, st')
        ∧ Pend st' o ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    {ρ : IEnv P} (hd : RStore.Denoting F ρ.store.get) (hf : ρ.factory = InterpLang.rfactory F)
    {nm : String} {args : List (CallArg P)} {md : MetaData P} {p : Procedure P (CmdExt P) Hdr}
    {σAO σf σ' : SemanticStore P} {evB : List (Event P)} {o o' : List P.Val}
    (hπ : π nm = some p) (hentry : CallEntry F (InterpLang.absStore F ρ.store.get) p args σAO)
    (hexit : CallExit F (InterpLang.absStore F ρ.store.get) p args σf σ')
    (hargs : CallArgsReach F (InterpLang.absStore F ρ.store.get) args)
    (hwb : WriteBackOK F (InterpLang.absStore F ρ.store.get) p args σf)
    (hbody : ∀ er : RStore P, InterpLang.absStore F er = σAO → RStore.Denoting F er →
      ∀ st, Pend st o → ∃ (fb : Nat) (sf : RStore P) (st' : obs.St),
        InterpLang.absStore F sf = σf ∧ RStore.Denoting F sf ∧
        (∀ i j, fb ≤ i → fb ≤ j → obs.run (runCallee (fun _ e c => stepCmd π i j e c) nm p.body
          (InterpLang.rfactory F) j er) cfgr st = (.ok sf, st')) ∧
        Pend st' o' ∧ obs.TraceExt F st st' evB)
    (hq : ∀ ev ∈ defaultAssertEvents F σAO (checksAtCall md p.spec.preconditions) ++ evB ++
      defaultAssertEvents F σf p.spec.postconditions, Q ev)
    (st : obs.St) (hst : Pend st o) :
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ i j, f0 ≤ i → f0 ≤ j → obs.run (stepCmd π i j ρ (.call nm args md)) cfgr st
        = (.ok (.terminal { ρ with store := σi }), st')) ∧ Pend st' o' ∧
      obs.TraceExt F st st' (defaultAssertEvents F σAO (checksAtCall md p.spec.preconditions) ++
        evB ++ defaultAssertEvents F σf p.spec.postconditions) := by
  obtain ⟨vi, vo, hin, hout, hinit⟩ := hentry
  obtain ⟨-, vs, hrd, hup, hrel⟩ := hexit
  obtain ⟨N, ri, hri, hev⟩ := evalBoundedList_of_reach hMono (storeDenotes_absStore hd) hin hargs
  obtain ⟨ro, hro, hrorel⟩ := readVarList_absStore _ _ (readVarList_of_readValues _ _ _ _ hout)
  obtain ⟨hlin, hlout, rfl⟩ := callEntryStore_of_initCallFrame _ _ _ _ hinit
  obtain ⟨habs, hden⟩ := callEntryStore_abs p hri hrorel
  have hQ : ∀ σr checks, RStore.Denoting F σr →
      (∀ ev ∈ defaultAssertEvents F (InterpLang.absStore F σr) checks, Q ev) →
      ∀ ev ∈ rDefaultAssertEvents (InterpLang.rfactory F) σr checks, EvGood F ev ∧ Q (ev.abs F) :=
    fun σr checks hσ h ev hev => ⟨evGood_rDefault hσ checks ev hev,
      h _ (rDefaultAssertEvents_abs F σr checks ▸ List.mem_map_of_mem hev)⟩
  simp only [List.forall_mem_append] at hq
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
  obtain ⟨s1, e1, p1, t1⟩ := hemit _ o st (hQ _ _ hden (habs ▸ hq1)) hst
  obtain ⟨fb, sf, s2, rfl, hdsf, hrun, p2, rb, hrb, t2⟩ := hbody _ habs hden s1 p1
  obtain ⟨s3, e3, p3, t3⟩ := hemit _ o' s2 (hQ _ p.spec.postconditions hdsf hq3) p2
  obtain ⟨ms, hms, hmsrel⟩ := readVarList_absStore sf _ (readVarList_of_readValues _ _ _ _ hrd)
  obtain ⟨olds, hold⟩ := readVarList_of_storedTy hrel
  have hwb := hwb _ _ _ _ (storeDenotes_absStore hd) (storeDenotes_absStore hdsf) hold hms
  have hbind := bindPositional_of_updateStates _ _ _ _ hup
  refine ⟨N + fb + 1, ρ.store.bindPositional (CallArg.getLhs args) ms, s3, ?_, ?_,
    fun i j hi hj => ?_, p3, ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p ri ro)
      (checksAtCall md p.spec.preconditions) ++ rb ++
      rDefaultAssertEvents (InterpLang.rfactory F) sf p.spec.postconditions, ?_, ?_⟩⟩
  · rw [IStore.get_bindPositional, absStore_bindPositional _ _ hmsrel, hbind.2]
  · rw [IStore.get_bindPositional]
    exact denoting_bindPositional _ hd hmsrel
  · obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [stepCmd]
    simp (disch := omega) [hπ, hf, hev, hro, hlin, hlout, hri.length_eq, hrorel.length_eq, e1,
      hrun i j, e3, hms, hold, hwb, ReadValuesLength hrd, hbind.1, -List.forM_eq_forM]
  · simp only [List.map_append, rDefaultAssertEvents_abs, habs, hrb]
  · simp [t1, t2, t3]

omit [DecidableEq P.Expr] in
/-- An oracle-reading command evaluation at any call-nesting height defines only the names
    `CmdDefs` lists: a base command only the binder of an `init`, a call nothing new, since its
    write-back (`CallExit`) updates already defined slots only. -/
private theorem oracleCmdAt_defines (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    ∀ n f σ c σ' evs o o', OracleCmdAt π n f σ c σ' evs o o' →
      DefinesWithin σ σ' (CmdDefs.defs (P := P) c) := by
  have hb : ∀ {f σ c σ' evs o o'}, OracleCmdBase f σ c σ' evs o o' →
      DefinesWithin σ σ' (CmdDefs.defs (P := P) c) := fun ⟨_, hc, h, _⟩ =>
    hc ▸ evalCmdE_cmdDefsSound _ _ _ _ _ h.toEvalCmdE
  rintro (_ | n) _ _ _ _ _ _ _ h
  · exact hb h
  rcases h with h | ⟨_, _, _, _, _, _, _, _, rfl, -, -, -, -, ⟨_, _, _, hup, -⟩, -⟩ |
    ⟨_, _, _, _, _, _, _, _, rfl, -, -, -, -, ⟨_, _, _, hup, -⟩, -⟩
  · exact hb h
  all_goals exact fun x hx => .inl (UpdateStatesDefMonotone' (vs := [x])
    (fun _ hv => List.mem_singleton.1 hv ▸ hx) hup x (List.mem_singleton_self x))

/-- Every command of an oracle-reading run, calls included, at every call-nesting height `n`, is
    performed by one `stepCmd π i j` step that follows its choices (`CmdFollowsFam` of the stepper
    family `callStepOf π`), under the same assumptions as for a base command (`emit` succeeding
    on the well-formed events satisfying `Q`). -/
private theorem oracleCmdAt_followsG {F : P.Factory}
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitGoodOn obs cfgr F Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f)) :
    ∀ n, CmdFollowsFam obs (callStepOf (m := m) π) cfgr F Pending Q (OracleCmdAt π n) := by
  have hem := fun revs o st hq h => follows_forM_emitG obs cfgr Pending hemit hf o revs hq st h
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ _ hd h hq st hst =>
    oracleCmdBase_followsG obs cfgr Pending π hemit hf hMono hlift hd h hq st hst
  | succ n ih =>
    rintro ρ _ _ _ o o' hd (h | hcall) hq st hst
    · exact oracleCmdBase_followsG obs cfgr Pending π hemit hf hMono hlift hd h hq st hst
    obtain ⟨hdρ, hfρ⟩ := hd
    have hq2 : ∀ {a b c : List (Event P)}, (∀ ev ∈ a ++ b ++ c, Q ev) → ∀ ev ∈ b, Q ev :=
      fun h ev hev => h ev (by simp [hev])
    rcases hcall with ⟨nm, p, args, md, σAO, ss, ρ', bodyEvs, rfl, hπ, hss, hentry, hbody, hexit,
        rfl, hargs, hwb⟩ |
      ⟨nm, p, args, md, σAO, gr, ρEnd, bodyEvs, rfl, hπ, hgr, hentry, hbody, hexit, rfl, hargs, hwb⟩
    all_goals
      refine (stepCmd_call_completeG obs cfgr π hMono hem hdρ hfρ hπ hentry hexit hargs hwb
        (fun er habs hder s1 p1 => ?_) hq st hst).imp fun _ ⟨σi, s, h1, h2, hr, hp, ht⟩ =>
          ⟨σi, s, h1, h2, fun i j _ hi hj _ => hr i j hi hj, hp, ht⟩
    · obtain ⟨f, cy, s2, ⟨hcd, -, hcy⟩, hb, p2, t2⟩ := runInterp_complete_follows_fam obs
        (callStepOf π) cfgr Pending hf hMono ih (oracleCmdAt_defines π n)
        (hbody.imp fun _ _ _ => OracleStepE.toParam hbool) (.inl ⟨_, rfl⟩) (hq2 hq) s1 p1
        (.stmt (.block "" ss #[]) ⟨.ofStore er, InterpLang.rfactory F⟩)
        (by simp [IConfig.abs, IEnv.abs, habs]) ⟨(by simpa using hder), rfl⟩ trivial
      obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_terminal (P := P) _ _ _).1 hcy
      exact ⟨f, ie.store.get, s2, rfl, hcd.1, fun i j hi hj => by
        simp [runCallee, hss, hb i j j hi hj hj], p2, t2⟩
    · have hx : (ICFGConfig.atBlock gr gr.entry ⟨.ofStore er, InterpLang.rfactory F⟩ :
          ICFGConfig String (CmdExt P) P).abs F =
            .atBlock gr gr.entry { store := σAO, factory := F } := by
        simp [ICFGConfig.abs, IEnv.abs, habs]
      obtain ⟨f, s2, y1, ⟨hyd, hy⟩, hb, p2, t2⟩ := runInterpCFG_follows_fam obs cfgr F Pending
        (Q := Q) (E := OracleCmdAt π n)
        (fun i j _ => StepCmdM.toStore (stepCmd π i) j)
        (fun σ c σ' evs o o' hσ hc hq st hst => by
          obtain ⟨f0, σi, s', hσi, hdi, hs, hp, ht⟩ :=
            ih ⟨σ, InterpLang.rfactory F⟩ c σ' evs o o' ⟨hσ, rfl⟩ hc hq st hst
          refine ⟨f0, s', σi, hσi, hdi, fun i j k hi hj hk => ?_, hp, ht⟩
          have hijk := hs i j k hi hj hk
          simp only [stepInterp_stmt_cmd, callStepOf] at hijk
          simp [hijk, IConfig.getEnv])
        hMono
        (x1 := .atBlock gr gr.entry ⟨.ofStore er, InterpLang.rfactory F⟩)
        (y := (.terminal ρEnd, o')) ⟨(by simpa [ICFGConfig.env] using hder), rfl⟩ (hx ▸ hbody)
        trivial (hq2 hq) s1 p1
      rcases y1 with _ | _ | ie <;> simp only [ICFGConfig.abs, CFGConfig.terminal.injEq,
        reduceCtorEq] at hy
      subst hy
      refine ⟨f, RStore.project er ie.store.get, s2, ?_, hyd.1.project er, fun i j hi hj => ?_,
        p2, t2⟩
      · rw [InterpLang.absStore_project _ hder, habs]
        rfl
      · simp [runCallee, hgr, hb i j j hi hj hj]

/-- Every command of an oracle-reading run, calls included, at every call-nesting height `n`, is
    performed by one `stepCmd π i j` step that follows its choices (`CmdFollowsFam` of the stepper
    family `callStepOf π`), when `emit` succeeds on the events satisfying `Q`, `choose` follows the
    choices `R` allows, every engine-realizable base-command step with typed choices is one with
    choices in `R`, `R` allows `tt` and `ff` as Booleans, and the bounded evaluator is
    fuel-monotone. -/
private theorem oracleCmdAt_follows {F : P.Factory}
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {R : ChoiceRecord P} {Q : Event P → Prop}
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f)) :
    ∀ n, CmdFollowsFam obs (callStepOf (m := m) π) cfgr F Pending Q (OracleCmdAt π n) :=
  oracleCmdAt_followsG obs cfgr Pending π (fun ev st _ h => hemit F ev st h) hf hMono hlift hbool

omit [HasFvars P] [LawfulMonad m] in
/-- The per-command law along a choice sequence for the stepper family `callStepOf π` gives it
    for the call-aware stepper family `fun d _ => stepCmd π d` of the driver `runCallInterp`. -/
private theorem cmdFollowsFam_stepCmd (π : String → Option (Procedure P (CmdExt P) Hdr))
    {F : P.Factory} {Q : Event P → Prop} {E : OracleCmdRel P}
    (h : CmdFollowsFam obs (callStepOf (m := m) π) cfgr F Pending Q E) :
    CmdFollowsFam obs (fun d _ => stepCmd (m := m) π d) cfgr F Pending Q E :=
  fun ρ c σ' evs o o' hd hc hq st hst =>
    have ⟨f0, σi, s, a, b, c, d, e⟩ := h ρ c σ' evs o o' hd hc hq st hst
    ⟨f0, σi, s, a, b, fun i _ fuel hi _ hfu => c i fuel fuel hi hfu hfu, d, e⟩

end Follows

section FollowsRun

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m]

/-- `call_runCallInterp_follows_prefix` with `emit` required to succeed on well-formed events
    only, and with the reached state's pending choices exhausted: for a reference run from the
    abstraction of a tracked configuration `start` to `final` resolving its choices as `cs` and
    emitting events satisfying `Q`, from every state `st` with `Pending st cs` there are `k`, a
    tracked configuration `cy` standing for `final` and a state `st'` with `Pending st' []` whose
    trace is the run's events prepended to the trace of `st`, such that at every large enough fuel
    and call-depth limit `d` the run at fuel `fuel + k` from `start` is the run at fuel `fuel` from
    `cy` from `st'`. -/
private theorem call_runCallInterp_follows_prefixG (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitGoodOn obs cfgr F Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    {start : IConfig P (CmdExt P)} {final : Config P (CmdExt P)} {evs : List (Event P)}
    {cs : List P.Val} (hds : start.Denoting F) (htr : start.Tracked)
    (hrun : RunChoices π (start.abs F) evs final cs)
    (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (k f0 : Nat) (cy : IConfig P (CmdExt P)) (st' : obs.St),
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d → obs.run (runCallInterp π (fuel + k) start d) cfgr st
        = obs.run (runCallInterp π fuel cy d) cfgr st')
      ∧ cy.abs F = final ∧ cy.Denoting F ∧ cy.Tracked ∧ Pending st' [] ∧
      obs.TraceExt F st st' evs := by
  obtain ⟨n, hn⟩ := hrun
  obtain ⟨k, f0, cy, st', h, hy, hdy, hty, hp, ht⟩ := runInterp_follows_prefix_fam obs
    (fun d _ => stepCmd π d) cfgr Pending hf hMono
    (cmdFollowsFam_stepCmd obs cfgr Pending π (oracleCmdAt_followsG obs cfgr Pending π hemit hf
      hMono hlift hbool n)) (oracleCmdAt_defines π n)
    ((List.append_nil cs ▸ hn []).imp fun _ _ _ => OracleStepE.toParam hbool) hq st hst start
    rfl hds htr
  exact ⟨k, f0, cy, st', fun fu d hfu hd => h d fu fu hd hfu hfu, hy, hdy, hty, hp, ht⟩

/-- **Following a choice sequence, up to a prefix.**  If a reference run of the call-aware
    semantics from the abstraction of a tracked configuration `start` to `final` resolves its
    choices as `cs` (`RunChoices`) and emits events satisfying `Q`, then from every state `st`
    with `Pending st cs` there are `k`, a tracked configuration `cy` standing for `final` and a
    state `st'` whose trace is the run's events prepended to the trace of `st`, such that for
    every large enough `fuel` and call-depth limit `d` the run of `runCallInterp π` at fuel
    `fuel + k` from `start` is the run at fuel `fuel` from `cy` from `st'`.  The run may stop
    anywhere.

    Hypotheses: `emit` succeeds on the events satisfying `Q` (`hemit`); `choose` follows the
    pending choices that `R` allows (`hf`); the bounded evaluator is fuel-monotone (`hMono`);
    every engine-realizable base-command step with typed choices (`EvalCmdEngE` at
    `ChoiceRecord.typed`) is one with choices in `R` (`hlift`); `R` allows `tt` and `ff` as
    Booleans (`hbool`).  The run's
    evaluations carry the engine's facts (`OracleCmdBase`, `OracleCallArm`, `StepEngParamE`,
    `StepCFGEngE`). -/
theorem call_runCallInterp_follows_prefix (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    {start : IConfig P (CmdExt P)} {final : Config P (CmdExt P)} {evs : List (Event P)}
    {cs : List P.Val} (hds : start.Denoting F) (htr : start.Tracked)
    (hrun : RunChoices π (start.abs F) evs final cs)
    (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (k f0 : Nat) (cy : IConfig P (CmdExt P)) (st' : obs.St),
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d → obs.run (runCallInterp π (fuel + k) start d) cfgr st
        = obs.run (runCallInterp π fuel cy d) cfgr st')
      ∧ cy.abs F = final ∧ cy.Denoting F ∧ cy.Tracked ∧ obs.TraceExt F st st' evs := by
  obtain ⟨k, f0, cy, st', h, hy, hdy, hty, -, ht⟩ := call_runCallInterp_follows_prefixG obs π cfgr
    Pending (fun ev st _ h => hemit F ev st h) hf hMono hlift hbool hds htr hrun hq st hst
  exact ⟨k, f0, cy, st', h, hy, hdy, hty, ht⟩

/-- **Whole-run completeness along a choice sequence.**  If a reference run of the call-aware
    semantics from the abstraction of a tracked configuration `start` resolves its choices as
    `cs` (`RunChoices`, under the engine's factory extension), ends at a configuration `final`
    the monadic interpreter stops at and emits events satisfying `Q`, then from every state `st`
    with `Pending st cs` the monadic interpreter `runCallInterp π` from `start` reaches a
    configuration denoting `final` (`IConfig.Denotes`) at every large enough fuel and call-depth
    limit, prepending runtime events denoting exactly the run's events to the trace.

    Hypotheses: `emit` succeeds on the events satisfying `Q` (`hemit`); `choose` follows the
    pending choices that `R` allows (`hf`); the bounded evaluator is fuel-monotone (`hMono`);
    every engine-realizable base-command step with typed choices (`EvalCmdEngE` at
    `ChoiceRecord.typed`) is one with choices in `R` (`hlift`); `R` allows `tt` and `ff` as
    Booleans (`hbool`).  The run's
    evaluations carry the engine's facts (`OracleCmdBase`, `OracleCallArm`, `StepEngParamE`,
    `StepCFGEngE`). -/
theorem call_runCallInterp_complete_follows (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hlift : ∀ f σ c σ' evs, EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs →
      EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    {start : IConfig P (CmdExt P)} {final : Config P (CmdExt P)} {evs : List (Event P)}
    {cs : List P.Val} (hds : start.Denoting F) (htr : start.Tracked)
    (hrun : RunChoices π (start.abs F) evs final cs)
    (hdone : Config.Done final) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (f0 : Nat) (final' : IConfig P (CmdExt P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCallInterp π fuel start d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨n, hn⟩ := hrun
  obtain ⟨f0, cy, st', hcy, h, -, ht⟩ := runInterp_complete_follows_fam obs
    (fun d _ => stepCmd π d) cfgr Pending hf hMono
    (cmdFollowsFam_stepCmd obs cfgr Pending π (oracleCmdAt_follows obs cfgr Pending π hemit hf
      hMono hlift hbool n)) (oracleCmdAt_defines π n)
    ((List.append_nil cs ▸ hn []).imp fun _ _ _ => OracleStepE.toParam hbool) hdone hq st hst start
    rfl hds htr
  exact ⟨f0, cy, st', hcy, fun fu d hfu hd => h d fu fu hd hfu hfu, ht⟩

/-- `call_runCallInterp_complete_follows` with the step premise on reference evaluations: the
    conclusion holds when every reference base-command evaluation (`EvalCmdE`) is an
    engine-realizable step with choices in `R` (`hchk`) and `R` allows `tt` and `ff` as Booleans
    (`hbool`). -/
theorem call_runCallInterp_complete_follows_chk (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    {R : ChoiceRecord P} {Q : Event P → Prop} (Pending : obs.St → List P.Val → Prop)
    (hemit : EmitTotalOn obs cfgr Q) (hf : ChooseFollows obs cfgr F R Pending)
    (hMono : BoundedEvalMono P)
    (hchk : ∀ f σ c σ' evs, EvalCmdE (P := P) f σ c σ' evs → EvalCmdEngE P R f σ c σ' evs)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    {start : IConfig P (CmdExt P)} {final : Config P (CmdExt P)} {evs : List (Event P)}
    {cs : List P.Val} (hds : start.Denoting F) (htr : start.Tracked)
    (hrun : RunChoices π (start.abs F) evs final cs)
    (hdone : Config.Done final) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St) (hst : Pending st cs) :
    ∃ (f0 : Nat) (final' : IConfig P (CmdExt P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCallInterp π fuel start d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs :=
  call_runCallInterp_complete_follows obs π cfgr Pending hemit hf hMono
    (fun _ _ _ _ _ he => hchk _ _ _ _ _ he.toEvalCmdE) hbool hds htr hrun hdone hq st hst

end FollowsRun

/-! ## Replay completeness for `CmdExt P` -/

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- **`ReplayM` follows its oracle**: the pending choices of a state are witnessed
    (`OracleWitness`) by a prefix of its oracle tail whose values pass `choose`'s type check
    (`OracleTyped`), and `choose` accepts the values that pass its checks. -/
theorem chooseFollows_replay (cfg : ReplayCfg P) (F : P.Factory) :
    ChooseFollows (obsReplay (P := P)) cfg F (ChoiceRecord.typed P)
      (fun st cs => ∃ rs, rs <+: st.remaining ∧ OracleWitness F rs cs ∧
        OracleTyped F (ChoiceRecord.typed P) rs cs) :=
  chooseFollows_replay_valid cfg

/-- **Whole-run `ReplayM` completeness with calls**, nondeterministic runs included.  If a
    reference run of the call-aware semantics from the abstraction of a tracked configuration
    `start` resolves its choices as `cs` (`RunChoices`) and ends at a configuration `final` the
    monadic interpreter stops at, then from every replay state whose oracle tail begins with a
    runtime segment `rs` that witnesses `cs` (`OracleWitness`) and passes `choose`'s type check
    (`OracleTyped`), under every config whose stop hook is off, `runCallInterp π` from `start`
    reaches a configuration denoting `final` at every large enough fuel and call-depth limit,
    prepending runtime events denoting exactly the run's events to the trace.

    Hypothesis: the bounded evaluator is fuel-monotone (`hMono`). -/
theorem call_replayRun_complete (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfg : ReplayCfg P) {F : P.Factory} (hcfg : cfg.interruptOn = fun _ => none)
    (hMono : BoundedEvalMono P)
    {start : IConfig P (CmdExt P)} {final : Config P (CmdExt P)} {evs : List (Event P)}
    {cs : List P.Val} (hds : start.Denoting F) (htr : start.Tracked)
    (hrun : RunChoices π (start.abs F) evs final cs)
    (hdone : Config.Done final) (st : ReplayState P) (rs : List P.Expr)
    (hpre : rs <+: st.remaining) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed P) rs cs) :
    ∃ (f0 : Nat) (final' : IConfig P (CmdExt P)) (st' : ReplayState P), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        replayRun (runCallInterp π fuel start d) cfg st = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs :=
  call_runCallInterp_complete_follows obsReplay π cfg (Q := fun _ => True) _
    (fun _ _ _ _ => emitTotal_replay cfg hcfg _ _) (chooseFollows_replay cfg F) hMono
    (fun _ _ _ _ _ h => h) (fun f _ => HasBool.boolIsValOfTy f) hds htr hrun hdone
    (fun _ _ => trivial) st ⟨rs, hpre, hrs, hty⟩

/-! ### Replay under a stop hook rejecting events that are not well formed -/

open Classical in
/-- The stop hook that throws on a runtime event that is not well formed under `F`. -/
private noncomputable def goodHook (F : P.Factory) (ev : IEvent P) : Option StopReason :=
  if EvGood F ev then none else some .oracleExhausted

/-- The strict replay configuration whose stop hook throws on the events that are not well formed
    under `F`. -/
private noncomputable def cfgGood (F : P.Factory) : ReplayCfg P := { interruptOn := goodHook F }

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- With the stop hook silent on `ev`, `emit ev` records the event and returns. -/
private theorem replayRun_emit_of_none (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P)
    (h : cfg.interruptOn ev = none) :
    replayRun (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st
      = (.ok ⟨⟩, { st with traceRev := ev :: st.traceRev }) := by
  simp only [InterpEffects.emit, replayRun_modify_bind, replayRun_read_bind, h]
  rfl

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- With the stop hook firing on `ev`, `emit ev` does not succeed. -/
private theorem replayRun_emit_of_some (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P)
    {r : StopReason} (h : cfg.interruptOn ev = some r) (u : Unit) (st' : ReplayState P) :
    replayRun (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st ≠ (.ok u, st') := by
  simp only [InterpEffects.emit, replayRun_modify_bind, replayRun_read_bind, h, replayRun_throw]
  simp

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- Under `cfgGood F`, `emit` succeeds on every well-formed event. -/
private theorem emitGood_replay (F : P.Factory) (Q : Event P → Prop) :
    EmitGoodOn (obsReplay (P := P)) (cfgGood F) F Q := fun ev st hg _ =>
  ⟨_, replayRun_emit_of_none ev _ st (by simp [cfgGood, goodHook, hg])⟩

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- An `emit` that succeeds under `cfgGood F` emits a well-formed event. -/
private theorem evGood_of_emit {F : P.Factory} {ev : IEvent P} {st st' : ReplayState P} {u : Unit}
    (h : replayRun (InterpEffects.emit (P := P) (m := ReplayM P) ev) (cfgGood F) st
      = (.ok u, st')) :
    EvGood F ev := Classical.byContradiction fun hg =>
  replayRun_emit_of_some ev _ st (r := .oracleExhausted) (by simp [cfgGood, goodHook, hg]) u st' h

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `ReplayM` under `cfgGood F` follows its oracle as in `chooseFollows_replay`, and keeps every
    recorded event well formed. -/
private theorem chooseFollows_good (F : P.Factory) :
    ChooseFollows (obsReplay (P := P)) (cfgGood F) F (ChoiceRecord.typed P)
      (fun st cs => (∃ rs, rs <+: st.remaining ∧ OracleWitness F rs cs ∧
        OracleTyped F (ChoiceRecord.typed P) rs cs) ∧ ∀ ev ∈ st.traceRev, EvGood F ev) := by
  have h := chooseFollows_replay (cfgGood F) F
  refine ⟨fun σr σ ty v cs st hs hp hR => ?_,
    fun ev cs st st' u he hp => ⟨h.emit ev cs st st' u he hp.1, ?_⟩⟩
  · obtain ⟨r, st', h1, h2, h3, h4, h5, h6⟩ := h.choose σr σ ty v cs st hs hp.1 hR
    have h5' : st'.traceRev = st.traceRev := h5
    exact ⟨r, st', h1, h2, h3, h4, h5, h6, fun ev hev => hp.2 ev (h5' ▸ hev)⟩
  · obtain rfl := (congrArg Prod.snd he).symm.trans (replayRun_emit_state ev _ st)
    exact List.forall_mem_cons.2 ⟨evGood_of_emit he, hp.2⟩

/-! ### Replay runs only extend the trace -/

/-- The trace of the run of `x` under `cfg` from `st` extends the trace of `st`. -/
@[reducible] private def GBridge {α : Type} (x : ReplayM P α) (cfg : ReplayCfg P)
    (st : ReplayState P) : Prop :=
  st.traceRev <:+ (replayRun x cfg st).2.traceRev

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
  [HasOldIdent P] in
/-- `GBridge` holds for `pure`. -/
private theorem gBridge_pure {α} (a : α) (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (pure a : ReplayM P α) cfg st := List.suffix_rfl

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
  [HasOldIdent P] in
/-- `GBridge` holds for `throw`. -/
private theorem gBridge_throw {α} (r : StopReason) (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (throw r : ReplayM P α) cfg st := List.suffix_rfl

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `GBridge` holds for `branch`, which throws in `ReplayM`. -/
private theorem gBridge_branch (factory : InterpLang.RFactory P) (store : RStore P) (v : P.Expr)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (InterpEffects.branch (P := P) (m := ReplayM P) factory store v) cfg st :=
  gBridge_throw .expressionWasNotBoolean cfg st

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `GBridge` holds for `emit`. -/
private theorem gBridge_emit (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st := by
  simp only [GBridge, replayRun_emit_state]
  exact List.suffix_cons _ _

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `GBridge` holds for `choose`. -/
private theorem gBridge_choose (factory : InterpLang.RFactory P) (store : RStore P)
    (ty : P.Ty) (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (InterpEffects.choose (P := P) factory store ty) cfg st := by
  simp only [GBridge, replayRun, choose_traceRev_eq, List.suffix_rfl]

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
  [HasOldIdent P] in
/-- `x >>= g` satisfies `GBridge` when `x` does and every `g a` does from every state. -/
private theorem gBridge_bind' {α β : Type} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : GBridge x cfg st) (hg : ∀ a s, GBridge (g a) cfg s) :
    GBridge (x >>= g) cfg st := by
  unfold GBridge at *
  rw [replayRun_bind]
  rcases hr : replayRun x cfg st with ⟨_ | a, s⟩ <;> rw [hr] at hx
  · exact hx
  · exact hx.trans (hg a s)

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `GBridge` holds for a `forM` of `emit`s. -/
private theorem gBridge_forM_emit (evs : List (IEvent P)) (cfg : ReplayCfg P)
    (st : ReplayState P) : GBridge (evs.forM (InterpEffects.emit (P := P))) cfg st := by
  bridge_ind gBridge

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- `GBridge` holds for `stepBaseCmdStore`. -/
private theorem gBridge_stepBaseCmdStore (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (base : Cmd P) (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (stepBaseCmdStore (m := ReplayM P) fuel factory store base) cfg st := by
  bridge_ind gBridge

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- `GBridge` holds for `stepInterp` over a command stepper satisfying it. -/
private theorem gBridge_stepInterp {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT) (cfg : ReplayCfg P) (st : ReplayState P),
        GBridge (stepCmd f e cmd) cfg st) :
    ∀ (n : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), GBridge (stepInterp stepCmd n c) cfg st := by bridge_ind gBridge

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- `GBridge` holds for `runInterp` over a command stepper satisfying it. -/
private theorem gBridge_runInterp {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT) (cfg : ReplayCfg P) (st : ReplayState P),
        GBridge (stepCmd f e cmd) cfg st) :
    ∀ (fuel : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), GBridge (runInterp stepCmd fuel c) cfg st := by bridge_ind gBridge

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- `GBridge` holds for `stepInterpCFG` over a store stepper satisfying it. -/
private theorem gBridge_stepInterpCFG {l CmdT : Type} [BEq l]
    (stepCmd : StepCmdStoreM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (fac : InterpLang.RFactory P) (σ : IStore P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P), GBridge (stepCmd f fac σ cmd) cfg st) :
    ∀ (n : Nat) (c : ICFGConfig l CmdT P) (cfg : ReplayCfg P) (st : ReplayState P),
      GBridge (stepInterpCFG stepCmd n c) cfg st := by bridge_ind gBridge

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- `GBridge` holds for `runInterpCFG` over a store stepper satisfying it. -/
private theorem gBridge_runInterpCFG {l CmdT : Type} [BEq l]
    (stepCmd : StepCmdStoreM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (fac : InterpLang.RFactory P) (σ : IStore P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P), GBridge (stepCmd f fac σ cmd) cfg st) :
    ∀ (n : Nat) (c : ICFGConfig l CmdT P) (cfg : ReplayCfg P) (st : ReplayState P),
      GBridge (runInterpCFG stepCmd n c) cfg st := by bridge_ind gBridge

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- `GBridge` holds for the callee body run `runCallee` over a command stepper satisfying it. -/
private theorem gBridge_runCallee (step : StepCmdM P (CmdExt P) (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdExt P) (cfg : ReplayCfg P) (st : ReplayState P),
        GBridge (step f e cmd) cfg st)
    (procName : String) (body : Body P (CmdExt P)) (fac : InterpLang.RFactory P) (n : Nat)
    (σ : RStore P) (cfg : ReplayCfg P) (st : ReplayState P) :
    GBridge (runCallee step procName body fac n σ) cfg st := by
  cases body
  · have hR := gBridge_runInterp step hstep
    unfold runCallee
    bridge_close gBridge
  · unfold runCallee
    bridge_close gBridge

omit [HasFvars P] in
/-- `GBridge` holds for `stepCmd π`. -/
private theorem gBridge_stepCmd (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    ∀ (k d : Nat) (env : IEnv P) (cmd : CmdExt P) (cfg : ReplayCfg P) (st : ReplayState P),
      GBridge (stepCmd π d k env cmd) cfg st := by bridge_ind gBridge

omit [HasFvars P] in
/-- The trace of a run of `runCallInterp π` under any configuration extends the trace of its start
    state. -/
private theorem gBridge_runCallInterp (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fuel : Nat) (start : IConfig P (CmdExt P)) (d : Nat) (cfg : ReplayCfg P)
    (st : ReplayState P) : GBridge (runCallInterp (m := ReplayM P) π fuel start d) cfg st :=
  gBridge_runInterp _ (fun k => gBridge_stepCmd π k d) ..

/-! ### Completeness of the replay verdict -/

/-- The semantic counterpart of `assertFailureHalt`: the event belongs to the target obligation
    (`label` and `md`) and its recorded condition evaluates, under the reference evaluator, to the
    Boolean value witnessing the obligation: `ffVal` (a failing assertion) for an `.assert`,
    `ttVal` (a reached cover) for a `.cover`; and the engine evaluates the condition to the
    corresponding literal up to metadata (`InterpLang.eqModuloMeta`), `HasBool.ff` respectively
    `HasBool.tt` (`EngEval`). -/
@[expose] def assertFailureE (target : AssertId P) : Event P → Prop
  | .assert a => target.label = a.label ∧ target.md = a.metadata ∧
      P.eval a.factory a.store a.expr = some (HasBool.ffVal a.factory) ∧
      EngEval P a.factory a.store a.expr (fun _ r => InterpLang.eqModuloMeta r HasBool.ff)
  | .cover a => target.label = a.label ∧ target.md = a.metadata ∧
      P.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) ∧
      EngEval P a.factory a.store a.expr (fun _ r => InterpLang.eqModuloMeta r HasBool.tt)
  | .assume _ => False

omit [HasFvar P] [HasFvars P] [HasOldIdent P] in
/-- A well-formed runtime event whose image satisfies `assertFailureE target` fires
    `assertFailureHalt target` at every large enough fuel, when the bounded evaluator is
    fuel-monotone. -/
private theorem assertFailureHalt_of_E (hMono : BoundedEvalMono P) {target : AssertId P}
    {F : P.Factory} {rev : IEvent P} (hg : EvGood F rev) (h : assertFailureE target (rev.abs F)) :
    ∃ n, ∀ fuel, n ≤ fuel → assertFailureHalt target fuel rev = true := by
  rcases rev with a | a | a <;> obtain ⟨hf, hden⟩ := hg
  · obtain ⟨hl, hm, he, hok⟩ := h
    obtain ⟨n, r, hb, -⟩ := hok.1 a.store _ (storeDenotes_absStore hden) he
    have hr : InterpLang.eqModuloMeta r HasBool.ff :=
      hok.2 a.store n r (storeDenotes_absStore hden) hb
    dsimp only [REventArg.abs] at hb
    exact ⟨n, fun fuel hn => by
      simp [assertFailureHalt, REventArg.abs, hl, hm, hf, hMono _ _ _ _ _ _ hn hb, hr]⟩
  · exact h.elim
  · obtain ⟨hl, hm, he, hok⟩ := h
    obtain ⟨n, r, hb, -⟩ := hok.1 a.store _ (storeDenotes_absStore hden) he
    have hr : InterpLang.eqModuloMeta r HasBool.tt :=
      hok.2 a.store n r (storeDenotes_absStore hden) hb
    dsimp only [REventArg.abs] at hb
    exact ⟨n, fun fuel hn => by
      simp [assertFailureHalt, REventArg.abs, hl, hm, hf, hMono _ _ _ _ _ _ hn hb, hr]⟩

/-- **Completeness of call-aware replay.**  If a reference run of the call-aware semantics from
    the configuration `cex.cfg` stands for resolves its choices as `cs` (`RunChoices`) and emits
    an event of the target obligation whose condition evaluates, under the reference evaluator, to
    the Boolean witnessing it (`assertFailureE`), and `cex.oracle` begins with a runtime segment
    `rs` that witnesses `cs` (`OracleWitness`) and passes `choose`'s type check (`OracleTyped`),
    then `cex`, replayed with its own oracle, reaches the target failure (`genuine`) at every
    sufficiently large fuel and call-depth limit.  The run may stop anywhere, after the failing
    event or not.

    Hypothesis: the bounded evaluator is fuel-monotone (`hMono`). -/
theorem call_replayComplete
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (cex : CexA P (CmdExt P))
    (hMono : BoundedEvalMono P)
    {evs : List (Event P)} {final : Config P (CmdExt P)} {cs : List P.Val}
    (F : P.Factory) (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hrun : RunChoices π (cex.cfg.abs F) evs final cs)
    (rs : List P.Expr) (hpre : rs <+: cex.oracle) (hrs : OracleWitness F rs cs)
    (hty : OracleTyped F (ChoiceRecord.typed P) rs cs)
    (hfail : ∃ ev ∈ evs, assertFailureE target ev) :
    ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine π target fuel cex d := by
  obtain ⟨k, f0, cy, st', hk, -, -, -, ⟨-, hgood⟩, revs, rfl, htr⟩ :=
    call_runCallInterp_follows_prefixG obsReplay π (cfgGood F) (Q := fun _ => True) _
      (emitGood_replay F _) (chooseFollows_good F) hMono (fun _ _ _ _ _ h => h)
      (fun f _ => HasBool.boolIsValOfTy f) hd ht hrun
      (fun _ _ => trivial) { remaining := cex.oracle } ⟨⟨rs, hpre, hrs, hty⟩, nofun⟩
  simp only [obsReplay] at hk htr
  obtain ⟨_, hev, hfe⟩ := hfail
  obtain ⟨rev, hrev, rfl⟩ := List.mem_map.1 hev
  have hmem : rev ∈ st'.traceRev := by simp [htr, hrev]
  obtain ⟨n, hn⟩ := assertFailureHalt_of_E hMono (hgood rev hmem) hfe
  refine ⟨n + f0 + k, fun fuel d hF hd => ?_⟩
  obtain ⟨G, rfl⟩ : ∃ G, fuel = G + k := ⟨fuel - k, by omega⟩
  refine (genuine_iff ..).2 ⟨rev, ?_, hn _ (by omega)⟩
  have hon := (dBridge_runCallInterp π (G + k) cex.cfg d (cfgGood F)
    { remaining := cex.oracle }).1.1
  rw [hk G d (by omega) (by omega)] at hon
  exact ((gBridge_runCallInterp π G cy d (cfgGood F) st').trans hon).subset hmem

/-! ## Every reference run has a choice sequence -/

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] [DecidableEq P.Expr] in
/-- The oracle-reading step relation is monotone in its command relation. -/
private theorem OracleStepE.imp {E E' : OracleCmdRel P}
    (h : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → E' f σ c σ' evs o o') :
    ∀ {x evs y}, OracleStepE E x evs y → OracleStepE E' x evs y := by
  intro _ _ _ h'
  induction h' <;> constructor <;> first | assumption | exact h _ _ _ _ _ _ _ ‹_›


omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- The oracle-reading CFG step relation is monotone in its command relation. -/
private theorem OracleCFGStepE.imp {E E' : OracleCmdRel P}
    (h : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → E' f σ c σ' evs o o') :
    ∀ {x : CFGConfig String (CmdExt P) P × List P.Val} {evs y},
      OracleCFGStepE E x evs y → OracleCFGStepE E' x evs y := by
  intro _ _ _ h'
  cases h' with
  | step_cmd he => exact .step_cmd (h _ _ _ _ _ _ _ he)
  | step_admin hs => exact .step_admin hs

omit [DecidableEq P.Expr] in
/-- The oracle-reading command relation grows with the call-nesting height: a derivation whose
    calls nest at most `n` deep also nests at most `m` deep, for every `m ≥ n`. -/
private theorem oracleCmdAt_mono (π : String → Option (Procedure P (CmdExt P) Hdr))
    :
    ∀ {n m : Nat}, n ≤ m → ∀ {f σ c σ' evs o o'},
      OracleCmdAt π n f σ c σ' evs o o' → OracleCmdAt π m f σ c σ' evs o o' := by
  intro n
  induction n with
  | zero =>
    intro m _ _ _ _ _ _ _ _ h
    cases m with
    | zero => exact h
    | succ m => exact .inl h
  | succ n ih =>
    intro m hm _ _ _ _ _ _ _ h
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rcases h with h | ⟨nm, p, a, md, σAO, ss, ρ', be, rfl, hp, hs, he, hb, hx, rfl, hr, hw⟩ |
      ⟨nm, p, a, md, σAO, g, ρE, be, rfl, hp, hs, he, hb, hx, rfl, hr, hw⟩
    · exact .inl h
    · exact .inr (.inl ⟨nm, p, a, md, σAO, ss, ρ', be, rfl, hp, hs, he,
        hb.imp fun _ _ _ => OracleStepE.imp fun _ _ _ _ _ _ _ => ih (by omega), hx, rfl, hr, hw⟩)
    · exact .inr (.inr ⟨nm, p, a, md, σAO, g, ρE, be, rfl, hp, hs, he,
        hb.imp fun _ _ _ => OracleCFGStepE.imp fun _ _ _ _ _ _ _ => ih (by omega), hx, rfl, hr,
          hw⟩)


omit [DecidableEq P.Expr] in
/-- A reference run over the command relation `E` has a choice sequence, when every `E`-step of
    a command has one (`hE`), the bounded evaluator reaches every reference value and runtime guard
    values agree with the reference ones. -/
private theorem runChoices_of_star
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hEvalComplete : BoundedEvalComplete P)
    (hGuards : EngineGuardsAgree P)
    {E : EvalCmdParamE P (CmdExt P) (Event P)}
    (hE : ∀ f σ c σ' evs, E f σ c σ' evs →
      ∃ cs n, ∀ rest, OracleCmdAt π n f σ c σ' evs (cs ++ rest) rest)
    {c c' : Config P (CmdExt P)} {evs : List (Event P)}
    (h : StepStmtStarE P E c evs c') :
    ∃ cs, RunChoices π c evs c' cs := by
  induction h with
  | refl => exact ⟨[], 0, fun _ => .refl _⟩
  | step x e y _ _ hs hr ih =>
    obtain ⟨a, n, ha⟩ : ∃ cs n, ∀ rest,
        OracleStepE (OracleCmdAt π n) (x, cs ++ rest) e (y, rest) := by
      clear ih hr
      induction hs with
      | step_cmd h =>
        obtain ⟨cs, n, H⟩ := hE _ _ _ _ _ h
        exact ⟨cs, n, fun r => .step_cmd (H r)⟩
      | step_ite_true he =>
        exact ⟨[], 0, fun _ =>
          .step_det (.step_ite_true he ⟨hEvalComplete.reach, (hGuards ..).1 he⟩)⟩
      | step_ite_false he =>
        exact ⟨[], 0, fun _ =>
          .step_det (.step_ite_false he ⟨hEvalComplete.reach, (hGuards ..).2 he⟩)⟩
      | step_loop_enter he =>
        exact ⟨[], 0, fun _ =>
          .step_det (.step_loop_enter he ⟨hEvalComplete.reach, (hGuards ..).1 he⟩)⟩
      | step_loop_exit he =>
        exact ⟨[], 0, fun _ =>
          .step_det (.step_loop_exit he ⟨hEvalComplete.reach, (hGuards ..).2 he⟩)⟩
      | step_ite_nondet_true => exact ⟨[_], 0, fun _ => .step_ite_then⟩
      | step_ite_nondet_false => exact ⟨[_], 0, fun _ => .step_ite_else⟩
      | step_loop_nondet_enter => exact ⟨[_], 0, fun _ => .step_loop_enter⟩
      | step_loop_nondet_exit => exact ⟨[_], 0, fun _ => .step_loop_exit⟩
      | step_seq_inner _ ih =>
        obtain ⟨cs, n, H⟩ := ih
        exact ⟨cs, n, fun r => .step_seq_inner (H r)⟩
      | step_block_body _ ih =>
        obtain ⟨cs, n, H⟩ := ih
        exact ⟨cs, n, fun r => .step_block_body (H r)⟩
      | _ => exact ⟨[], 0, fun _ => .step_det (by constructor <;> assumption)⟩
    obtain ⟨b, m, hb⟩ := ih
    refine ⟨a ++ b, n + m, fun r => ?_⟩
    rw [List.append_assoc]
    exact .step _ _ _ _ _
      (OracleStepE.imp (fun _ _ _ _ _ _ _ => oracleCmdAt_mono π (by omega)) (ha _))
      ((hb r).imp fun _ _ _ =>
        OracleStepE.imp fun _ _ _ _ _ _ _ => oracleCmdAt_mono π (by omega))


omit [DecidableEq P.Expr] in
/-- A CFG reference run over the command relation `E` reads its choices off an oracle, when
    every `E`-step of a command has a choice sequence (`hE`), the bounded evaluator reaches every
    reference value and runtime guard values agree with the reference ones. -/
private theorem oracleCFG_of_star
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hEvalComplete : BoundedEvalComplete P) (hGuards : EngineGuardsAgree P)
    {E : EvalCmdParamE P (CmdExt P) (Event P)}
    (hE : ∀ f σ c σ' evs, E f σ c σ' evs →
      ∃ cs n, ∀ rest, OracleCmdAt π n f σ c σ' evs (cs ++ rest) rest)
    {c c' : CFGConfig String (CmdExt P) P} {evs : List (Event P)}
    (h : StepCFGStarE P E c evs c') :
    ∃ cs n, ∀ rest,
      ReflTransTrace (OracleCFGStepE (OracleCmdAt π n)) (c, cs ++ rest) evs (c', rest) := by
  induction h with
  | refl => exact ⟨[], 0, fun _ => .refl _⟩
  | step x e y _ _ hs _ ih =>
    obtain ⟨a, n, ha⟩ : ∃ cs n, ∀ rest,
        OracleCFGStepE (OracleCmdAt π n) (x, cs ++ rest) e (y, rest) := by
      cases hs with
      | step_cmd h =>
        obtain ⟨cs, n, H⟩ := hE _ _ _ _ _ h
        exact ⟨cs, n, fun r => .step_cmd (H r)⟩
      | _ =>
        refine ⟨[], 0, fun _ => .step_admin ?_⟩
        first
          | exact .fetch ‹_›
          | exact .goto_true ‹_› ⟨hEvalComplete.reach, (hGuards ..).1 ‹_›⟩
          | exact .goto_false ‹_› ⟨hEvalComplete.reach, (hGuards ..).2 ‹_›⟩
          | exact .finish
    obtain ⟨b, m, hb⟩ := ih
    refine ⟨a ++ b, n + m, fun r => ?_⟩
    rw [List.append_assoc]
    exact .step _ _ _ _ _
      (OracleCFGStepE.imp (fun _ _ _ _ _ _ _ => oracleCmdAt_mono π (by omega)) (ha _))
      ((hb r).imp fun _ _ _ =>
        OracleCFGStepE.imp fun _ _ _ _ _ _ _ => oracleCmdAt_mono π (by omega))

omit [DecidableEq P.Expr] in
/-- **Every reference run has a choice sequence.**  A run of the call-aware reference semantics
    has a choice sequence (`RunChoices`), when the bounded evaluator reaches every reference value
    (`hEvalComplete`), runtime guard values agree with the reference ones (`hGuards`), the runtime
    value checks are complete for typed write-back (`hWB`) and every reference base-command
    evaluation passes the engine's value checks with typed choices (`hchk`). -/
theorem runChoices_of_stepStmtExtStarE
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hEvalComplete : BoundedEvalComplete P)
    (hGuards : EngineGuardsAgree P)
    (hWB : WriteBackTypedComplete P)
    (hchk : ∀ f σ c σ' evs, EvalCmdE (P := P) f σ c σ' evs →
      EvalCmdEngE P (ChoiceRecord.typed P) f σ c σ' evs)
    {c c' : Config P (CmdExt P)} {evs : List (Event P)}
    (h : StepStmtExtStarE π c evs c') :
    ∃ cs, RunChoices π c evs c' cs := by
  have hcmd : ∀ f σ c σ' evs, EvalCmdExtE π f σ c σ' evs →
      ∃ cs n, ∀ rest, OracleCmdAt π n f σ c σ' evs (cs ++ rest) rest := by
    intro _ _ _ _ _ h
    induction h using EvalCmdExtE.induct with
    | cmd_sem h =>
      cases h with
      | eval_init_unconstrained hi =>
        obtain ⟨_, hx, _⟩ := hi
        exact ⟨[_], 0, fun _ => ⟨_, rfl,
          hchk _ _ _ _ _ (.eval_init_unconstrained (.init ‹_› hx ‹_›) ‹_› ‹_›),
          .inr ⟨_, _, rfl, hx, .inl ⟨_, _, rfl⟩⟩⟩⟩
      | eval_set_nondet hu =>
        obtain ⟨_, hx, _⟩ := hu
        exact ⟨[_], 0, fun _ => ⟨_, rfl,
          hchk _ _ _ _ _ (.eval_set_nondet (.update ‹_› hx ‹_›) ‹_› ‹_›),
          .inr ⟨_, _, rfl, hx, .inr ⟨_, rfl⟩⟩⟩⟩
      | _ => exact ⟨[], 0, fun _ => ⟨_, rfl, hchk _ _ _ _ _ (by constructor <;> assumption),
          .inl ⟨rfl, rfl⟩⟩⟩
    | call_sem hπ he _ hx ih =>
      obtain ⟨ss, ρ', hss, rfl, hr⟩ | ⟨g, ρE, hg, rfl, hr⟩ := ih
      · obtain ⟨cs, n, hn⟩ :=
          runChoices_of_star π hEvalComplete hGuards (fun _ _ _ _ _ ⟨_, hm⟩ => hm) hr
        exact ⟨cs, n + 1, fun r =>
          .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, hπ, hss, he, hn r, hx, rfl,
            fun _ _ => hEvalComplete.reach, writeBackOK_of_complete hWB hx⟩)⟩
      · obtain ⟨cs, n, hn⟩ :=
          oracleCFG_of_star π hEvalComplete hGuards (fun _ _ _ _ _ ⟨_, hm⟩ => hm) hr
        exact ⟨cs, n + 1, fun r =>
          .inr (.inr ⟨_, _, _, _, _, _, _, _, rfl, hπ, hg, he, hn r, hx, rfl,
            fun _ _ => hEvalComplete.reach, writeBackOK_of_complete hWB hx⟩)⟩
  exact runChoices_of_star π hEvalComplete hGuards hcmd h

/-! ## Deterministic programs resolve no choice -/

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] [DecidableEq P.Expr] in
/-- An engine-realizable step keeps the statements still to be executed deterministic. -/
private theorem StepEngParamE.preserves_det {R : ChoiceRecord P}
    {E : EvalCmdParamE P (CmdExt P) (Event P)}
    {c c' : Config P (CmdExt P)} {evs : List (Event P)} (h : StepEngParamE P R E c evs c') :
    c.noNondetGuards = true ∧ c.allCmds CmdExtDeterministic →
      c'.noNondetGuards = true ∧ c'.allCmds CmdExtDeterministic := by
  induction h <;> (try split) <;> simp_all [Config.noNondetGuards, Stmt.noNondetGuards,
    Block.noNondetGuards, Config.allCmds, Stmt.allCmds, Block.allCmds]

omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOldIdent P] [DecidableEq P.Expr] in
/-- An oracle-reading run over `E` in a deterministic program leaves the oracle alone and keeps
    the program deterministic, given that the deterministic `E`-commands do (`harm`). -/
private theorem oracleStar_det {E : OracleCmdRel P}
    (harm : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → CmdExtDeterministic c = true → o' = o)
    {x y : Config P (CmdExt P) × List P.Val} {evs : List (Event P)}
    (h : ReflTransTrace (OracleStepE E) x evs y) :
    x.1.noNondetGuards = true ∧ x.1.allCmds CmdExtDeterministic →
      y.2 = x.2 ∧ y.1.noNondetGuards = true ∧ y.1.allCmds CmdExtDeterministic := by
  have hstep : ∀ x evs y, OracleStepE E x evs y →
      x.1.noNondetGuards = true ∧ x.1.allCmds CmdExtDeterministic →
      y.2 = x.2 ∧ y.1.noNondetGuards = true ∧ y.1.allCmds CmdExtDeterministic := by
    intro x evs y h
    induction h <;> grind [StepEngParamE.preserves_det, Config.noNondetGuards,
      Stmt.noNondetGuards, Block.noNondetGuards, Config.allCmds, Stmt.allCmds, Block.allCmds]
  induction h <;> grind

omit [HasFvars P] [DecidableEq P.Expr] [HasOldIdent P] in
/-- A deterministic base command of an oracle-reading run leaves the oracle alone. -/
private theorem oracleCmdBase_det {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P}
    {evs : List (Event P)} {o o' : List P.Val} (h : OracleCmdBase f σ c σ' evs o o')
    (hd : CmdExtDeterministic c = true) : o' = o := by
  obtain ⟨_, rfl, -, ⟨-, rfl⟩ | ⟨_, _, -, -, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩⟩ := h <;>
    simp_all [CmdExtDeterministic, CmdDeterministic, ExprOrNondet.isDet]


omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- An oracle-reading CFG run over `E` from a configuration whose remaining commands are
    deterministic (`CFGConfig.allCmds`) leaves the oracle alone and ends in a configuration whose
    remaining commands are deterministic, given that the deterministic `E`-commands leave the oracle alone
    (`harm`). -/
private theorem oracleCFG_det {E : OracleCmdRel P}
    (harm : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' → CmdExtDeterministic c = true → o' = o)
    {x y : CFGConfig String (CmdExt P) P × List P.Val} {evs : List (Event P)}
    (h : ReflTransTrace (OracleCFGStepE E) x evs y) :
    x.1.allCmds CmdExtDeterministic → y.2 = x.2 ∧ y.1.allCmds CmdExtDeterministic := by
  induction h with
  | refl => exact fun h => ⟨rfl, h⟩
  | step _ _ _ _ _ hs _ ih =>
    intro hr
    cases hs with
    | step_cmd he =>
      simp only [CFGConfig.allCmds, List.all_cons, Bool.and_eq_true] at hr
      obtain rfl := harm _ _ _ _ _ _ _ he hr.2.1
      exact ih ⟨hr.1, hr.2.2⟩
    | step_admin hs =>
      apply ih
      cases hs <;> grind [CFGConfig.allCmds, CFG.allCmds]

omit [DecidableEq P.Expr] in
/-- **A deterministic program's runs resolve no choice**: if neither the statements still to be
    executed in `c`, nor any structured callee body of `π`, nor any block of a CFG callee body of
    `π` contains a `.nondet` guard or a nondeterministic base command (`ProgDeterministic`), every
    choice sequence of a reference run from `c` is empty. -/
theorem runChoices_nil_of_deterministic {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {c c' : Config P (CmdExt P)} {evs : List (Event P)}
    {cs : List P.Val} (hdet : ProgDeterministic π c) (h : RunChoices π c evs c' cs) :
    cs = [] := by
  have hcmd : ∀ n f σ c σ' evs o o', OracleCmdAt π n f σ c σ' evs o o' →
      CmdExtDeterministic c = true → o' = o := by
    intro n
    induction n with
    | zero => exact fun _ _ _ _ _ _ _ => oracleCmdBase_det
    | succ n ih =>
      rintro _ _ _ _ _ _ _ (h | ⟨_, _, _, _, _, ss, _, _, rfl, hp, hs, -, hb, -, rfl, -⟩ |
        ⟨_, _, _, _, _, g, _, _, rfl, hp, hg, -, hb, -, rfl, -⟩) hd
      · exact oracleCmdBase_det h hd
      · exact (oracleStar_det ih hb (by simpa [Config.noNondetGuards, Stmt.noNondetGuards,
          Config.allCmds, Stmt.allCmds] using hdet.2.1 _ _ _ hp hs)).1
      · exact (oracleCFG_det ih hb (hdet.2.2 _ _ _ hp hg)).1
  obtain ⟨n, hn⟩ := h
  exact (oracleStar_det (hcmd n) (List.append_nil cs ▸ hn []) hdet.1).1.symm

end Calls

end -- public section

end Imperative
