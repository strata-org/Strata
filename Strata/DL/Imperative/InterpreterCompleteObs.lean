/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCompleteGeneric
public import Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCompleteGeneric
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterObsProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps

/-! # Whole-run completeness for the `ReplayM` observation

The monad-generic completeness of `InterpreterCompleteGeneric.lean`, instantiated at the
counterexample-replay monad `ReplayM`. Key theorems:

* `emitTotal_replay`: `ReplayM`'s `emit` always succeeds when its stop hook is off;
* `runInterp_complete_replay_from`, `runInterp_complete_replay`: completeness on deterministic
  programs; `runInterp_complete_replay_of_agree`: completeness under `EngineAgreesFrom`;
* `evalCmdEngE_complete_replay`: an engine-realizable command evaluation is replayed, consuming
  exactly its oracle segment;
* `OracleWitness`, `OracleTyped`: a runtime oracle segment witnessing semantic choices and passing
  `choose`'s checks;
* `chooseFollows_replay_valid`, `runInterp_replayRun_complete`: `ReplayM` follows its oracle, and
  whole-run completeness along a choice sequence, nondeterministic programs included;
* `runInterp_complete_replay_spec`: `RunInterpComplete` for `ReplayM`, nondeterministic programs
  included, with the oracle built from the derivation. -/

namespace Imperative

public section

section Instances

variable {P : PureExpr} [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]

/-- The runtime oracle segment `rs` witnesses the semantic choices `cs` under `F`: position by
    position, each runtime value denotes the choice, passes the engine's `isValue` check, and is the
    Boolean literal up to metadata (`InterpLang.boolLit?`) when the choice is a Boolean value. -/
@[expose] def OracleWitness {P : PureExpr} [HasBool P] [InterpLang P] (F : P.Factory)
    (rs : List P.Expr) (cs : List P.Val) : Prop :=
  rs.length = cs.length ∧ ∀ rv ∈ rs.zip cs, InterpLang.Denotes F rv.1 rv.2 ∧
        (InterpLang.ops (P := P)).isValue (InterpLang.rfactory F) rv.1 = true ∧
        (rv.2 = HasBool.ttVal F → InterpLang.boolLit? rv.1 = some true) ∧
        (rv.2 = HasBool.ffVal F → InterpLang.boolLit? rv.1 = some false)

/-- The runtime oracle segment `rs` passes `choose`'s type check for the choices `cs` it witnesses:
    position by position, the runtime value has every type at which the choice record `R` allows
    its semantic value under `F`.  Two runtime values denoting the same semantic value need not
    pass the same type checks, so this does not follow from `OracleWitness` and `ValidChoices`. -/
@[expose] def OracleTyped {P : PureExpr} [HasBool P] [InterpLang P] (F : P.Factory)
    (R : ChoiceRecord P) (rs : List P.Expr) (cs : List P.Val) : Prop :=
  ∀ rv ∈ rs.zip cs, ∀ σ ty, R F σ ty rv.2 →
    (InterpLang.ops (P := P)).hasType (InterpLang.rfactory F) rv.1 ty = true

/-! ## `ReplayM` -/

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] in
/-- With the stop hook off (`interruptOn = fun _ => none`), `ReplayM`'s `emit` is a state
    update, so it always succeeds. -/
theorem emitTotal_replay (cfg : (obsReplay (P := P)).Cfg) (h : cfg.interruptOn = fun _ => none) :
    EmitTotal (obsReplay (P := P)) cfg := fun _ _ => ⟨_, replayRun_emit _ _ _ h⟩

/-- **Replay completeness on a deterministic program.** Assume the language's bounded evaluator
    reaches every reference value at some fuel and keeps it at every larger fuel, and every
    deterministic base-command evaluation reachable from `start` passes the engine's value checks.
    Then every reference derivation out of the syntactically deterministic configuration `start`,
    ending at a configuration `final` the monadic interpreter stops at, is reproduced by a `ReplayM`
    run from every configuration `istart` denoting `start` to a configuration denoting `final` at
    every sufficiently large fuel, under any config whose stop hook is off, from any start state,
    prepending runtime events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_replay_from {F : P.Factory} (cfg : (obsReplay (P := P)).Cfg)
    (hcfg : cfg.interruptOn = fun _ => none)
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : (obsReplay (P := P)).St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hg : EngineGuardsAgree P)
    (hchk : EngineChecksAgreeFrom (P := P) (ChoiceRecord.bot P)
              start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
              start evs final)
    (hdet : start.deterministic = true)
    (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : (obsReplay (P := P)).St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        (obsReplay (P := P)).run
            (runInterp (baseStepCmd (m := ReplayM P)) fuel istart) cfg st
          = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs := by
  apply runInterp_complete_of_deterministic_from _ _ (emitTotal_replay _ hcfg) <;> assumption

/-- Replay completeness on a deterministic program, for a language whose bounded evaluator reaches
    every reference value at some fuel and keeps it at every larger fuel, and where every
    deterministic base-command evaluation the reference admits passes the engine's value checks:
    with the stop hook off, every reference derivation out of a syntactically deterministic
    configuration `start` and ending at a configuration `final` the monadic interpreter stops at is
    reproduced by a `ReplayM` run of `runInterp baseStepCmd` from every configuration denoting
    `start` to a configuration denoting `final` at every sufficiently large fuel, prepending runtime
    events that stand for exactly the derivation's events to the trace. -/
theorem runInterp_complete_replay {F : P.Factory} (cfg : (obsReplay (P := P)).Cfg)
    (hcfg : cfg.interruptOn = fun _ => none)
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (hg : EngineGuardsAgree P) (hchk : EngineChecksAgree (P := P) (ChoiceRecord.bot P))
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : (obsReplay (P := P)).St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _)
              start evs final)
    (hdet : start.deterministic = true)
    (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : (obsReplay (P := P)).St), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        (obsReplay (P := P)).run
            (runInterp (baseStepCmd (m := ReplayM P)) fuel istart) cfg st
          = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs := by
  exact runInterp_complete_replay_from _ hcfg hEvalComplete hMono _ _ _ st istart hstart hg
    (hchk.toFrom _) hrun hdet hdone

/-- **Replay completeness against the reference semantics, under engine agreement.** For a
    fuel-monotone bounded evaluator, if every reference step from a configuration a reference
    derivation reaches from `start` is an engine-realizable step under the empty choice record with
    the same events and successor (`EngineAgreesFrom`), then, with the stop hook off, every
    reference derivation out of `start` ending at a configuration `final` the monadic interpreter
    stops at is reproduced by a `ReplayM` run of `runInterp baseStepCmd` from every configuration
    `istart` denoting `start` to a configuration denoting `final` at every sufficiently large fuel,
    from any start state, prepending runtime events that stand for exactly the derivation's events
    to the trace. -/
theorem runInterp_complete_replay_of_agree {F : P.Factory} (cfg : (obsReplay (P := P)).Cfg)
    (hcfg : cfg.interruptOn = fun _ => none) (hMono : BoundedEvalMono P)
    (start final : Config P (Cmd P)) (evs : List (Event P)) (st : (obsReplay (P := P)).St)
    (istart : IConfig P (Cmd P)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := P) (ChoiceRecord.bot P) (@EvalCmdE P _ _)
      (EvalCmdEngE P (ChoiceRecord.bot P)) start)
    (hrun : StepStmtStarE P (@EvalCmdE P _ _) start evs final)
    (hdone : Config.Done final) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : (obsReplay (P := P)).St),
      final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        (obsReplay (P := P)).run
            (runInterp (baseStepCmd (m := ReplayM P)) fuel istart) cfg st
          = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs :=
  runInterp_complete_generic_of_agree _ _
    (stepInterpCompleteGeneric_of_laws _ _ (emitTotal_replay _ hcfg) (chooseResolves_bot _ _) hMono)
    _ _ _ st istart hstart hag hrun hdone

/-! ## `ReplayM` on nondeterministic programs: the oracle built from the derivation -/

omit [HasBoolOps P] in
/-- With the stop hook off, a fuel-monotone bounded evaluator, and a choice
    record whose values pass `choose`'s checks, a base-command evaluation that the reference
    admits with the engine's value checks and with its nondeterministic values drawn from the
    record is performed by a `ReplayM` run of `stepBaseCmdStore` at every sufficiently large
    fuel, consuming exactly an oracle segment `os` and recording exactly its events. -/
theorem evalCmdEngE_complete_replay {R : ChoiceRecord P} (cfg : ReplayCfg P)
    (hcfg : cfg.interruptOn = fun _ => none)
    (hMono : BoundedEvalMono P)
    (hvalid : ValidChoices (P := P) R)
    {f : P.Factory} {σ : IStore P} {σ' : SemanticStore P} {cmd : Cmd P} {evs : Trace P}
    (hd : RStore.Denoting f σ.get)
    (h : EvalCmdEngE P R f (InterpLang.absStore f σ.get) cmd σ' evs) :
    ∃ (f0 : Nat) (os : List P.Expr) (σi : IStore P) (revs : List (IEvent P)),
      InterpLang.absStore f σi.get = σ' ∧ RStore.Denoting f σi.get ∧
      revs.map (REvent.abs f) = evs ∧
      ∀ (fuel : Nat), f0 ≤ fuel →
      ∀ (rest u : List P.Expr) (t : List (IEvent P)),
        replayRun (stepBaseCmdStore (m := ReplayM P) fuel (InterpLang.rfactory f) σ cmd) cfg
            { remaining := os ++ rest, usedRev := u, traceRev := t }
          = (.ok σi, { remaining := rest, usedRev := os.reverse ++ u,
                       traceRev := revs.reverse ++ t }) := by
  have hsd := storeDenotes_absStore hd
  cases h with
  | @eval_init _ _ _ _ _ x _ hx he hok =>
    obtain ⟨n, r, hb, hr⟩ := hok.1 σ.get _ hsd he
    obtain ⟨hv, ht⟩ := hok.2 σ.get n r hsd hb
    refine ⟨n, [], σ.update x r, [], by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr, rfl, fun k hk rest u t => ?_⟩
    simp [stepBaseCmdStore, absStore_eq_none hd _ hx, hMono _ _ _ _ _ _ hk hb, hv, ht,
      replayRun_pure]
  | @eval_set _ _ _ _ x _ _ hx he hok =>
    obtain ⟨ro, hro, -⟩ := absStore_eq_some _ _ hx
    obtain ⟨n, r, hb, hr⟩ := hok.1 σ.get _ hsd he
    obtain ⟨hv, ht⟩ := hok.2 σ.get n r hsd hb ro hro
    refine ⟨n, [], σ.update x r, [], by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr, rfl, fun k hk rest u t => ?_⟩
    simp [stepBaseCmdStore, hro, hMono _ _ _ _ _ _ hk hb, hv, ht, replayRun_pure]
  | @eval_init_nondet _ _ ty v x _ hx hR =>
    obtain ⟨r, hr, hv, ht, -, -⟩ := hvalid _ _ _ _ hR
    refine ⟨0, [r], σ.update x r, [], by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr, rfl, fun k hk rest u t => ?_⟩
    simp [stepBaseCmdStore, absStore_eq_none hd _ hx, replayRun_bind, replayRun_pure,
      -bind_pure_comp,
      replayRun_choose_cons _ _ _ cfg { remaining := r :: rest, usedRev := u, traceRev := t }
        r rest rfl hv ht]
  | @eval_set_nondet _ _ x ty v _ _ hx hty hR _ hok =>
    obtain ⟨ro, hro, -⟩ := absStore_eq_some _ _ hx
    obtain ⟨r, hr, hv, ht, -, -⟩ := hvalid _ _ _ _ hR
    obtain ⟨-, hs⟩ := hok σ.get ro r hsd hro hr
    refine ⟨0, [r], σ.update x r, [], by simp [InterpLang.absStore_update _ _ hr],
      by simpa using hd.update _ hr, rfl, fun k hk rest u t => ?_⟩
    simp [stepBaseCmdStore, hro, hty σ.get ro hsd hro, replayRun_bind, replayRun_pure, hv, hs,
      replayRun_choose_cons _ _ _ cfg { remaining := r :: rest, usedRev := u, traceRev := t }
        r rest rfl hv ht]
  | _ =>
    first
      | refine ⟨0, [], σ, [.assert ⟨InterpLang.rfactory f, σ.get, _, _, _⟩], rfl, hd, rfl,
          fun _ _ rest u t => ?_⟩
      | refine ⟨0, [], σ, [.assume ⟨InterpLang.rfactory f, σ.get, _, _, _⟩], rfl, hd, rfl,
          fun _ _ rest u t => ?_⟩
      | refine ⟨0, [], σ, [.cover ⟨InterpLang.rfactory f, σ.get, _, _, _⟩], rfl, hd, rfl,
          fun _ _ rest u t => ?_⟩
    simp only [stepBaseCmdStore_assert, stepBaseCmdStore_assume, stepBaseCmdStore_cover,
      Cmd.rEmittedEvents, List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind,
      List.nil_append, replayRun_bind, replayRun_emit _ _ _ hcfg, List.reverse_nil,
      List.reverse_cons, List.cons_append]
    rfl

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] in
/-- **`ReplayM` follows its oracle**: a state's pending choices are witnessed by a prefix of its
    oracle tail (`OracleWitness`) that passes `choose`'s type check at every type the choice record
    allows (`OracleTyped`). -/
theorem chooseFollows_replay_valid {R : ChoiceRecord P} (cfg : ReplayCfg P) :
    ChooseFollows (obsReplay (P := P)) cfg F R (fun st cs => ∃ rs, rs <+: st.remaining ∧
      OracleWitness F rs cs ∧ OracleTyped F R rs cs) := by
  refine ⟨?_, fun ev _ st _ _ h hp => ?_⟩
  · rintro σr σ ty v cs st - ⟨_ | ⟨r, rs⟩, ⟨t, ht⟩, ⟨hlen, hw⟩, hty⟩ hR
    · cases hlen
    obtain ⟨hden, hv, htt, hff⟩ := hw (r, v) (.head _)
    refine ⟨r, _, replayRun_choose_cons _ _ _ _ st r (rs ++ t) ht.symm hv
      (hty (r, v) (.head _) σ ty hR), hden, htt, hff, rfl, rs, ⟨t, rfl⟩,
      ⟨by simpa using hlen, fun rv h => hw rv (.tail _ h)⟩, fun rv h => hty rv (.tail _ h)⟩
  · obtain rfl := (congrArg Prod.snd h).symm.trans (replayRun_emit_state ev cfg st)
    exact hp

/-- **Whole-run `ReplayM` completeness along a choice sequence, for base commands.**  If an
    oracle-reading run of the base-command semantics from `start.abs`, the configuration a
    tracked interpreter configuration `start` stands for, resolves its choices as `cs`
    (`RunChoicesParam` over `OracleCmdEngE R`), the run ends in a configuration `final` the
    monadic interpreter stops at, and the bounded evaluator is fuel-monotone, then
    from every replay state whose oracle tail begins with a runtime segment `rs` witnessing `cs`
    (`OracleWitness`) and passing `choose`'s type check (`OracleTyped`), under every config whose
    stop hook is off, `runInterp baseStepCmd` from `start` reaches a configuration denoting `final`
    at every large enough fuel, prepending runtime events that stand for exactly the run's events
    to the trace. -/
theorem runInterp_replayRun_complete {R : ChoiceRecord P} (cfg : ReplayCfg P) {F : P.Factory}
    (hcfg : cfg.interruptOn = fun _ => none)
    (hMono : BoundedEvalMono P)
    {start : IConfig P (Cmd P)} {final : Config P (Cmd P)} {evs : List (Event P)}
    {cs : List P.Val}
    (hrun : RunChoicesParam R (OracleCmdEngE R)
      (start.abs F) evs final cs)
    (hds : start.Denoting F) (htr : start.Tracked)
    (hdone : Config.Done final) (st : ReplayState P) (rs : List P.Expr)
    (hpre : rs <+: st.remaining)
    (hrs : OracleWitness F rs cs) (hty : OracleTyped F R rs cs) :
    ∃ (f0 : Nat) (final' : IConfig P (Cmd P)) (st' : ReplayState P), final'.Denotes F final ∧
      (∀ fuel, f0 ≤ fuel →
        replayRun (runInterp (baseStepCmd (m := ReplayM P)) fuel start) cfg st
          = (.ok final', st'))
      ∧ (obsReplay (P := P)).TraceExt F st st' evs := by
  exact runInterp_complete_follows obsReplay cfg (Q := fun _ => True) _
    (fun _ _ _ _ => emitTotal_replay cfg hcfg _ _) (chooseFollows_replay_valid cfg)
    hMono hrun hds htr hdone (fun _ _ => trivial) st ⟨rs, hpre, hrs, hty⟩

/-- With the stop hook off, a fuel-monotone bounded evaluator, and a choice record
    whose values pass `choose`'s checks, an engine-realizable step out of the abstraction of a
    tracked denoting configuration `c` is performed by one `ReplayM` step of `stepInterp` at every
    sufficiently large fuel, consuming exactly an oracle segment `os`, recording runtime events
    `revs` that stand for the step's events, and reaching a tracked denoting configuration that
    stands for the step's successor. -/
private theorem stepEngE_replay {R : ChoiceRecord P} (cfg : ReplayCfg P) {F : P.Factory}
    (hcfg : cfg.interruptOn = fun _ => none)
    (hMono : BoundedEvalMono P)
    (hvalid : ValidChoices (P := P) R) :
    ∀ (c : IConfig P (Cmd P)) (c' : Config P (Cmd P)) (evs : List (Event P)),
      c.Tracked → c.Denoting F → StepEngE P R (c.abs F) evs c' →
      ∃ (f0 : Nat) (os : List P.Expr) (cy : IConfig P (Cmd P)) (revs : List (IEvent P)),
        cy.abs F = c' ∧ cy.Denoting F ∧ cy.Tracked ∧ revs.map (REvent.abs F) = evs ∧
        ∀ fuel, f0 ≤ fuel → ∀ (rest u : List P.Expr) (t : List (IEvent P)),
          replayRun (stepInterp (baseStepCmd (m := ReplayM P)) fuel c) cfg
              { remaining := os ++ rest, usedRev := u, traceRev := t }
            = (.ok cy, { remaining := rest, usedRev := os.reverse ++ u,
                         traceRev := revs.reverse ++ t }) := by
  intro c _ _ ht hd h
  generalize hx : c.abs F = x at h
  induction h generalizing c with
  | step_cmd hc =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨n, os, σi, revs, hσ, hdσ, hr, h1⟩ :=
      evalCmdEngE_complete_replay cfg hcfg hMono hvalid hd.1 hc
    exact ⟨n, os, .terminal { ie with store := σi }, revs, by simp [IConfig.abs, IEnv.abs, hσ],
      ⟨hdσ, hd.2⟩, trivial, hr,
      fun k hk rest u t => obs_stepInterp_cmd_fwd obsReplay _ _ _ _ _ _ _ (hd.2 ▸ h1 k hk rest u t)⟩
  | @step_seq_inner _ _ _ ss hs ih =>
    rcases (IConfig.abs_eq_seq ..).1 hx with ⟨ci, rfl, hci⟩ | ⟨rfl, ci, k, rfl, hci⟩
    · obtain ⟨n, os, c', revs, ha, hd', ht', hr, h1⟩ := ih ci ht hd hci
      have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done')
      refine ⟨n, os, .seq c' ss, revs, by simp [IConfig.abs, ha], hd', ht', hr,
        fun k hk rest u t => ?_⟩
      exact obs_seq_fwd obsReplay _ _ _ _ _ _ _ _ hnd.1 hnd.2 (h1 k hk rest u t)
    · obtain ⟨c0, ha0, ht0, hd0, hs0⟩ := IConfig.seqs_peel (m := ReplayM P) F ci k
      obtain ⟨n, os, c', revs, ha, hd', ht', hr, h1⟩ :=
        ih c0 (ht0 ▸ ht) (hd0 ▸ hd) (ha0.trans hci)
      refine ⟨n, os, c'.seqNil, revs, by simp [ha], by simpa using hd', by simpa using ht', hr,
        fun k hk rest u t => ?_⟩
      rw [hs0 _ _ (hci ▸ hs.not_done'), map_eq_pure_bind, replayRun_bind, h1 k hk rest u t]
      rfl
  | @step_block_body _ _ _ l _ hs ih =>
    obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IConfig.abs_eq_block ..).1 hx
    obtain ⟨n, os, c', revs, ha, hd', ht', hr, h1⟩ := ih ci ht.2 hd.2 hci
    have hnd := IConfig.not_done_of_abs (hci ▸ hs.not_done')
    have hl := StepStmtE.lvl_defines evalCmdE_cmdDefsSound
      (hs.toStepStmtE' (EvalCmd := @EvalCmdE P _ _) fun _ _ _ _ _ h => h.toEvalCmdE)
    refine ⟨n, os, .block l (fr.record ci.levelCmd?) c', revs, by simp [IConfig.abs, ha, hfr],
      ⟨by simpa using hd.1, hd'⟩, ⟨ScopeFrame.record_exact ht.1 (by
        simpa [← hci, ← ha, InterpLang.absStore_isSome hd'.lvl,
          InterpLang.absStore_isSome hd.2.lvl] using hl), ht'⟩, hr, fun k hk rest u t => ?_⟩
    exact obs_block_fwd obsReplay _ _ _ _ _ _ _ _ _ hnd.1 hnd.2 (h1 k hk rest u t)
  | @step_ite_nondet v tss ess _ ρ hR hv =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨r, -, hvr, htr, htt, hff⟩ := hvalid F _ _ _ hR
    rcases hv with rfl | rfl
    · have hl := htt rfl
      refine ⟨0, [r], .block .none (.opened ie.store) (.stmts tss ie), [],
        by simp [IConfig.abs, IEnv.abs, ScopeFrame.opened], ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ rest u t => ?_⟩
      simp [stepInterp, resolveGuard, hd.2, hl, replayRun_bind, replayRun_pure, -bind_pure_comp,
        replayRun_choose_cons _ _ _ cfg
          { remaining := r :: rest, usedRev := u, traceRev := t }
          r rest rfl hvr htr]
    · have hl := hff rfl
      refine ⟨0, [r], .block .none (.opened ie.store) (.stmts ess ie), [],
        by simp [IConfig.abs, IEnv.abs, ScopeFrame.opened, (HasBool.ttVal_ne_ffVal F).symm],
        ⟨hd.1, hd⟩, by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ rest u t => ?_⟩
      simp [stepInterp, resolveGuard, hd.2, hl, replayRun_bind, replayRun_pure, -bind_pure_comp,
        replayRun_choose_cons _ _ _ cfg
          { remaining := r :: rest, usedRev := u, traceRev := t }
          r rest rfl hvr htr]
  | @step_loop_nondet v mm inv body md ρ hR hv =>
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_stmt ..).1 hx
    obtain ⟨r, -, hvr, htr, htt, hff⟩ := hvalid F _ _ _ hR
    rcases hv with rfl | rfl
    · have hl := htt rfl
      refine ⟨0, [r],
        .seq (.block .none (.opened ie.store) (.stmts body ie)) [.loop .nondet mm inv body md], [],
        by simp [IConfig.abs, ScopeFrame.opened, IEnv.abs], ⟨hd.1, hd⟩,
        by simp [IConfig.Tracked, IConfig.lvl], rfl, fun _ _ rest u t => ?_⟩
      simp [stepInterp, resolveGuard, hd.2, hl, replayRun_bind, replayRun_pure, -bind_pure_comp,
        replayRun_choose_cons _ _ _ cfg
          { remaining := r :: rest, usedRev := u, traceRev := t }
          r rest rfl hvr htr]
    · have hl := hff rfl
      refine ⟨0, [r], .terminal ie, [],
        by simp [IConfig.abs, IEnv.abs, (HasBool.ttVal_ne_ffVal F).symm], hd, trivial, rfl,
        fun _ _ rest u t => ?_⟩
      simp [stepInterp, resolveGuard, hd.2, hl, replayRun_bind, replayRun_pure, -bind_pure_comp,
        replayRun_choose_cons _ _ _ cfg
          { remaining := r :: rest, usedRev := u, traceRev := t }
          r rest rfl hvr htr]
  | _ =>
    exact (stepInterp_admin_complete obsReplay (fun _ _ => baseStepCmd) cfg hMono
      (evs := []) (by constructor <;> assumption) _ hx hd ht).elim
      fun n ⟨cy, ha, hd', ht', _, h1⟩ =>
      ⟨n, [], cy, [], ha, hd', ht', rfl, fun k hk rest u t => h1 k k k hk hk hk _⟩

/-- With the stop hook off, a fuel-monotone bounded evaluator, and a choice record
    whose values pass `choose`'s checks, an engine-realizable run out of the abstraction of a
    tracked denoting configuration `c`, ending at a configuration the driver stops at, is
    performed by a `ReplayM` run of `runInterp baseStepCmd` at every sufficiently large fuel,
    consuming exactly an oracle segment `os` and recording runtime events `revs` that stand for
    the run's events, reaching a configuration that denotes the run's final one. -/
private theorem runEngE_replay {R : ChoiceRecord P} (cfg : ReplayCfg P) {F : P.Factory}
    (hcfg : cfg.interruptOn = fun _ => none)
    (hMono : BoundedEvalMono P)
    (hvalid : ValidChoices (P := P) R) :
    ∀ (c : IConfig P (Cmd P)) (final : Config P (Cmd P)) (evs : List (Event P)),
      c.Tracked → c.Denoting F → StepEngStarE P R (c.abs F) evs final → Config.Done final →
      ∃ (f0 : Nat) (os : List P.Expr) (final' : IConfig P (Cmd P)) (revs : List (IEvent P)),
        final'.Denotes F final ∧ revs.map (REvent.abs F) = evs ∧
        ∀ fuel, f0 ≤ fuel → ∀ (rest u : List P.Expr) (t : List (IEvent P)),
          replayRun (runInterp (baseStepCmd (m := ReplayM P)) fuel c) cfg
              { remaining := os ++ rest, usedRev := u, traceRev := t }
            = (.ok final', { remaining := rest, usedRev := os.reverse ++ u,
                             traceRev := revs.reverse ++ t }) := by
  intro c _ _ ht hd h hdone
  generalize hx : c.abs F = x at h
  induction h generalizing c with
  | refl =>
    subst hx
    exact ⟨0, [], c, [], ⟨hd, ht, rfl⟩, rfl, fun _ _ rest u t => by
      simp [runInterp_of_abs_done _ _ hdone, replayRun_pure]⟩
  | step _ _ _ _ _ hs _ ih =>
    subst hx
    obtain ⟨a, os1, c1, r1, ha, hd1, ht1, hr1, h1⟩ :=
      stepEngE_replay cfg hcfg hMono hvalid _ _ _ ht hd hs
    obtain ⟨b, os2, cf, r2, hf, hr2, h2⟩ := ih c1 ht1 hd1 hdone ha
    refine ⟨a + b + 1, os1 ++ os2, cf, r1 ++ r2, hf, by simp [hr1, hr2],
      fun | 0, _ => by omega | k + 1, _ => fun rest u t => ?_⟩
    have hnd := IConfig.not_done_of_abs hs.not_done'
    rw [runInterp_succ_nonterminal _ _ _ hnd.1 hnd.2, replayRun_bind, List.append_assoc,
      h1 (k + 1) (by omega)]
    simp [h2 k (by omega)]

/-- **`RunInterpComplete` for the replay observation**, nondeterministic programs included: given a
    fuel-monotone bounded evaluator, every engine-realizable run to a configuration the
    driver stops at, over a choice record whose values pass `ReplayM`'s checks (`ValidChoices`), and
    where every deterministic base-command evaluation passes the engine's value checks, is
    reproduced from the empty trace by a `ReplayM` run of `runInterp baseStepCmd` at some fuel
    and from some oracle, recording exactly the run's events. -/
theorem runInterp_complete_replay_spec :
    RunInterpComplete P (ReplayM P)
      (obsReplay (P := P)) := by
  intro hMono F R _ final evs istart ⟨hd, ht, rfl⟩ hrun _ hvalid hdone
  obtain ⟨f0, os, final', revs, hf, hr, H⟩ :=
    runEngE_replay {} rfl hMono hvalid _ _ _ ht hd hrun hdone
  exact ⟨f0, {}, { remaining := os ++ [], usedRev := [], traceRev := [] }, _, final', revs, rfl,
    H f0 (Nat.le_refl _) [] [] [], hf, by simp [obsReplay], hr⟩

end Instances

end -- public section

end Imperative
