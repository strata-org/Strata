/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkSimProps
public import Strata.DL.Imperative.InterpreterTowerProps
public import Strata.Languages.Core.ConfigWF
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplayProps
import all Strata.Languages.Core.Counterexample.BackLinkSim
import all Strata.Languages.Core.Counterexample.BackLinkSimProps
import all Strata.Languages.Core.ConfigWF
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import Strata.DL.Imperative.Counterexample.Tactics
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.Languages.Core.IdentifiersProps
import Strata.Languages.Core.InterpreterDomainProps
public import Strata.Languages.Core.Counterexample.BackLinkRelSim
import all Strata.Languages.Core.Counterexample.BackLinkRelSim
public import Strata.Languages.Core.ReplayWF
import all Strata.DL.Imperative.CmdSemantics

/-! # Replay-vs-replay simulation over a configuration relation, proved once

`claim_back_of_simulation` generalized to phases that rewrite statements: the runs are
related by a configuration relation `R` and by the state relation `StRel` of a relational
context `RelCtx` (same oracle cursor, traces related by an event relation `ER`).  Each
downstream step either *stutters* (emits nothing, draws nothing, stays related to the same
upstream configuration) or is dominated by one upstream step (*lockstep*, `RelDom`).  The
equality instance of `BackLinkSim` is the special case that never stutters
(`relStepSim_of_replaySimulation`).

Key theorems: `runInterp_relSim`, `claim_back_of_relSimulation`,
`claim_back_of_relSimulation_free`, `evAgree_transfer`, `relStepSim_of_replaySimulation`.
Key definitions: `StuttersRel`, `RelStepSim`, `EvAgree`.

Building blocks for relational simulations between two replay runs whose stores agree
outside a set of names `fresh` (names a phase introduced, which the source never mentions)
and whose factories are equal: a base command, a condition, a spec event, stepped at
downstream fuel `k ≤` upstream fuel `m`, with events related by `EvAgree fresh`
(`stepBaseCmdStore_rel`, and `cel_stepBaseCmdStore_rel` for a command that draws nothing
from a free oracle). -/

namespace Core

open Imperative

public section

/-! ## The whole run, from a per-step obligation -/

/-- A stuttering step stutters relationally. -/
theorem Stutters.toRel {K : RelCtx} (hK : K.Compat)
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    {X' : ReplayM Expression (IConfig Expression Command)} {c : IConfig Expression Command}
    (h : Stutters K R X' c) : StuttersRel K R X' c := fun s' s hst => by
  rcases h s' with ⟨_, hrun, _⟩ | ⟨_, hrun⟩ <;> simp_all [hst.fired hK]

/-- Running `f <$> X` runs `X` and applies `f` to a success. -/
private theorem rrun_map {α β : Type} (f : α → β) (X : ReplayM Expression α)
    (cfg : ReplayCfg Expression) (s : ReplayState Expression) :
    rrun (f <$> X) cfg s = ((rrun X cfg s).1.map f, (rrun X cfg s).2) := by
  rw [← bind_pure_comp, rrun_bind]
  rcases rrun X cfg s with ⟨_ | _, _⟩ <;> simp [rrun_pure, Except.map]

/-- Domination with results compared through the expansion of sequence towers carries over to
    computations whose results have the same expansions. -/
private theorem RelDom.unseqs {K : RelCtx}
    {X' Y' X Y : ReplayM Expression (IConfig Expression Command)}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (h' : (·.unseqs) <$> X' = (·.unseqs) <$> Y') (h : (·.unseqs) <$> X = (·.unseqs) <$> Y)
    (hd : RelDom K Y' Y fun a' a => R a'.unseqs a.unseqs) :
    RelDom K X' X fun a' a => R a'.unseqs a.unseqs := by
  have e' := fun s => congrArg (fun Z => rrun Z K.cfgD s) h'
  have e := fun s => congrArg (fun Z => rrun Z K.cfgU s) h
  simp only [rrun_map, Prod.mk.injEq] at e' e
  refine ⟨fun s0 => (e s0).2 ▸ hd.1 s0, fun s' s hst => ⟨fun a' s'1 hrun => ?_, ?_⟩⟩
  · obtain ⟨e1, e2⟩ := hrun ▸ e' s'
    rcases hY : (rrun Y' K.cfgD s').1 with _ | b' <;> rw [hY] at e1 <;>
      simp only [Except.map, reduceCtorEq, Except.ok.injEq] at e1
    rcases (hd.2 s' s hst).1 b' s'1 (Prod.ext hY e2.symm) with ⟨b, s1, hb, hR, hst1⟩ | hf
    · obtain ⟨f1, f2⟩ := e s
      rw [hb] at f1 f2
      rcases hX : (rrun X K.cfgU s).1 with _ | a <;> rw [hX] at f1 <;>
        simp only [Except.map, reduceCtorEq, Except.ok.injEq] at f1
      exact .inl ⟨a, s1, Prod.ext hX f2, show R a'.unseqs a.unseqs by rw [e1, f1]; exact hR, hst1⟩
    · exact .inr ((e s).2 ▸ hf)
  · intro err s'1 hrun hf
    obtain ⟨e1, e2⟩ := hrun ▸ e' s'
    rcases hY : (rrun Y' K.cfgD s').1 with err' | b' <;> rw [hY] at e1 <;> simp [Except.map] at e1
    exact (e s).2 ▸ (hd.2 s' s hst).2 err' s'1 (Prod.ext hY e2.symm) hf

/-- A relational stutter with results compared through the expansion of sequence towers carries
    over to a computation whose results have the same expansions, against an upstream
    configuration with the same expansion. -/
private theorem StuttersRel.unseqs {K : RelCtx}
    {X' Y' : ReplayM Expression (IConfig Expression Command)} {c c0 : IConfig Expression Command}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (h' : (·.unseqs) <$> X' = (·.unseqs) <$> Y') (hc : c0.unseqs = c.unseqs)
    (hS : StuttersRel K (fun a' a => R a'.unseqs a.unseqs) Y' c0) :
    StuttersRel K (fun a' a => R a'.unseqs a.unseqs) X' c := by
  have e' := fun s => congrArg (fun Z => rrun Z K.cfgD s) h'
  simp only [rrun_map, Prod.mk.injEq] at e'
  refine fun s' s hst => ⟨fun c'1 s'1 hrun => ?_, fun err s'1 hrun hf => ?_⟩
  · obtain ⟨e1, e2⟩ := hrun ▸ e' s'
    rcases hY : (rrun Y' K.cfgD s').1 with _ | b' <;> rw [hY] at e1 <;>
      simp only [Except.map, reduceCtorEq, Except.ok.injEq] at e1
    obtain ⟨hst1, hR⟩ := (hS s' s hst).1 b' s'1 (Prod.ext hY e2.symm)
    exact ⟨hst1, show R c'1.unseqs c.unseqs by rw [e1, ← hc]; exact hR⟩
  · obtain ⟨e1, e2⟩ := hrun ▸ e' s'
    rcases hY : (rrun Y' K.cfgD s').1 with err' | b' <;> rw [hY] at e1 <;> simp [Except.map] at e1
    exact (hS s' s hst).2 err' s'1 (Prod.ext hY e2.symm) hf

/-- Expanding sequence towers does not change whether the monadic interpreter stops at a
    configuration. -/
private theorem IConfig.done_unseqs (c : IConfig Expression Command) :
    IConfig.Done c.unseqs ↔ IConfig.Done c := by
  cases c <;> exact .rfl

/-- **A relational simulation through the expansion of sequence towers.**  When every downstream
    step from configurations related by `R` either stutters or is dominated by one upstream step,
    with results related by `R` after the expansion of sequence towers (`IConfig.unseqs`), then
    `R` read through the expansion is a relational simulation (`RelStepSim`). -/
theorem relStepSim_unseqs {K : RelCtx} {sc' sc : StepCmdM Expression Command (ReplayM Expression)}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (h : ∀ c' c, R c' c → ¬ IConfig.Done c' → ∀ k m, 1 ≤ k → k ≤ m →
      StuttersRel K (fun a' a => R a'.unseqs a.unseqs) (stepInterp sc' k c') c ∨
        (¬ IConfig.Done c ∧
          RelDom K (stepInterp sc' k c') (stepInterp sc m c) fun a' a => R a'.unseqs a.unseqs)) :
    RelStepSim K sc' sc fun c' c => R c'.unseqs c.unseqs := by
  intro c' c hR hd k m hk hkm
  rcases h _ _ hR (by rwa [IConfig.done_unseqs c']) k m hk hkm with hS | ⟨hcd, hdom⟩
  · exact .inl (StuttersRel.unseqs (stepInterp_unseqs sc' k c') (IConfig.unseqs_unseqs c) hS)
  · exact .inr ⟨by rwa [IConfig.done_unseqs c] at hcd,
      RelDom.unseqs (stepInterp_unseqs sc' k c') (stepInterp_unseqs sc m c) hdom⟩

/-- A run from a configuration whose abstraction is stopping returns it. -/
private theorem runInterp_done {sc : StepCmdM Expression Command (ReplayM Expression)} (n : Nat)
    {c : IConfig Expression Command} (h : IConfig.Done c) : runInterp sc n c = pure c := by
  cases c <;> cases h <;> cases n <;> rfl

/-- A fueled run from a configuration whose abstraction is not stopping steps once. -/
private theorem runInterp_step {sc : StepCmdM Expression Command (ReplayM Expression)} (n : Nat)
    {c : IConfig Expression Command} (h : ¬ IConfig.Done c) :
    runInterp sc (n + 1) c = stepInterp sc (n + 1) c >>= runInterp sc n := by
  cases c <;> first | rfl | exact absurd trivial h

/-- **Whole-run relational simulation.**  From related configurations and states, a
    downstream run at fuel `n` that fires the downstream target predicate is matched by
    an upstream run at any fuel `m ≥ n` that fires the upstream one. -/
theorem runInterp_relSim {K : RelCtx} (hK : K.Compat)
    {sc' sc : StepCmdM Expression Command (ReplayM Expression)}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (hsim : RelStepSim K sc' sc R) (hg : StepGrows K.cfgU sc) :
    ∀ (n m : Nat), n ≤ m → ∀ (c' c : IConfig Expression Command) (s' s : ReplayState Expression),
      R c' c → StRel K s' s →
      FiredD K (rrun (runInterp sc' n c') K.cfgD s').2 →
      FiredU K (rrun (runInterp sc m c) K.cfgU s).2 := fun n => by
  have hG := runInterp_grows hg
  induction n <;> intro m hle c' c s' s hR hst hf <;> by_cases hd : IConfig.Done c'
  any_goals
    refine (hst.fired hK ?_).mono (hG m c s)
    first
      | rwa [runInterp_done _ hd] at hf
      | cases c' <;> exact hf
  rename_i n ih
  rw [runInterp_step _ hd, rrun_bind] at hf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rcases hsim c' c hR hd (n + 1) (m + 1) (Nat.le_add_left 1 n) hle with hS | ⟨hcu, -, hdom⟩
  · have ⟨hok, herr⟩ := hS s' s hst
    split at hf
    · exact ih (m + 1) (Nat.le_of_succ_le hle) _ _ _ _ (hok _ _ ‹_›).2 (hok _ _ ‹_›).1 hf
    · exact (herr _ _ ‹_› hf).mono (hG _ c s)
  have ⟨hok, herr⟩ := hdom s' s hst
  rw [runInterp_step _ hcu]
  split at hf
  · rcases hok _ _ ‹_› with ⟨_, _, hrun, hR', hs1⟩ | hfu
    · rw [rrun_bind, hrun]
      exact ih m (Nat.le_of_succ_le_succ hle) _ _ _ _ hR' hs1 hf
    · apply_rules [hfu.mono, rrun_bind_ext]
  · exact (herr _ _ ‹_› hf).mono (rrun_bind_ext _ (hG m) s)

/-- Claim transport through a relational simulation of the two production runs whose
    upstream oracle is free exactly when `b` holds: a downstream claim `c'` genuine and
    feasible at fuel `f` gives an upstream claim, from a configuration `c` related to `c'`'s,
    genuine and feasible at fuel `f' ≥ f`,
    with any oracle `o` when `b` holds and `c'`'s oracle otherwise. -/
private theorem cel_claimBack {π' π : String → Option Procedure} {d : Nat}
    {t' t : AssertId Expression}
    {f f' : Nat} (hle : f ≤ f') {ER : IEvent Expression → IEvent Expression → Prop}
    (hER : EventTransfer t' t f f' ER)
    {Extra : IEvent Expression → Prop} (hx : ∀ ev, Extra ev → assertFailureHalt t' f ev = false)
    {b : Bool} {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (hsim : RelStepSim (relProdCtx t' t f f' ER Extra b)
      (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d) R)
    (c' : CexA Expression Command) (c : IConfig Expression Command)
    (hR : R c'.cfg c)
    {o : List Expression.Expr} (ho : b = true ∨ c'.oracle = o)
    (h : genuineFeasible π' t' f c' d) : genuineFeasible π t f' ⟨c, o⟩ d := by
  simp only [genuineFeasible_iff_genuineEnforced, genuineEnforced, Calls.genuineEnforced,
    Calls.runCallInterp_eq, runReplay_genuine_iff] at h ⊢
  exact runInterp_relSim (relProdCtx_compat hER _ hx b) hsim
    (fun k => replayStepCmd_grows _ π k d k)
    f _ hle _ _ _ _ hR ⟨by simpa [relProdCtx] using ho, by simp [relProdCtx], .nil⟩ h

/-- **Claim transport through a relational simulation.**  If the production runs of the
    downstream table `π'` (target `t'`, fuel `f`) and of the upstream table `π` (target
    `t`, fuel `f' ≥ f`) are related by a relational simulation, the start configurations are
    related and the oracles are the same,
    a downstream claim genuine and feasible at fuel `f` gives an upstream claim genuine and
    feasible at fuel `f'`. -/
theorem claim_back_of_relSimulation {π' π : String → Option Procedure} {d : Nat}
    {t' t : AssertId Expression} {f f' : Nat} (hle : f ≤ f')
    {ER : IEvent Expression → IEvent Expression → Prop} (hER : EventTransfer t' t f f' ER)
    {Extra : IEvent Expression → Prop}
    (hx : ∀ ev, Extra ev → assertFailureHalt t' f ev = false)
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (hsim : RelStepSim (relProdCtx t' t f f' ER Extra)
      (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d) R)
    (c' : CexA Expression Command) (c : IConfig Expression Command)
    (hR : R c'.cfg c)
    (h : genuineFeasible π' t' f c' d) : genuineFeasible π t f' ⟨c, c'.oracle⟩ d :=
  cel_claimBack hle hER hx hsim c' c hR (.inr rfl) h

/-- **Claim transport through a relational simulation whose upstream run never draws.**  If the
    production runs of the downstream table `π'` (target `t'`, fuel `f`) and of the upstream
    table `π` (target `t`, fuel `f' ≥ f`) are related by a relational simulation whose context
    sets `freeOracle`, and the start configurations are related, a downstream claim genuine and
    feasible at fuel `f` gives an upstream claim genuine and feasible at fuel `f'`.  Because the
    upstream run never draws from the oracle, the upstream claim may carry any oracle `o`, not
    only the downstream claim's. -/
theorem claim_back_of_relSimulation_free {π' π : String → Option Procedure} {d : Nat}
    {t' t : AssertId Expression} {f f' : Nat} (hle : f ≤ f')
    {ER : IEvent Expression → IEvent Expression → Prop} (hER : EventTransfer t' t f f' ER)
    {Extra : IEvent Expression → Prop}
    (hx : ∀ ev, Extra ev → assertFailureHalt t' f ev = false)
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    (hsim : RelStepSim (relProdCtx t' t f f' ER Extra true)
      (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d) R)
    (c' : CexA Expression Command) (c : IConfig Expression Command)
    (hR : R c'.cfg c)
    (o : List Expression.Expr)
    (h : genuineFeasible π' t' f c' d) : genuineFeasible π t f' ⟨c, o⟩ d :=
  cel_claimBack hle hER hx hsim c' c hR (.inl rfl) h

/-! ## Evaluation agreement outside a set of names

The event relation of phases whose two runs differ only on the values of names the
source never mentions: the stores agree outside those names, and a condition mentioning
none of them evaluates alike. -/

/-- **Evaluation agreement.**  A condition mentioning no name of `fresh` evaluates alike
    in two stores that agree outside `fresh`, under a well-formed factory, when
    the upstream store is closed. -/
theorem evalBounded_agree {fresh : Expression.Ident → Prop} {F : Lambda.Factory CoreLParams}
    (hF : FactoryOK F) {σ' σ : RStore Expression} (hσ : StoreClosed σ)
    (hag : StoreAgreeOutside fresh σ' σ) {e : Expression.Expr} (he : ExprAvoids fresh e)
    (n : Nat) : evalBounded n F σ' e = evalBounded n F σ e := by
  obtain ⟨hwf, -⟩ := hF
  unfold evalBounded
  rw [evalTypedDomain_congr fun x hx => hag x (he x hx),
    evalOpsChecked_congr fun x hx => hag x (he x hx),
    Lambda.eval_env_congr (fun _ _ => Core.coreIdent_eq_of_name)
    n F σ' σ hwf hσ e fun x hx => hag x (he x hx)]

/-- Agreeing event arguments evaluate alike. -/
theorem EventArgAgree.eval {fresh : Expression.Ident → Prop}
    {a' a : REventArg Expression (InterpLang.RFactory Expression)}
    (h : EventArgAgree fresh a' a) (n : Nat) :
    evalBounded n a'.factory a'.store a'.expr = evalBounded n a.factory a.store a.expr := by
  grind [EventArgAgree, evalBounded_agree]

/-- Event agreement up to the names `fresh` (`EvAgree`: same kind, agreeing arguments)
    transfers target firing and hook decisions between two production runs for the same
    target, at downstream fuel `f ≤` upstream fuel `f'` (`EventTransfer`). -/
theorem evAgree_transfer (fresh : Expression.Ident → Prop) (t : AssertId Expression)
    {f f' : Nat} (hle : f ≤ f') : EventTransfer t t f f' (EvAgree fresh) := by
  have hc : ∀ ev' ev, EvAgree fresh ev' ev →
      assertFailureHalt t f' ev = assertFailureHalt t f' ev' ∧
        enforceInterrupt t f' ev = enforceInterrupt t f' ev' := fun ev' ev h => by
    cases ev' <;> cases ev <;> simp only [EvAgree] at h
    all_goals
      obtain ⟨-, hl, -, hmd, -⟩ := id h
      simp only [assertFailureHalt, Calls.assertFailureHalt, enforceInterrupt,
        Calls.enforceInterrupt, InterpLang.boundedEval, h.eval f', hl, hmd, true_and]
      all_goals rfl
  have he := eventTransfer_eq t hle
  exact ⟨fun ev' ev h hh => (hc _ _ h).1.trans (he.halt _ _ rfl hh),
    fun ev' ev h hh => (he.hook _ _ rfl hh).imp (hc _ _ h).2.trans (hc _ _ h).1.trans⟩

/-! ## The equality instance -/

/-- A replay simulation (`IsReplaySimulation`: the downstream command stepper is
    dominated by the upstream one) is a relational simulation (`RelStepSim`) that relates
    events and configurations by equality and never stutters, at every call-depth budget `d`. -/
theorem relStepSim_of_replaySimulation {π' π : String → Option Procedure}
    (hsim : IsReplaySimulation π' π) (t : AssertId Expression) {f f' : Nat} (hle : f ≤ f')
    (d : Nat) :
    RelStepSim (relProdCtx t t f f' Eq) (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d) Eq := by
  rintro c' c rfl hd k m _ hkm
  have hK := relProdCtx_eqCompat t hle
  exact .inr ⟨hd, stepInterp_dom hK (hsim _ hK d) c' k m hkm⟩

/-! ## Relational steps of runs agreeing outside a set of names -/

/-- Updating both stores at one name keeps them agreeing outside `fresh`. -/
theorem StoreAgreeOutside.update {fresh : Expression.Ident → Prop}
    {σ' σ : RStore Expression} (h : StoreAgreeOutside fresh σ' σ) (x : Expression.Ident)
    (v : Expression.Expr) :
    StoreAgreeOutside fresh (RStore.update σ' x v) (RStore.update σ x v) :=
  fun y hy => by simp [RStore.update, h y hy]

/-- Updating the first store at a name of `fresh` keeps the stores agreeing. -/
theorem StoreAgreeOutside.update_fresh {fresh : Expression.Ident → Prop}
    {σ' σ : RStore Expression} (h : StoreAgreeOutside fresh σ' σ) {x : Expression.Ident}
    (hx : fresh x) (v : Expression.Expr) :
    StoreAgreeOutside fresh (RStore.update σ' x v) σ := fun y hy => by
  simp [RStore.update, h y hy, show y ≠ x from fun e => hy (e ▸ hx)]

/-- Projections of stores agreeing outside `fresh` agree outside `fresh`. -/
theorem StoreAgreeOutside.project {fresh : Expression.Ident → Prop}
    {σp' σp σ' σ : RStore Expression} (hp : StoreAgreeOutside fresh σp' σp)
    (h : StoreAgreeOutside fresh σ' σ) :
    StoreAgreeOutside fresh (RStore.project σp' σ') (RStore.project σp σ) := fun y hy => by
  simp [RStore.project, hp y hy, h y hy]

/-- On stores agreeing outside `fresh` (upstream closed, factory well-formed), a command
    avoiding `fresh` emits event lists related pointwise by `EvAgree fresh`. -/
private theorem emittedEvents_agree {fresh : Expression.Ident → Prop}
    {F : Lambda.Factory CoreLParams}
    (hF : FactoryOK F) {σ' σ : IStore Expression} (hσ : StoreClosed σ.get)
    (hag : StoreAgreeOutside fresh σ'.get σ.get) (c : Cmd Expression) (hc : CmdAvoids fresh c) :
    List.Rel₂ (EvAgree fresh) (Cmd.rEmittedEvents (P := Expression) c F σ'.get)
      (Cmd.rEmittedEvents (P := Expression) c F σ.get) := by
  cases c <;> first | exact .nil | exact .cons ⟨rfl, rfl, rfl, rfl, hag, hc, hF, hσ⟩ .nil

set_option hygiene false in
/-- Closes a relational base-command step after its emit prefix (`hK`, `hkm`, `hO` from the
    context): the guard/RHS value transported along the fuel bound `x`, results related by `v`. -/
macro "cel_relLoop " x:term:max v:term:max : tactic =>
  `(tactic| (split <;> try simp_all [-bind_pure_comp]) <;> repeat' first
    | exact .throw hK _ _
    | exact RelDom.throw_bind_left hK _ _ (by grows_tac)
    | exact RelDom.throw_left hK _ (by grows_tac)
    | (simp only [InterpLang.boundedEval, evalBounded_mono hkm _ _ _ _ $x]
       exact .ite _ (fun _ => .pure $v) fun _ => .throw hK _ _)
    | exact .bind (.choose hK hO _ _ _ _)
        (fun _ _ h => by
          cases h.1
          first
            | exact .pure $v
            | exact .ite _ (fun _ => .pure $v) fun _ => .throw hK _ _)
        fun _ => by grows_tac
    | split)

set_option hygiene false in
/-- One evaluating command arm of a `RelStepSim` step (`hK`, `hkm` from the context): a pure
    step closed by `t`, or a guard/RHS value transported along the fuel bound `x`. -/
macro "cel_cmdArm " x:term:max t:tacticSeq : tactic => `(tactic| first
  | exact .pure (by $t)
  | (split <;> first
      | exact RelDom.throw_bind_left hK _ _ (by grows_tac)
      | exact RelDom.throw_left hK _ (by grows_tac)
      | (simp only [InterpLang.boundedEval, evalBounded_mono hkm _ _ _ _ $x]
         split <;> (try split) <;> (try simp [*]) <;> first
          | exact .pure (by $t)
          | exact RelDom.throw_bind_left hK _ _
              (Grows.bind (Grows.throw _ _) fun _ => Grows.pure _ _)
          | exact .throw hK _ _)))

/-- **A base command, relationally, without an oracle draw.**  Stepped on stores agreeing
    outside `fresh` (upstream closed, factory well-formed), at downstream fuel `k ≤`
    upstream fuel `m`, a command avoiding `fresh` gives stores agreeing outside `fresh`,
    provided it is not a nondeterministic `init`/`set` or the oracle is not free. -/
theorem cel_stepBaseCmdStore_rel {K : RelCtx} (hK : K.Compat) {fresh : Expression.Ident → Prop}
    (hER : AgreeCtx K fresh) {k m : Nat} (hkm : k ≤ m) {F : Lambda.Factory CoreLParams}
    (hF : FactoryOK F) {σ' σ : IStore Expression} (hσ : StoreClosed σ.get)
    (hag : StoreAgreeOutside fresh σ'.get σ.get) (c : Cmd Expression)
    (hO : (match c with | .init _ _ .nondet _ | .set _ .nondet _ => true | _ => false) = false ∨
      K.freeOracle = false)
    (hc : CmdAvoids fresh c) :
    RelDom K (stepBaseCmdStore (m := ReplayM Expression) k F σ' c)
      (stepBaseCmdStore (m := ReplayM Expression) m F σ c)
      (fun a b => StoreAgreeOutside fresh a.get b.get) := by
  cases c <;> (try cases ‹ExprOrNondet _›) <;> simp only [stepBaseCmdStore, CmdAvoids] at hc hO ⊢
  all_goals first
    | exact .bind (.forM_emit hK (.imp hER (emittedEvents_agree hF hσ hag _ hc)))
        (fun _ _ _ => .pure hag) fun _ => by grows_tac
    | rw [hag _ (by first | exact hc | exact hc.1)]
  all_goals with_reducible cel_relLoop
    (by with_unfolding_all exact (evalBounded_agree hF hσ hag hc.2 k).symm.trans ‹_›)
    (by simp only [IStore.get_update]; exact hag.update _ _)

/-- **A base command, relationally.**  Stepped on stores agreeing outside `fresh`
    (upstream closed, factory well-formed), at downstream fuel `k ≤` upstream fuel `m`,
    a command avoiding `fresh` gives stores agreeing outside `fresh`. -/
theorem stepBaseCmdStore_rel {K : RelCtx} (hK : K.Compat) (hO : K.freeOracle = false)
    {fresh : Expression.Ident → Prop}
    (hER : AgreeCtx K fresh) {k m : Nat} (hkm : k ≤ m) {F : Lambda.Factory CoreLParams}
    (hF : FactoryOK F) {σ' σ : IStore Expression} (hσ : StoreClosed σ.get)
    (hag : StoreAgreeOutside fresh σ'.get σ.get) (c : Cmd Expression) (hc : CmdAvoids fresh c) :
    RelDom K (stepBaseCmdStore (m := ReplayM Expression) k F σ' c)
      (stepBaseCmdStore (m := ReplayM Expression) m F σ c)
      (fun a b => StoreAgreeOutside fresh a.get b.get) :=
  cel_stepBaseCmdStore_rel hK hER hkm hF hσ hag c (.inr hO) hc

end -- public section

end Core
