/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.Counterexample.Run
public import Strata.Languages.Core.Counterexample.BackLink
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Languages.Core.Counterexample.RunProps
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink
public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.Languages.Core.InterpreterInterruptBridge
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterCFG
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplayProps
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Imperative.Counterexample.Tactics
public import Strata.Util.ListUtilsProps
public import Strata.Languages.Core.Counterexample.BackLinkSim
import all Strata.Languages.Core.Counterexample.BackLinkSim

/-! # Replay-vs-replay domination, proved once

A *downstream* replay run is related to an *upstream* one through a *relational context*
`RelCtx`: the two run configurations, the target predicate of each side, and an event relation
`ER`.  Related states (`StRel`) have the same oracle cursor and traces related by `ER`.
`RelDom K X' X Ra` (*domination*): from related states, a success of `X'` is matched by a
success of `X` with results related by `Ra` and related states, or `X` has recorded an event
firing the upstream target (*escape*); a failure of `X'` whose state has fired the downstream
target leaves `X` fired upstream.  The `RelDom` combinators (`pure`, `throw`, `bind`, `emit`,
`choose`, branching) are proved once here.

A phase that only changes the procedure table relates two runs by the *equality instance*:
equal events (`RelCtx.EqCompat`), results related by equality, no stuttering.  It supplies
the per-command obligation `StepDom`, lifted to the whole run (`runInterp_dom`), so that a
downstream claim genuine and feasible at fuel `f` is so upstream at any fuel `f' ≥ f`
(`claim_back_of_simulation`).  Phases that rewrite statements use the stuttering relational
simulations of `BackLinkRelSim`, of which this instance is a special case.

Key theorems: `RelDom.bind`, `RelDom.fired`, `runInterp_dom`, `claim_back_of_simulation`,
`isReplaySimulation_of_sub`, `genuineFeasible_fuel_mono`.  Key definitions: `RelCtx`, `StRel`,
`RelDom`, `RelCtx.EqCompat`, `StepDom`, `IsReplaySimulation`. -/

namespace Core

open Imperative

public section

/-! ## Runs and growth -/

/-! ## `Grows` combinators -/

/-- Running a bind runs the continuation on success. -/
theorem rrun_bind {α β : Type} (x : ReplayM Expression α) (g : α → ReplayM Expression β)
    (cfg : ReplayCfg Expression) (s : ReplayState Expression) :
    rrun (x >>= g) cfg s
      = (match rrun x cfg s with
         | (.ok a, s') => rrun (g a) cfg s'
         | (.error e, s') => (.error e, s')) := by
  simp only [rrun, replayM_run_bind]
  rcases ((x.run cfg).run).run s with ⟨_ | _, _⟩ <;> rfl

/-- Running `pure a` succeeds with `a`, state unchanged. -/
theorem rrun_pure {α : Type} (a : α) (cfg : ReplayCfg Expression) (s : ReplayState Expression) :
    rrun (pure a : ReplayM Expression α) cfg s = (.ok a, s) := rfl

/-- Running `throw e` fails with `e`, state unchanged. -/
theorem rrun_throw {α : Type} (e : StopReason) (cfg : ReplayCfg Expression)
    (s : ReplayState Expression) :
    rrun (throw e : ReplayM Expression α) cfg s = (.error e, s) := rfl

/-- `pure` grows the trace. -/
theorem Grows.pure {α : Type} (cfg : ReplayCfg Expression) (a : α) :
    Grows cfg (Pure.pure a : ReplayM Expression α) := fun _ => List.suffix_refl _

/-- `throw` grows the trace. -/
theorem Grows.throw {α : Type} (cfg : ReplayCfg Expression) (e : StopReason) :
    Grows cfg (MonadExcept.throw e : ReplayM Expression α) := fun _ => List.suffix_refl _

/-- A bind of growing computations grows the trace. -/
theorem Grows.bind {α β : Type} {cfg : ReplayCfg Expression} {x : ReplayM Expression α}
    {g : α → ReplayM Expression β} (hx : Grows cfg x) (hg : ∀ a, Grows cfg (g a)) :
    Grows cfg (x >>= g) := fun s => by
  rw [rrun_bind]
  split <;> rename_i h
  · exact (h ▸ hx s :).trans (hg _ _)
  · exact (h ▸ hx s :)

/-- The upstream final trace of a bind extends the trace after its first part. -/
theorem rrun_bind_ext {α β : Type} {cfg : ReplayCfg Expression} (x : ReplayM Expression α)
    {g : α → ReplayM Expression β} (hg : ∀ a, Grows cfg (g a)) (s : ReplayState Expression) :
    (rrun x cfg s).2.traceRev <:+ (rrun (x >>= g) cfg s).2.traceRev := by
  grind [rrun_bind, Grows]

/-- Emitting an event grows the trace. -/
theorem Grows.emit (cfg : ReplayCfg Expression) (ev : IEvent Expression) :
    Grows cfg (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev) := fun s => by
  simp [replayM_run_emit_state]

/-- Emitting a list grows the trace. -/
theorem Grows.forM_emit (cfg : ReplayCfg Expression) :
    ∀ evs : List (IEvent Expression),
      Grows cfg (evs.forM (InterpEffects.emit (P := Expression) (m := ReplayM Expression)))
  | [] => .pure cfg _
  | ev :: rest => .bind (.emit cfg ev) fun _ => .forM_emit cfg rest

/-- `branch` grows the trace: `ReplayM` keeps its default, which throws. -/
theorem Grows.branch (cfg : ReplayCfg Expression) (factory : Lambda.Factory CoreLParams)
    (store : RStore Expression) (v : Expression.Expr) :
    Grows cfg (InterpEffects.branch (m := ReplayM Expression) factory store v) :=
  .throw cfg .expressionWasNotBoolean

/-- `choose` never touches the trace. -/
theorem choose_traceRev (cfg : ReplayCfg Expression) (factory : Lambda.Factory CoreLParams)
    (store : RStore Expression) (ty : Expression.Ty) (s : ReplayState Expression) :
    (rrun (InterpEffects.choose (m := ReplayM Expression) factory store ty) cfg s).2.traceRev
      = s.traceRev := by
  cel_rr
  (repeat' split) <;> cel_rr

/-- `choose` grows the trace. -/
theorem Grows.choose (cfg : ReplayCfg Expression) (factory : Lambda.Factory CoreLParams)
    (store : RStore Expression) (ty : Expression.Ty) :
    Grows cfg (InterpEffects.choose (m := ReplayM Expression) factory store ty) :=
  fun s => (choose_traceRev cfg factory store ty s).symm ▸ List.suffix_refl _

/-- Close a `Grows` goal on a computation built from `pure`/`throw`/`choose`/`emit`/`branch`,
    binds, and pure branching. -/
macro "grows_tac" : tactic => `(tactic| repeat' (first
  | with_reducible exact Grows.pure _ _ | with_reducible exact Grows.throw _ _
  | with_reducible exact Grows.choose _ _ _ _
  | with_reducible exact Grows.forM_emit _ _ | with_reducible exact Grows.emit _ _
  | with_reducible exact Grows.branch _ _ _ _
  | (with_reducible refine Grows.bind ?_ (fun _ => ?_)) | split))

/-! ## Contexts and state relation -/

/-- `TraceRel K` is reflexive when `K.ER` is. -/
theorem TraceRel.refl_eq {K : RelCtx} (hK : ∀ ev, K.ER ev ev) :
    ∀ l : List (IEvent Expression), TraceRel K l l := fun l => by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (hK a) ih

/-- `FiredU` is preserved by trace growth. -/
theorem FiredU.mono {K : RelCtx} {s s2 : ReplayState Expression} (h : FiredU K s)
    (hs : s.traceRev <:+ s2.traceRev) : FiredU K s2 := h.imp fun _ ⟨hm, he⟩ => ⟨hs.subset hm, he⟩

/-- Related states transfer firing upstream. -/
theorem StRel.fired {K : RelCtx} (hK : K.Compat) {s' s : ReplayState Expression}
    (h : StRel K s' s) (hf : FiredD K s') : FiredU K s := by
  obtain ⟨-, -, h⟩ := h
  unfold FiredU FiredD at *
  generalize s'.traceRev = l', s.traceRev = l at *
  induction h <;> simp_all only [List.not_mem_nil, false_and, forall_exists_index, List.mem_cons,
    exists_eq_or_imp] <;> grind [hK.halt, hK.extra]

/-! ## Relational domination of one computation -/

namespace RelDom

variable {K : RelCtx}

/-- Related pure values are dominated. -/
theorem pure {α' α : Type} {Ra : α' → α → Prop} {a' : α'} {a : α} (h : Ra a' a) :
    RelDom K (Pure.pure a') (Pure.pure a) Ra :=
  ⟨.pure _ _, fun _ _ hst => ⟨fun _ _ he => (by cases he; exact .inl ⟨_, _, rfl, h, hst⟩),
    fun _ _ he => by cases he⟩⟩

/-- A downstream failure that changes nothing is dominated by any growing upstream
    computation. -/
theorem throw_left (hK : K.Compat) {α' α : Type} {Ra : α' → α → Prop} (e : StopReason)
    {X : ReplayM Expression α} (hX : Grows K.cfgU X) :
    RelDom K (MonadExcept.throw e : ReplayM Expression α') X Ra :=
  ⟨hX, fun _ s hst => ⟨fun _ _ he => (by cases he),
    fun _ _ he hf => (by cases he; exact (hst.fired hK hf).mono (hX s))⟩⟩

/-- Two failures are dominated. -/
theorem throw (hK : K.Compat) {α' α : Type} {Ra : α' → α → Prop} (e e' : StopReason) :
    RelDom K (MonadExcept.throw e : ReplayM Expression α')
      (MonadExcept.throw e' : ReplayM Expression α) Ra := throw_left hK _ (.throw _ _)

/-- A downstream throw-then-bind is dominated by any growing upstream computation. -/
theorem throw_bind_left (hK : K.Compat) {α β' α' : Type}
    {Ra : α' → α → Prop} (e : StopReason) (g : β' → ReplayM Expression α')
    {X : ReplayM Expression α} (hX : Grows K.cfgU X) :
    RelDom K ((MonadExcept.throw e : ReplayM Expression β') >>= g) X Ra :=
  ⟨hX, fun _ _ hs => ⟨nofun, fun _ _ h hf => by cases h; exact (hs.fired hK hf).mono (hX _)⟩⟩

/-- `throw e >>= _` is dominated by `throw e >>= _` for any continuations. -/
private theorem throw_bind (hK : K.Compat) {α β' β : Type} {Rb : β' → β → Prop}
    (e : StopReason) (f' : α → ReplayM Expression β') (f : α → ReplayM Expression β) :
    RelDom K ((MonadExcept.throw e : ReplayM Expression α) >>= f')
      ((MonadExcept.throw e : ReplayM Expression α) >>= f) Rb :=
  throw_bind_left hK e f' fun _ => List.suffix_refl _

/-- Bind preserves domination. -/
theorem bind {α' α β' β : Type} {Ra : α' → α → Prop} {Rb : β' → β → Prop}
    {X' : ReplayM Expression α'} {X : ReplayM Expression α}
    {f' : α' → ReplayM Expression β'} {f : α → ReplayM Expression β}
    (hx : RelDom K X' X Ra) (hf : ∀ a' a, Ra a' a → RelDom K (f' a') (f a) Rb)
    (hg : ∀ a, Grows K.cfgU (f a)) :
    RelDom K (X' >>= f') (X >>= f) Rb := by
  refine ⟨.bind hx.1 hg, fun s' s hst => ?_⟩
  have hext := rrun_bind_ext X hg s
  have ⟨hok, herr⟩ := hx.2 s' s hst
  rw [rrun_bind]
  split <;> rename_i hX'
  · rcases hok _ _ hX' with ⟨_, _, hX, hR, hst1⟩ | hF
    · rw [rrun_bind, hX]
      exact (hf _ _ hR).2 _ _ hst1
    · exact ⟨fun _ _ _ => .inr (hF.mono hext), fun _ _ _ _ => hF.mono hext⟩
  · exact ⟨nofun, fun _ _ h hF => by cases h; exact (herr _ _ hX' hF).mono hext⟩

/-- Domination is monotone in the result relation. -/
theorem mono {α' α : Type} {Ra Rb : α' → α → Prop} {X' : ReplayM Expression α'}
    {X : ReplayM Expression α} (h : RelDom K X' X Ra) (hab : ∀ a' a, Ra a' a → Rb a' a) :
    RelDom K X' X Rb := by grind [RelDom, h.1, h.2]

/-- The two runs emit related events. -/
theorem emit (hK : K.Compat) {ev' ev : IEvent Expression} (hev : K.ER ev' ev) :
    RelDom K (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev')
      (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev)
      (fun _ _ => True) := by
  refine ⟨Grows.emit _ ev, fun s' s hst => ?_⟩
  have hst' : StRel K ⟨s'.remaining, s'.usedRev, ev' :: s'.traceRev⟩
      ⟨s.remaining, s.usedRev, ev :: s.traceRev⟩ := ⟨hst.1, hst.2.1, .cons hev hst.2.2⟩
  cel_rr
  cases hd : K.cfgD.interruptOn ev' <;> cases hu : K.cfgU.interruptOn ev <;> cel_rr
  · exact ⟨fun _ _ h => by cases h; exact .inl ⟨_, _, rfl, trivial, hst'⟩, nofun⟩
  · have hU := (hK.hook _ _ hev hd).resolve_left (by simp [hu])
    exact ⟨fun _ _ _ => .inr ⟨ev, List.mem_cons_self .., hU⟩, nofun⟩
  all_goals exact ⟨nofun, fun _ _ h hf => by cases h; exact hst'.fired hK hf⟩

/-- Emitting related lists is dominated. -/
theorem forM_emit (hK : K.Compat) :
    ∀ {evs' evs : List (IEvent Expression)}, List.Rel₂ K.ER evs' evs →
      RelDom K (evs'.forM (InterpEffects.emit (P := Expression) (m := ReplayM Expression)))
        (evs.forM (InterpEffects.emit (P := Expression) (m := ReplayM Expression)))
        (fun _ _ => True) := fun h => by
  induction h with
  | nil => exact .pure trivial
  | cons hab _ ih => exact .bind (.emit hK hab) (fun _ _ _ => ih) fun _ => .forM_emit _ _

/-- Both runs draw from the oracle with the same factory and type: the same value, which
    the draw validated. -/
theorem choose (hK : K.Compat) (hO : K.freeOracle = false) (factory : Lambda.Factory CoreLParams)
    (store' store : RStore Expression) (ty : Expression.Ty) :
    RelDom K (InterpEffects.choose (m := ReplayM Expression) factory store' ty)
      (InterpEffects.choose (m := ReplayM Expression) factory store ty)
      (fun a' a => a' = a ∧ ((InterpLang.ops (P := Expression)).isValue factory a
        && (InterpLang.ops (P := Expression)).hasType factory a ty) = true) := by
  refine ⟨.choose _ _ _ _, fun s' s ⟨hrem, hused, htr⟩ =>
    ⟨fun a _ h => ?_, fun _ _ h hf => ?_⟩⟩
  · simp only [hO, Bool.false_eq_true, false_or] at hrem hused
    change replayRun _ _ _ = _ at h
    rcases hs : s.remaining with _ | ⟨_, _⟩ <;> eff_inv [hK.strictD, hrem, hs, seqRight_eq_bind]
    exact .inl ⟨a, _, replayM_choose_cons _ _ _ _ _ _ _ hs ‹_›, ⟨rfl, ‹_›⟩, .inr rfl,
      .inr (by simp [hused]), htr⟩
  · have hx := choose_traceRev K.cfgD factory store' ty s'
    rw [h] at hx
    obtain ⟨e, he, hh⟩ := hf
    exact (StRel.fired hK ⟨hrem, hused, htr⟩ ⟨e, hx ▸ he, hh⟩).mono (Grows.choose _ _ _ _ s)

/-- Identical pure branching on both sides. -/
theorem ite {α' α : Type} {Ra : α' → α → Prop} (c : Prop) [Decidable c]
    {X' Y' : ReplayM Expression α'} {X Y : ReplayM Expression α}
    (h1 : c → RelDom K X' X Ra) (h2 : ¬ c → RelDom K Y' Y Ra) :
    RelDom K (if c then X' else Y') (if c then X else Y) Ra := by grind

/-- `branch` is dominated by itself: `ReplayM` keeps its default, which throws. -/
theorem branch (hK : K.Compat) {Rb : Bool → Bool → Prop} (factory : Lambda.Factory CoreLParams)
    (store : RStore Expression) (v : Expression.Expr) :
    RelDom K (InterpEffects.branch (m := ReplayM Expression) factory store v)
      (InterpEffects.branch (m := ReplayM Expression) factory store v) Rb :=
  throw hK .expressionWasNotBoolean .expressionWasNotBoolean

/-- From related states, a downstream run whose final state has fired the downstream target
    is matched by an upstream run whose final state has fired the upstream target. -/
theorem fired (hK : K.Compat) {α' α : Type} {Ra : α' → α → Prop} {X' : ReplayM Expression α'}
    {X : ReplayM Expression α} (h : RelDom K X' X Ra) {s' s : ReplayState Expression}
    (hst : StRel K s' s) (hf : FiredD K (rrun X' K.cfgD s').2) :
    FiredU K (rrun X K.cfgU s).2 := by
  have ⟨hok, herr⟩ := h.2 s' s hst
  rcases hr : rrun X' K.cfgD s' with ⟨_ | _, _⟩ <;> rw [hr] at hf
  · exact herr _ _ hr hf
  exact (hok _ _ hr).elim (fun ⟨_, _, hu, _, hst1⟩ => hu ▸ hst1.fired hK hf) id

end RelDom

/-! ## The equality instance -/

namespace RelDom

variable {K : RelCtx}

/-- Bind preserves domination when the first results are related by equality. -/
theorem bind_eq {α β' β : Type} {Rb : β' → β → Prop} {X' X : ReplayM Expression α}
    {f' : α → ReplayM Expression β'} {f : α → ReplayM Expression β}
    (hx : RelDom K X' X Eq) (hf : ∀ a, RelDom K (f' a) (f a) Rb) :
    RelDom K (X' >>= f') (X >>= f) Rb :=
  .bind hx (fun _ _ h => h ▸ hf _) fun a => (hf a).1

/-- `emit` is dominated by itself. -/
theorem emit_eq (hK : K.EqCompat) (ev : IEvent Expression) :
    RelDom K (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev)
      (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev) Eq :=
  (emit hK.compat (hK.refl ev)).mono fun _ _ _ => rfl

/-- Emitting a list is dominated by itself. -/
theorem forM_emit_eq (hK : K.EqCompat) (evs : List (IEvent Expression)) :
    RelDom K (evs.forM (InterpEffects.emit (P := Expression) (m := ReplayM Expression)))
      (evs.forM (InterpEffects.emit (P := Expression) (m := ReplayM Expression))) Eq :=
  (forM_emit hK.compat (.imp (fun _ _ h => h ▸ hK.refl _) (.refl (fun _ => rfl) evs))).mono
    fun _ _ _ => rfl

/-- `choose` is dominated by itself. -/
theorem choose_eq (hK : K.EqCompat) (factory : Lambda.Factory CoreLParams)
    (store : RStore Expression) (ty : Expression.Ty) :
    RelDom K (InterpEffects.choose (m := ReplayM Expression) factory store ty)
      (InterpEffects.choose (m := ReplayM Expression) factory store ty) Eq :=
  (choose hK.compat hK.oracle factory store store ty).mono fun _ _ h => h.1

end RelDom

/-- One step of an equality-instance `RelDom` proof between two computations of the same
    shape: a closing law (`throw_left`/`throw_bind_left` with the `Grows` side by
    `grows_tac`), a bind/ite decomposition, or a `split`. -/
macro "cel_dstep" hK:term : tactic => `(tactic| first
  | with_reducible exact RelDom.pure rfl | with_reducible exact RelDom.throw ($hK).compat _ _
  | with_reducible exact RelDom.throw_bind ($hK).compat _ _ _
  | with_reducible exact RelDom.choose_eq $hK _ _ _
  | with_reducible exact RelDom.forM_emit_eq $hK _ | with_reducible exact RelDom.emit_eq $hK _
  | with_reducible exact RelDom.branch ($hK).compat _ _ _
  | with_reducible exact RelDom.throw_left ($hK).compat _ (by grows_tac)
  | with_reducible exact RelDom.throw_bind_left ($hK).compat _ _ (by grows_tac)
  | (with_reducible refine RelDom.bind_eq ?_ (fun _ => ?_))
  | (with_reducible refine RelDom.ite _ (fun _ => ?_) (fun _ => ?_)) | split)

/-! ## Base commands and single steps -/

/-- One step of a fuel-monotone equality-instance `RelDom` proof: a bind decomposition, equal
    `pure`s, an upstream evaluation rewritten by its downstream success at the smaller fuel
    (`hle`), a `split`, or a `cel_dstep` step. -/
local macro "dom_step" hK:term "," hle:term : tactic => `(tactic| first
  | (with_reducible refine RelDom.bind_eq ?_ (fun _ => ?_)) | with_reducible exact RelDom.pure rfl
  | simp only [evalBounded_mono $hle _ _ _ _ ‹_›] | split | cel_dstep $hK)

/-- Every `stepBaseCmdStore` run grows the trace. -/
theorem stepBaseCmdStore_grows (cfg : ReplayCfg Expression) (k : Nat)
    (factory : Lambda.Factory CoreLParams) (store : IStore Expression) (c : Cmd Expression) :
    Grows cfg (stepBaseCmdStore (m := ReplayM Expression) k factory store c) := by
  cases c <;> simp only [stepBaseCmdStore] <;> grows_tac

/-- A base command at downstream fuel `k` is dominated by the same command at any
    upstream fuel `k' ≥ k`. -/
private theorem stepBaseCmdStore_dom {K : RelCtx} (hK : K.EqCompat) {k k' : Nat} (hle : k ≤ k')
    (factory : Lambda.Factory CoreLParams) (store : IStore Expression) (c : Cmd Expression) :
    RelDom K (stepBaseCmdStore (m := ReplayM Expression) k factory store c)
      (stepBaseCmdStore (m := ReplayM Expression) k' factory store c) Eq := by
  cases c <;> simp only [stepBaseCmdStore, InterpLang.boundedEval] <;> repeat' dom_step hK, hle

/-- Havocking a list of names (`Calls.havocVarList`) grows the trace. -/
theorem havocVarList_grows (cfg : ReplayCfg Expression) (k : Nat)
    (factory : Lambda.Factory CoreLParams) :
    ∀ (names : List Expression.Ident) (store : IStore Expression),
      Grows cfg (Calls.havocVarList (m := ReplayM Expression) k factory names store)
  | [], _ => .pure _ _
  | _ :: names, _ =>
    .bind (stepBaseCmdStore_grows _ _ _ _ _) fun _ => havocVarList_grows cfg k factory names _

/-- The contract run of a callee (`Calls.runAbstractCallee`) grows the trace. -/
theorem runAbstractCallee_grows (cfg : ReplayCfg Expression) (k : Nat)
    (factory : Lambda.Factory CoreLParams) (outs : List Expression.Ident)
    (post : ListMap String (Imperative.Check Expression)) (σ : RStore Expression) :
    Grows cfg (Calls.runAbstractCallee (m := ReplayM Expression) k factory outs post σ) :=
  .bind (havocVarList_grows _ _ _ _ _) fun _ => by grows_tac

/-- Havocking a list of names at downstream fuel `k` is dominated by the same havoc at any
    upstream fuel `k' ≥ k`. -/
private theorem havocVarList_dom {K : RelCtx} (hK : K.EqCompat) {k k' : Nat} (hle : k ≤ k')
    (factory : Lambda.Factory CoreLParams) :
    ∀ (names : List Expression.Ident) (store : IStore Expression),
      RelDom K (Calls.havocVarList (m := ReplayM Expression) k factory names store)
        (Calls.havocVarList (m := ReplayM Expression) k' factory names store) Eq
  | [], _ => .pure rfl
  | _ :: names, _ => .bind_eq (stepBaseCmdStore_dom hK hle _ _ _) fun _ =>
    havocVarList_dom hK hle factory names _

/-- The contract run of a callee at downstream fuel `k` is dominated by the same run at any
    upstream fuel `k' ≥ k`. -/
private theorem runAbstractCallee_dom {K : RelCtx} (hK : K.EqCompat) {k k' : Nat} (hle : k ≤ k')
    (factory : Lambda.Factory CoreLParams) (outs : List Expression.Ident)
    (post : ListMap String (Imperative.Check Expression)) (σ : RStore Expression) :
    RelDom K (Calls.runAbstractCallee (m := ReplayM Expression) k factory outs post σ)
      (Calls.runAbstractCallee (m := ReplayM Expression) k' factory outs post σ) Eq :=
  .bind_eq (havocVarList_dom hK hle _ _ _) fun _ => by repeat' cel_dstep hK

/-! ## The whole run, from a per-command obligation -/

/-- The upstream stepper of a `StepDom` grows the trace. -/
theorem StepDom.grows {K : RelCtx} {sc' sc : StepCmdM Expression Command (ReplayM Expression)}
    (h : StepDom K sc' sc) : StepGrows K.cfgU sc := fun _ _ _ => (h 0 _ _ _ (Nat.zero_le _)).1

/-- `stepInterp` over a growing stepper grows the trace. -/
theorem stepInterp_grows {cfg : ReplayCfg Expression}
    {sc : StepCmdM Expression Command (ReplayM Expression)} (h : StepGrows cfg sc) :
    ∀ (c : IConfig Expression Command) (k : Nat), Grows cfg (stepInterp sc k c) := by
  intro c
  induction c <;> intro k <;> simp only [stepInterp, resolveGuard.eq_def] <;> repeat' (first
    | with_reducible exact Grows.pure _ _ | with_reducible exact h _ _ _ | split
    | (with_reducible refine .bind ?_ fun _ => ?_) | (with_reducible apply_assumption; done))
  grows_tac

/-- A run over a growing stepper grows the trace. -/
theorem runInterp_grows {cfg : ReplayCfg Expression}
    {sc : StepCmdM Expression Command (ReplayM Expression)} (h : StepGrows cfg sc) :
    ∀ (n : Nat) (c : IConfig Expression Command), Grows cfg (runInterp sc n c) := by
  intro n
  induction n <;> intro c <;> cases c <;> simp only [runInterp] <;> first
    | with_reducible exact .pure _ _ | with_reducible exact .throw _ _
    | with_reducible exact .bind (stepInterp_grows h _ _) ‹_›

/-- **Single-step domination**: a per-command obligation lifts to one `stepInterp`
    step at every configuration, downstream fuel `k ≤ k'` upstream fuel. -/
theorem stepInterp_dom {K : RelCtx} (hK : K.EqCompat)
    {sc' sc : StepCmdM Expression Command (ReplayM Expression)} (h : StepDom K sc' sc) :
    ∀ (c : IConfig Expression Command) (k k' : Nat), k ≤ k' →
      RelDom K (stepInterp sc' k c) (stepInterp sc k' c) Eq := by
  intro c
  induction c <;> intro k k' hle <;>
    simp only [stepInterp, resolveGuard.eq_def, InterpLang.boundedEval]
  all_goals repeat' (first
    | with_reducible exact h _ _ _ _ hle | dom_step hK, hle | (apply_assumption <;> assumption))

/-- **Whole-run domination**: a per-command obligation lifts to the whole interpreter run,
    downstream fuel `n ≤ n'` upstream fuel. -/
theorem runInterp_dom {K : RelCtx} (hK : K.EqCompat)
    {sc' sc : StepCmdM Expression Command (ReplayM Expression)} (h : StepDom K sc' sc) :
    ∀ (n n' : Nat), n ≤ n' → ∀ (c : IConfig Expression Command),
      RelDom K (runInterp sc' n c) (runInterp sc n' c) Eq := by
  have hg := h.grows
  have hU := fun k n c => Grows.bind (stepInterp_grows hg c k) (runInterp_grows hg n)
  intro n
  induction n <;> intro n' hle c <;> cases n' <;> cases c <;> simp only [runInterp] <;> first
    | omega | with_reducible exact .pure rfl | with_reducible exact .throw hK.compat _ _
    | with_reducible exact .throw_left hK.compat _ (hU _ _ _)
    | exact .bind_eq (stepInterp_dom hK h _ _ _ (by omega)) fun _ => by apply_assumption; omega

/-! ## CFG callee bodies -/

/-- A CFG step over a store stepper whose every run grows the trace grows the trace. -/
theorem stepInterpCFG_grows {cfg : ReplayCfg Expression}
    {sc : StepCmdStoreM Expression Command (ReplayM Expression)}
    (h : ∀ k f σ c, Grows cfg (sc k f σ c)) :
    ∀ (k : Nat) (c : ICFGConfig String Command Expression),
      Grows cfg (stepInterpCFG sc k c) := by
  intro k c
  cases c <;> simp only [stepInterpCFG] <;> repeat' (first
    | with_reducible exact Grows.pure _ _ | (with_reducible refine Grows.bind ?_ (fun _ => ?_))
    | with_reducible exact h _ _ _ _ | with_reducible exact Grows.throw _ _
    | with_reducible exact Grows.branch _ _ _ _ | split)

/-- A CFG run over a store stepper whose every run grows the trace grows the trace. -/
theorem runInterpCFG_grows {cfg : ReplayCfg Expression}
    {sc : StepCmdStoreM Expression Command (ReplayM Expression)}
    (h : ∀ k f σ c, Grows cfg (sc k f σ c)) :
    ∀ (n : Nat) (c : ICFGConfig String Command Expression),
      Grows cfg (runInterpCFG sc n c) := by
  intro n
  induction n <;> intro c <;> cases c <;> unfold runInterpCFG <;> first
    | with_reducible exact .pure _ _ | with_reducible exact .throw _ _
    | with_reducible exact .bind (stepInterpCFG_grows h _ _) ‹_›

/-- **Single CFG step domination**: if the downstream store stepper at fuel `k` is dominated by
    the upstream one at every fuel `k' ≥ k`, one CFG step at downstream fuel `k` is dominated by
    one at upstream fuel `k' ≥ k`. -/
theorem stepInterpCFG_dom {K : RelCtx} (hK : K.EqCompat)
    {sc' sc : StepCmdStoreM Expression Command (ReplayM Expression)}
    (h : ∀ k k' f σ c, k ≤ k' → RelDom K (sc' k f σ c) (sc k' f σ c) Eq) :
    ∀ (c : ICFGConfig String Command Expression) (k k' : Nat), k ≤ k' →
      RelDom K (stepInterpCFG sc' k c) (stepInterpCFG sc k' c) Eq := by
  intro c k k' hle
  cases c <;> simp only [stepInterpCFG, InterpLang.boundedEval]
  all_goals repeat' (first | with_reducible exact h _ _ _ _ _ hle | dom_step hK, hle)

/-- **CFG run domination**: if the downstream store stepper at fuel `k` is dominated by the
    upstream one at every fuel `k' ≥ k`, a CFG run at downstream fuel `n` is dominated by one at
    upstream fuel `n' ≥ n`. -/
theorem runInterpCFG_dom {K : RelCtx} (hK : K.EqCompat)
    {sc' sc : StepCmdStoreM Expression Command (ReplayM Expression)}
    (h : ∀ k k' f σ c, k ≤ k' → RelDom K (sc' k f σ c) (sc k' f σ c) Eq) :
    ∀ (n n' : Nat), n ≤ n' → ∀ (c : ICFGConfig String Command Expression),
      RelDom K (runInterpCFG sc' n c) (runInterpCFG sc n' c) Eq := by
  have hg : ∀ k f σ c, Grows K.cfgU (sc k f σ c) := fun _ _ _ _ => (h 0 _ _ _ _ (Nat.zero_le _)).1
  have hU := fun k n c => Grows.bind (stepInterpCFG_grows hg k c) (runInterpCFG_grows hg n)
  intro n
  induction n <;> intro n' hle c <;> cases n' <;> cases c <;> unfold runInterpCFG <;> first
    | omega | with_reducible exact .pure rfl | with_reducible exact .throw hK.compat _ _
    | with_reducible exact .throw_left hK.compat _ (hU _ _ _)
    | exact .bind_eq (stepInterpCFG_dom hK h _ _ _ (by omega)) fun _ => by
        apply_assumption; omega

/-- A callee body run (`Calls.runCallee`) over a growing command stepper grows the trace. -/
theorem runCallee_grows {cfg : ReplayCfg Expression}
    {sc : StepCmdM Expression Command (ReplayM Expression)} (h : StepGrows cfg sc)
    (procName : String) (body : Body Expression Command) (fac : Lambda.Factory CoreLParams)
    (n : Nat) (σ : RStore Expression) : Grows cfg (Calls.runCallee sc procName body fac n σ) := by
  cases body <;> simp only [Calls.runCallee]
  · exact .bind (runInterp_grows h _ _) fun _ => by grows_tac
  · exact .bind (runInterpCFG_grows (fun _ _ _ _ => .bind (h _ _ _) fun _ => .pure _ _) _ _)
      fun _ => by grows_tac
  · exact .throw _ _

/-- **Callee body run domination**: under the per-command obligation `StepDom`, a callee body
    run (`Calls.runCallee`) at downstream fuel `n` is dominated by the same body's run at upstream
    fuel `n' ≥ n`. -/
theorem runCallee_dom {K : RelCtx} (hK : K.EqCompat)
    {sc' sc : StepCmdM Expression Command (ReplayM Expression)} (h : StepDom K sc' sc)
    (procName : String) (body : Body Expression Command) (fac : Lambda.Factory CoreLParams)
    {n n' : Nat} (hle : n ≤ n') (σ : RStore Expression) :
    RelDom K (Calls.runCallee sc' procName body fac n σ)
      (Calls.runCallee sc procName body fac n' σ) Eq := by
  cases body <;> simp only [Calls.runCallee]
  · exact .bind_eq (runInterp_dom hK h _ _ hle _) fun _ => by repeat' cel_dstep hK
  · exact .bind_eq (runInterpCFG_dom hK (fun k k' f σ c hk =>
      .bind_eq (h k k' ⟨σ, f⟩ c hk) fun r => .pure (a := r.getEnv.store) rfl) _ _ hle _) fun _ => by
        repeat' cel_dstep hK
  · exact .throw hK.compat _ _

/-! ## The Core command stepper -/

/-- Unfolds a step of Core's command stepper (`replayStepCmd`, `Calls.stepCmd`) on a known
    command, at the goal, to its match on the command's arguments, whether `Calls.stepCmd` is the
    stepper itself or the instance of a generic one (`Calls.stepCmdWith` at `Calls.CmdExt.view`). -/
local macro "cel_unfold_step" : tactic =>
  `(tactic| (unfold replayStepCmd Calls.stepCmd
             (try unfold Calls.stepCmdWith)
             (try dsimp only [Calls.CmdExt.view, Calls.dispatchCall, Calls.callBody])
             (try dsimp only)))

/-- `cel_unfold_step` at the hypothesis `h` and at the goal. -/
local macro "cel_unfold_step" h:ident : tactic =>
  `(tactic| (unfold replayStepCmd Calls.stepCmd at $h:ident ⊢
             (try unfold Calls.stepCmdWith at $h:ident ⊢)
             (try dsimp only [Calls.CmdExt.view, Calls.dispatchCall, Calls.callBody] at $h:ident ⊢)
             (try dsimp only at $h:ident ⊢)))

/-- Every run of Core's command stepper grows the trace (any procedure table, any
    call-depth budget, any fuel), calls included. -/
theorem replayStepCmd_grows (cfg : ReplayCfg Expression) (π : String → Option Procedure) :
    ∀ (k d : Nat), StepGrows cfg (fun _ => replayStepCmd (m := ReplayM Expression) π d k) := by
  intro k
  induction k <;> intro d _ env cmd <;> dsimp only <;> cases cmd <;> cel_unfold_step <;>
    repeat' first
    | (with_reducible refine Grows.bind ?_ (fun _ => ?_)) | with_reducible exact Grows.pure _ _
    | split | with_reducible exact Grows.throw _ _ | with_reducible exact Grows.forM_emit _ _
    | with_reducible exact stepBaseCmdStore_grows _ _ _ _ _
    | with_reducible exact runAbstractCallee_grows _ _ _ _ _ _
    | (with_reducible refine runCallee_grows ?_ _ _ _ _ _) | exact fun _ => ‹∀ d, StepGrows _ _› _ 0

/-- `evalBoundedList` is upward-monotone in fuel. -/
private theorem evalBoundedList_mono {a b : Nat} (hle : a ≤ b)
    (factory : Lambda.Factory CoreLParams) (store : RStore Expression) :
    ∀ (es vs : List Expression.Expr), evalBoundedList a factory store es = some vs →
      evalBoundedList b factory store es = some vs := fun es => by
  induction es <;> intro vs h <;>
    simp only [evalBoundedList, Calls.evalBoundedList, InterpLang.boundedEval] at h ⊢
    <;> grind [evalBounded_mono, Option.map_eq_some_iff]

/-- **Core per-command obligation for a sub-table.**  If every procedure the
    downstream table resolves is resolved identically upstream (`π' ⊆ π`), Core's
    command stepper over `π'` at fuel `k` is dominated by the one over `π` at any
    fuel `k' ≥ k`.  A downstream call to a procedure the downstream table lacks
    stops the downstream run; the upstream run may continue. -/
private theorem replayStepCmd_dom {K : RelCtx} (hK : K.EqCompat) (π' π : String → Option Procedure)
    (hsub : ∀ n p, π' n = some p → π n = some p) :
    ∀ (k k' : Nat), k ≤ k' → ∀ d env cmd,
      RelDom K (replayStepCmd (m := ReplayM Expression) π' d k env cmd)
        (replayStepCmd (m := ReplayM Expression) π d k' env cmd) Eq := by
  intro k
  induction k <;> intro k' hle d env cmd <;> rcases cmd with _ | ⟨fn, tyArgs, args, md⟩ <;>
    (try (simp only [replayStepCmd_cmd, bind_pure_comp]
          exact .bind_eq (stepBaseCmdStore_dom hK hle _ _ _) fun _ => .pure rfl))
  · have hg := replayStepCmd_grows K.cfgU π k' d 0 env (.call fn tyArgs args md)
    dsimp only at hg
    cel_unfold_step hg
    exact .throw_left hK.compat _ hg
  rename_i k ih
  obtain _ | k' := k'
  · omega
  have hg := replayStepCmd_grows K.cfgU π (k' + 1) d 0 env (.call fn tyArgs args md)
  dsimp only at hg
  cel_unfold_step hg
  obtain _ | d := d
  · exact .throw hK.compat _ _
  have hS : StepDom K _ _ := fun _ _ env cmd _ => ih k' (by omega) d env cmd
  rcases hπ' : π' fn with _ | p
  · exact .throw_left hK.compat _ hg
  simp only [hsub _ _ hπ'] at hg ⊢
  rcases hinst : ProcedureTypeInstantiation.instantiate p (tyArgs.getD []) with _ | p
  · simp only [hinst] at hg ⊢
    exact .throw hK.compat _ _
  simp only [hinst] at hg ⊢
  cases hev : Calls.evalBoundedList (k + 1) env.factory env.store.get (Calls.getInputExprs args)
  · exact .throw_left hK.compat _ hg
  have hev' : Calls.evalBoundedList (k' + 1) env.factory env.store.get (Calls.getInputExprs args)
    = some _ := evalBoundedList_mono (by omega) _ _ _ _ hev
  rw [hev']
  repeat' (first
    | with_reducible exact runCallee_dom hK hS _ _ _ (by omega) _
    | with_reducible exact runAbstractCallee_dom hK (by omega) _ _ _ _
    | cel_dstep hK)

/-! ## Claim transport, proved once -/

/-- The relational context of two production runs is compatible (`RelCtx.Compat`) when
    the event relation `ER` transfers target firing and hook decisions between them
    (`EventTransfer`) and no extra downstream event fires the downstream target. -/
theorem relProdCtx_compat {t' t : AssertId Expression} {f f' : Nat}
    {ER : IEvent Expression → IEvent Expression → Prop} (h : EventTransfer t' t f f' ER)
    (Extra : IEvent Expression → Prop)
    (hx : ∀ ev, Extra ev → assertFailureHalt t' f ev = false) (free : Bool := false) :
    (relProdCtx t' t f f' ER Extra free).Compat := ⟨rfl, rfl, h.halt, h.hook, hx⟩

/-- Raising the fuel cannot un-fire a target assertion: an event that fires the failing
    target at fuel `f` still fires it at every fuel `f' ≥ f`. -/
theorem assertFailureHalt_mono (target : AssertId Expression) {f f' : Nat} (hle : f ≤ f')
    (ev : IEvent Expression) (h : assertFailureHalt target f ev = true) :
    assertFailureHalt target f' ev = true := by
  cases ev <;> simp only [assertFailureHalt, Calls.assertFailureHalt, InterpLang.boundedEval] at h ⊢
    <;> grind [evalBounded_mono]

/-- Equality of events transfers target firing and hook decisions between two production
    runs for the same target, at downstream fuel `f ≤` upstream fuel `f'`. -/
theorem eventTransfer_eq (t : AssertId Expression) {f f' : Nat} (hle : f ≤ f') :
    EventTransfer t t f f' Eq :=
  ⟨fun _ _ he hh => he ▸ assertFailureHalt_mono t hle _ hh, fun ev _ he h => by
    subst he
    cases ev <;> simp only [enforceInterrupt, Calls.enforceInterrupt, InterpLang.boundedEval]
      at h ⊢ <;> split at h <;> grind [evalBounded_mono]⟩

/-- The relational context of two production runs for the same target, at fuels `f ≤ f'`,
    with events related by equality, is an equality instance (`RelCtx.EqCompat`). -/
theorem relProdCtx_eqCompat (t : AssertId Expression) {f f' : Nat} (hle : f ≤ f') :
    (relProdCtx t t f f' Eq).EqCompat :=
  ⟨relProdCtx_compat (eventTransfer_eq t hle) _ nofun, rfl, fun _ => rfl⟩

/-- **Whole-run claim transport, proved once.**  If Core's command stepper over the
    downstream table `π'` is dominated by the one over the upstream table `π`
    (`IsReplaySimulation`), a downstream claim genuine and feasible at fuel `f` is genuine
    and feasible upstream, on the same configuration and oracle, at every fuel `f' ≥ f`, at the
    same call-depth limit `d`. -/
theorem claim_back_of_simulation {π' π : String → Option Procedure}
    (hsim : IsReplaySimulation π' π) (target : AssertId Expression) {f f' : Nat}
    (hle : f ≤ f') (c : CexA Expression Command) {d : Nat}
    (h : genuineFeasible π' target f c d) : genuineFeasible π target f' c d := by
  simp only [genuineFeasible_iff_genuineEnforced, genuineEnforced, Calls.genuineEnforced,
    Calls.runCallInterp_eq, runReplay_genuine_iff] at h ⊢
  have hK := relProdCtx_eqCompat target hle
  exact (runInterp_dom hK (hsim _ hK d) f f' hle c.cfg).fired hK.compat
    ⟨.inr rfl, .inr rfl, .refl_eq (fun _ => rfl) _⟩ h

/-- A sub-table (`π' ⊆ π`) is a replay simulation. -/
theorem isReplaySimulation_of_sub {π' π : String → Option Procedure}
    (hsub : ∀ n p, π' n = some p → π n = some p) : IsReplaySimulation π' π :=
  fun _ hK d _ _ _ _ hle => replayStepCmd_dom hK π' π hsub _ _ hle d _ _

/-- **Replay fuel monotonicity**: a claim genuine and feasible at fuel `f` is genuine
    and feasible at every fuel `f' ≥ f`, at the same call-depth limit `d`. -/
theorem genuineFeasible_fuel_mono (π : String → Option Procedure)
    (target : AssertId Expression) {f f' : Nat} (hle : f ≤ f') (c : CexA Expression Command)
    {d : Nat} (h : genuineFeasible π target f c d) : genuineFeasible π target f' c d :=
  claim_back_of_simulation (isReplaySimulation_of_sub fun _ _ => id) target hle c h

end -- public section

end Core
