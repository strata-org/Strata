/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DeadDefElimProps
public import Strata.DL.Imperative.BigStep.Adequacy
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.Util.ListUtilsProps
public import Strata.DL.Imperative.Logic.TraceInterp
import Strata.DL.Imperative.Logic.TraceInterpProps
import all Strata.DL.Imperative.Cmd

/-! # Erasing unread definitions over-approximates

Erasing unread `init`s (`deadDefElim`) keeps every failure: if a statement list fails a
target from a value-valued store, so does the list without its unread `init`s, from
the same store, at the same target (`deadDefElim_fails` in the big-step semantics
and `deadDefElim_failsE` in the reference event semantics for lists without loops), for a
factory evaluating alike on well-formed stores agreeing on the free variables
(`WellFormedSemanticEvalExprCongr`).  The run of the output follows the run of the input;
its store is the input's store without the erased variables, which no later statement
mentions, so every condition evaluates alike.

The trace of the output's run corresponds to the input's event by event (`DDEventRel`, lists
related position by position by `List.Rel₂`), and its outcome to the input's
(`DDOutcomeRel`), for runs (`deadDefElim_run_rel`) and for reaches (`deadDefElim_reach_rel`).
The correspondence reflects assertion validity when the condition interpretation
is stable under `DDArgRel` (`dd_assertValid_reflect`); evaluation to `true`
satisfies this requirement (`evalInterp_stableUnder`).

The transformation-level statement over the shared trace specification
(`OverapproximatesTracesUptoWhen` of `Strata.Transform.Specification`) needs an event language,
which this generic level does not have; it is stated for Core's (`EventLang.coreBlock`) by
`Core.DeadDefElim.deadDefElim_overapproximatesTraces` in `DeadDefElimCoreCorrect`.

The executable pass `deadDefElimH` has the same properties (`deadDefElimH_fails`,
`deadDefElimH_failsE`, `deadDefElimH_run_rel`, `deadDefElimH_reach_rel`): each is the property
of `deadDefElim` through `deadDefElimH_eq`.

Key theorems: `deadDefElim_fails`, `deadDefElim_failsE`, `deadDefElim_run_rel`,
`deadDefElim_reach_rel`, `dd_assertValid_reflect`, `evalInterp_stableUnder`, and their
`deadDefElimH` forms.

Key definitions: `StoreProjected`, `DDArgRel`, `Event.Matches`, `DDOutcomeRel`. -/

namespace Imperative
namespace DeadDefElim

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasBool P] [HasFvar P] [HasFvars P] [LawfulHasVal P]

/-! ## The run of the output follows the run of the input -/

/-- What a failure check observes of an event: its kind, label, condition, and the value of
    the condition in the event's store. -/
private def Event.obs : Event P → Nat × String × P.Expr × Option P.Expr
  | .assert a => (0, a.label, a.expr, P.eval a.factory a.store a.expr)
  | .assume a => (1, a.label, a.expr, P.eval a.factory a.store a.expr)
  | .cover a => (2, a.label, a.expr, P.eval a.factory a.store a.expr)

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P]
    [HasFvars P] in
/-- Assumptions evaluating to `true` along a trace evaluate to `true` along every trace observed
    like it. -/
private theorem feasible_obs {evs evs' : List (Event P)}
    (hm : evs'.map Event.obs = evs.map Event.obs) (h : Trace.AssumptionsHold P evalInterp () evs) :
    Trace.AssumptionsHold P evalInterp () evs' := by
  intro a ha
  obtain ⟨e, he, heq⟩ := List.mem_map.1 (hm ▸ List.mem_map_of_mem (f := Event.obs) ha)
  cases e with
  | assume a' =>
    simp only [Event.obs, Prod.mk.injEq] at heq
    show P.eval _ _ _ = _
    rw [← heq.2.2.2]
    exact h a' he
  | assert | cover => simp [Event.obs] at heq

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P]
    [HasFvars P] in
/-- An event observed like a failing occurrence of `t` is one. -/
private theorem failsAt_obs {t : AssertId P} {e e' : Event P}
    (hm : Event.obs e' = Event.obs e) (h : FailsAt t e) : FailsAt t e' := by
  cases e <;> cases e' <;> simp only [Event.obs, FailsAt, Prod.mk.injEq] at hm h ⊢ <;> grind

/-- `σ'` agrees with `σ` on `N` and is a projection of `σ`. -/
private def Agree (N : List P.Ident) (σ σ' : SemanticStore P) : Prop :=
  (∀ y ∈ N, σ' y = σ y) ∧ StoreProjected σ σ'

/-- The outcomes have the same kind and label, their stores agree on `N`, and the first
    store is value-valued. -/
private def OAgree (F : P.Factory) (N : List P.Ident) : Outcome P → Outcome P → Prop
  | .normal σ, .normal σ' => Agree N σ σ' ∧ WellFormedStore σ F
  | .exit l σ, .exit l' σ' => l = l' ∧ Agree N σ σ' ∧ WellFormedStore σ F
  | _, _ => False

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [LawfulHasVal P] [HasFvars P] in
/-- Agreement on `N` gives agreement on any subset of `N`. -/
private theorem Agree.mono {N N' : List P.Ident} {σ σ' : SemanticStore P}
    (h : Agree N σ σ') (hN : ∀ y ∈ N', y ∈ N) : Agree N' σ σ' :=
  ⟨fun y hy => h.1 y (hN y hy), h.2⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [LawfulHasVal P] [HasFvars P] in
/-- Leaving a scope keeps agreement. -/
private theorem Agree.proj {N : List P.Ident} {σp σp' σ σ' : SemanticStore P}
    (hp : Agree N σp σp') (h : Agree N σ σ') :
    Agree N (projectStore σp σ) (projectStore σp' σ') := by
  refine ⟨fun y hy => by simp [projectStore, hp.1 y hy, h.1 y hy], storeAgreement_iff.2 ?_⟩
  intro y
  simp only [projectStore]
  rcases storeAgreement_iff.1 hp.2 y with hy | hy <;>
    rcases storeAgreement_iff.1 h.2 y with hz | hz <;> simp [hy, hz]

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P]
  [LawfulHasVal P]

omit [HasFvars P] in
/-- Leaving a scope keeps the store value-valued. -/
private theorem _root_.Imperative.WellFormedStore.proj {F : P.Factory}
    {σp σ : SemanticStore P} (h : WellFormedStore σ F) :
    WellFormedStore (projectStore σp σ) F := fun y v hv => by
  simp only [projectStore] at hv
  split at hv
  · exact h y v hv
  · cases hv

omit [HasFvars P] in
/-- Leaving an `ite` branch keeps outcome agreement. -/
private theorem OAgree.proj {F : P.Factory} {N : List P.Ident} {σ σ' : SemanticStore P}
    {o o' : Outcome P} (hA : Agree N σ σ') (h : OAgree F N o o') :
    OAgree F N (o.proj σ) (o'.proj σ') := by
  rcases o with _ | _ <;> rcases o' with _ | _ <;> simp only [OAgree] at h
  · exact ⟨hA.proj h.1, h.2.proj⟩
  · exact ⟨h.1, hA.proj h.2.1, h.2.2.proj⟩

omit [HasFvars P] in
/-- Leaving a block keeps outcome agreement. -/
private theorem OAgree.block {F : P.Factory} {N : List P.Ident} {σ σ' : SemanticStore P}
    {o o' : Outcome P} (l : String) (hA : Agree N σ σ') (h : OAgree F N o o') :
    OAgree F N (o.block l σ) (o'.block l σ') := by
  rcases o with _ | _ <;> rcases o' with _ | _ <;> simp only [OAgree] at h
  · exact ⟨hA.proj h.1, h.2.proj⟩
  · obtain ⟨rfl, h1, h2⟩ := h
    simp only [Outcome.block]
    split
    · exact ⟨hA.proj h1, h2.proj⟩
    · exact ⟨rfl, hA.proj h1, h2.proj⟩

omit [HasFvars P] in
/-- Outcome agreement on `N` gives outcome agreement on any subset of `N`. -/
private theorem OAgree.mono {F : P.Factory} {N N' : List P.Ident} {o o' : Outcome P}
    (h : OAgree F N o o') (hN : ∀ y ∈ N', y ∈ N) : OAgree F N' o o' := by
  rcases o with _ | _ <;> rcases o' with _ | _ <;> simp only [OAgree] at h ⊢
  · exact ⟨h.1.mono hN, h.2⟩
  · exact ⟨h.1, h.2.1.mono hN, h.2.2⟩

omit [HasFvars P] in
/-- A store agreeing with a value-valued store, elsewhere undefined, is value-valued. -/
private theorem Agree.canon {F : P.Factory} {N : List P.Ident} {σ σ' : SemanticStore P}
    (hA : Agree N σ σ') (hC : WellFormedStore σ F) : WellFormedStore σ' F := fun y v hv =>
  hC y v (hA.2.supplies_mono_premise y v hv)

end

variable {F : P.Factory}

/-- Value-valued stores agreeing on the free variables of an expression evaluate it alike
    under the factory `F`. -/
private def EvCongr (F : P.Factory) : Prop :=
  ∀ ⦃σ σ' : SemanticStore P⦄, WellFormedStore σ F → WellFormedStore σ' F → ∀ e : P.Expr,
    (∀ y ∈ HasFvars.getFvars e, σ' y = σ y) → P.eval F σ' e = P.eval F σ e

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A factory evaluating alike on well-formed stores agreeing on the free variables
    (`WellFormedSemanticEvalExprCongr`) evaluates alike in value-valued stores agreeing on the
    free variables. -/
private theorem evCongr_of_congr (hcong : WellFormedSemanticEvalExprCongr F) : EvCongr F :=
  fun _ _ hC hC' e he => hcong e _ _ hC' hC he

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- An expression whose free variables are in `N` evaluates alike in two stores agreeing on
    `N`, the first value-valued. -/
private theorem ev_agree (hE : EvCongr F) {N : List P.Ident} {σ σ' : SemanticStore P}
    (hC : WellFormedStore σ F) (hA : Agree N σ σ') {e : P.Expr}
    (he : ∀ y ∈ HasFvars.getFvars e, y ∈ N) :
    P.eval F σ' e = P.eval F σ e :=
  hE hC (hA.canon hC) e fun y hy => hA.1 y (he y hy)

/-- The argument `a'` replays the argument `a` of an event of factory `F`: both have factory
    `F` and the same label, condition and metadata; the store of `a` is value-valued, and the
    store of `a'` agrees with it on the free variables of the condition and elsewhere agrees
    with it or is undefined. -/
private def ArgReplay (F : P.Factory) (a a' : EventArg P) : Prop :=
  a.factory = F ∧ a'.factory = F ∧ a'.label = a.label ∧ a'.expr = a.expr ∧
    a'.metadata = a.metadata ∧ Agree (HasFvars.getFvars a.expr) a.store a'.store ∧
    WellFormedStore a.store F

/-- The event `e'` replays the event `e` of factory `F`: same kind, with replaying
    arguments (`ArgReplay`). -/
private def EvReplay (F : P.Factory) : Event P → Event P → Prop
  | .assert a, .assert a' => ArgReplay F a a'
  | .assume a, .assume a' => ArgReplay F a a'
  | .cover a, .cover a' => ArgReplay F a a'
  | _, _ => False

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A replaying event is observed like the event it replays. -/
private theorem EvReplay.obs (hE : EvCongr F) {e e' : Event P} (h : EvReplay F e e') :
    Event.obs e' = Event.obs e := by
  have key : ∀ {a a' : EventArg P}, ArgReplay F a a' →
      (a'.label, a'.expr, P.eval a'.factory a'.store a'.expr) =
        (a.label, a.expr, P.eval a.factory a.store a.expr) := by
    rintro ⟨f, s, l, x, m⟩ ⟨f', s', l', x', m'⟩ ⟨rfl, rfl, rfl, rfl, -, hA, hC⟩
    exact congrArg _ (congrArg _ (ev_agree hE hC hA fun _ hy => hy))
  rcases e with a | a | a <;> rcases e' with a' | a' | a' <;> simp only [EvReplay] at h <;>
    simp only [Event.obs, key h]

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A trace replaying a trace event by event is observed like it. -/
private theorem _root_.List.Rel₂.map_obs (hE : EvCongr F) {evs evs' : List (Event P)} :
    List.Rel₂ (EvReplay F) evs evs' → evs'.map Event.obs = evs.map Event.obs
  | .nil => rfl
  | .cons h hs => by simp only [List.map_cons, h.obs hE, hs.map_obs hE]

omit [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P] [HasFvars P] in
/-- Defining `x` as the value `v` in both stores keeps agreement and value-validity. -/
private theorem agree_def {N : List P.Ident} {σ σ1 σ' : SemanticStore P}
    {x : P.Ident} {v : P.Expr} (hA : Agree (x :: N) σ σ') (hC : WellFormedStore σ F)
    (hv : HasVal.value F v) (h1 : σ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y) :
    Agree N σ1 (SemanticStore.update σ' x v) ∧ WellFormedStore σ1 F := by
  refine ⟨⟨fun y hy => ?_, storeAgreement_iff.2 fun y => ?_⟩, fun y w hw => ?_⟩ <;>
    by_cases hyx : x = y
  · simp [SemanticStore.update, ← hyx, h1]
  · simp [SemanticStore.update, Ne.symm hyx, hfr y hyx, hA.1 y (.tail _ hy)]
  · simp [SemanticStore.update, ← hyx, h1]
  · simp only [SemanticStore.update, ite_eq_right (Ne.symm hyx), hfr y hyx]
    exact storeAgreement_iff.1 hA.2 y
  · rw [← hyx, h1] at hw
    cases hw
    exact hv
  · exact hC y w (hfr y hyx ▸ hw)

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] in
/-- An `init` step defines its undefined variable as a value, keeps the other variables and
    emits no event. -/
private theorem evalE_init_inv {σ σ1 : SemanticStore P} {x : P.Ident} {ty : P.Ty}
    {e : ExprOrNondet P} {md : MetaData P} {evs : List (Event P)}
    (h : EvalE F σ (.cmd (.init x ty e md)) σ1 evs) :
    ∃ v, HasVal.value F v ∧ σ x = none ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] := by
  cases e with
  | det e =>
    obtain ⟨v, -, h0, h1, hfr, rfl, hty⟩ := evalE_init_det_inv_typed h
    exact ⟨v, LawfulHasVal.valueOfTy_isVal _ _ _ hty, h0, h1, hfr, rfl⟩
  | nondet => exact evalE_init_nondet_inv h

omit [BEq P.Ident] [LawfulBEq P.Ident] in
/-- **A command step, replayed.**  A command step from the value-valued `σ`, replayed from
    a store agreeing with `σ` on the identifiers of the command and on `N`: a step of the
    same command, observed alike, to a store agreeing on `N` with the value-valued result. -/
private theorem cmd_sim (hE : EvCongr F) {c : Cmd P} {σ σ1 σ' : SemanticStore P}
    {evs : List (Event P)} {N : List P.Ident} (h : EvalE F σ (.cmd c) σ1 evs)
    (hC : WellFormedStore σ F) (hA : Agree (Stmt.idents (.cmd (.cmd c) : PStmt P) ++ N) σ σ') :
    ∃ σ1' evs', EvalE F σ' (.cmd c) σ1' evs' ∧ List.Rel₂ (EvReplay F) evs evs' ∧
      Agree N σ1 σ1' ∧ WellFormedStore σ1 F := by
  have hev : ∀ e, (∀ y ∈ HasFvars.getFvars e, y ∈ Stmt.idents (.cmd (.cmd c) : PStmt P)) →
      P.eval F σ' e = P.eval F σ e := fun e he =>
    ev_agree hE hC hA fun y hy => List.mem_append_left _ (he y hy)
  have hobl : ∀ e, Stmt.idents (.cmd (.cmd c) : PStmt P) = HasFvars.getFvars e →
      Agree (HasFvars.getFvars e) σ σ' := fun e he =>
    hA.mono fun y hy => List.mem_append_left _ (he ▸ hy)
  cases c with
  | init x ty e md =>
    have hx : σ' x = σ x := hA.1 x (by cases e <;> simp [Stmt.idents])
    have hA' : Agree (x :: N) σ σ' := hA.mono fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · cases e <;> simp [Stmt.idents]
      · exact List.mem_append_right _ hy
    cases e with
    | det e =>
      match h with
      | .eval_init (v := v) hv (.init h0 h1 hfr) hty hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_init ((hev e fun y hy => by simp [Stmt.idents, hy]).trans hv)
          (.init (hx.trans h0) hU1 hU2) hty hwf, .nil,
          agree_def hA' hC (LawfulHasVal.valueOfTy_isVal _ _ _ hty) h1 hfr⟩
    | nondet =>
      match h with
      | .eval_init_unconstrained (v := v) (.init h0 h1 hfr) hty hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_init_unconstrained (.init (hx.trans h0) hU1 hU2) hty hwf, .nil,
          agree_def hA' hC (LawfulHasVal.valueOfTy_isVal _ _ _ hty) h1 hfr⟩
  | set x e md =>
    have hx : σ' x = σ x := hA.1 x (by cases e <;> simp [Stmt.idents])
    have hA' : Agree (x :: N) σ σ' := hA.mono fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · cases e <;> simp [Stmt.idents]
      · exact List.mem_append_right _ hy
    cases e with
    | det e =>
      match h with
      | .eval_set (v := v) hv (.update h0 h1 hfr) ⟨p, ty, hp, hpt, hvt⟩ hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_set ((hev e fun y hy => by simp [Stmt.idents, hy]).trans hv)
          (.update (hx.trans h0) hU1 hU2) ⟨p, ty, hx.trans hp, hpt, hvt⟩ hwf, .nil,
          agree_def hA' hC (LawfulHasVal.valueOfTy_isVal _ _ _ hvt) h1 hfr⟩
    | nondet =>
      match h with
      | .eval_set_nondet (v := v) (.update h0 h1 hfr) ⟨p, ty, hp, hpt, hvt⟩ hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_set_nondet (.update (hx.trans h0) hU1 hU2)
          ⟨p, ty, hx.trans hp, hpt, hvt⟩ hwf, .nil,
          agree_def hA' hC (LawfulHasVal.valueOfTy_isVal _ _ _ hvt) h1 hfr⟩
  | assert l e md =>
    obtain ⟨rfl, rfl⟩ := evalE_assert_inv h
    exact ⟨σ', _, .eval_assert, .cons ⟨rfl, rfl, rfl, rfl, rfl, hobl e rfl, hC⟩ .nil,
      hA.mono fun y hy => List.mem_append_right _ hy, hC⟩
  | assume l e md =>
    obtain ⟨rfl, rfl⟩ := evalE_assume_inv h
    exact ⟨σ', _, .eval_assume, .cons ⟨rfl, rfl, rfl, rfl, rfl, hobl e rfl, hC⟩ .nil,
      hA.mono fun y hy => List.mem_append_right _ hy, hC⟩
  | cover l e md =>
    obtain ⟨rfl, rfl⟩ := evalE_cover_inv h
    exact ⟨σ', _, .eval_cover, .cons ⟨rfl, rfl, rfl, rfl, rfl, hobl e rfl, hC⟩ .nil,
      hA.mono fun y hy => List.mem_append_right _ hy, hC⟩

omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [LawfulHasVal P] [HasFvars P] in
/-- An erasable statement is an `init` whose variable is not in `live`. -/
private theorem erasable_inv {live : List P.Ident} {s : PStmt P}
    (h : erasable live s = true) :
    ∃ x ty e md, s = .cmd (.cmd (.init x ty e md)) ∧ x ∉ live := by
  rcases s with ((x | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;> simp_all [erasable]

omit [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] in
/-- Erasing an `init` of a variable outside `N` from a run: the store after the `init`
    still agrees with the replaying store on `N`. -/
private theorem erase_init {s : PStmt P} {x : P.Ident} {ty : P.Ty} {e : ExprOrNondet P}
    {md : MetaData P} (hs : s = .cmd (.cmd (.init x ty e md))) {N : List P.Ident}
    (hx : x ∉ N) {σ σ1 σ' : SemanticStore P} {evs : List (Event P)}
    (h : BRunS F s σ evs (.normal σ1)) (hC : WellFormedStore σ F) (hA : Agree N σ σ') :
    evs = [] ∧ Agree N σ1 σ' ∧ WellFormedStore σ1 F := by
  subst hs
  cases h with
  | cmd h =>
    obtain ⟨v, hv, h0, h1, hfr, rfl⟩ := evalE_init_inv h
    refine ⟨rfl, ⟨fun y hy => ?_, storeAgreement_iff.2 fun y => ?_⟩, fun y w hw => ?_⟩ <;>
      by_cases hyx : x = y
    · exact absurd (hyx ▸ hy) hx
    · rw [hfr y hyx, hA.1 y hy]
    · subst hyx
      exact .inr ((storeAgreement_iff.1 hA.2 x).elim (·.trans h0) id)
    · rw [hfr y hyx]
      exact storeAgreement_iff.1 hA.2 y
    · rw [← hyx, h1] at hw
      cases hw
      exact hv
    · exact hC y w (hfr y hyx ▸ hw)

omit [LawfulBEq P.Ident] in
mutual
/-- **A run of a list, replayed without the unread `init`s.**  A run of `ss` from the
    value-valued `σ` gives a run of `deadDefElim live ss` from any store agreeing with `σ` on
    the identifiers of the output and on `live`, observed alike, whose outcome agrees with
    the input's on `live`. -/
private theorem dd_run [LawfulBEq P.Ident] (hE : EvCongr F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRun F ss σ evs o → ∀ {live : List P.Ident} {σ' : SemanticStore P},
    WellFormedStore σ F → Agree (Block.idents (deadDefElim live ss) ++ live) σ σ' →
    ∃ evs' o', BRun F (deadDefElim live ss) σ' evs' o' ∧
      List.Rel₂ (EvReplay F) evs evs' ∧ OAgree F live o o'
  | _, _, _, _, .nil, _, _, hC, hA =>
    ⟨[], _, .nil, .nil, by simpa [deadDefElim, Block.idents] using hA, hC⟩
  | _, _, _, _, .cons_normal (s := s) (rest := rest) h1 h2, live, σ', hC, hA => by
    simp only [deadDefElim] at hA ⊢
    split at hA
    next he =>
      obtain ⟨x, ty, e, md, hs, hx⟩ := erasable_inv he
      obtain ⟨rfl, hA1, hC1⟩ := erase_init hs hx h1 hC hA
      rw [ite_eq_left he]
      exact dd_run hE h2 hC1 hA1
    next he =>
      rw [ite_eq_right he]
      obtain ⟨evs1', o1', h1', hm1, hO1⟩ :=
        dd_runS hE (live := Block.idents (deadDefElim live rest) ++ live) h1 hC
          (hA.mono fun y hy => by simpa [Block.idents] using hy)
      rcases o1' with σ1' | _ <;> simp only [OAgree] at hO1
      obtain ⟨evs2', o', h2', hm2, hO⟩ := dd_run hE h2 hO1.2 hO1.1
      exact ⟨evs1' ++ evs2', o', .cons_normal h1' h2', hm1.append hm2, hO⟩
  | _, _, _, _, .cons_exit (s := s) (rest := rest) h1, live, σ', hC, hA => by
    simp only [deadDefElim] at hA ⊢
    split at hA
    next he =>
      obtain ⟨x, ty, e, md, rfl, hx⟩ := erasable_inv he
      cases h1
    next he =>
      rw [ite_eq_right he]
      obtain ⟨evs1', o1', h1', hm1, hO1⟩ :=
        dd_runS hE (live := Block.idents (deadDefElim live rest) ++ live) h1 hC
          (hA.mono fun y hy => by simpa [Block.idents] using hy)
      rcases o1' with _ | ⟨l', σ1'⟩ <;> simp only [OAgree] at hO1
      obtain ⟨rfl, hA1, hC1⟩ := hO1
      exact ⟨evs1', _, .cons_exit h1', hm1,
        ⟨rfl, hA1.mono fun y hy => List.mem_append_right _ hy, hC1⟩⟩
/-- **A run of a statement, replayed without the unread `init`s** of its branches or body:
    `dd_run` for one statement. -/
private theorem dd_runS [LawfulBEq P.Ident] (hE : EvCongr F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRunS F s σ evs o → ∀ {live : List P.Ident} {σ' : SemanticStore P},
    WellFormedStore σ F → Agree (Stmt.idents (deadDefElimS live s) ++ live) σ σ' →
    ∃ evs' o', BRunS F (deadDefElimS live s) σ' evs' o' ∧
      List.Rel₂ (EvReplay F) evs evs' ∧ OAgree F live o o'
  | _, _, _, _, .cmd (c := .cmd c) h, _, _, hC, hA => by
    obtain ⟨σ1', evs', h', hm, hA1, hC1⟩ := cmd_sim hE h hC hA
    exact ⟨evs', _, .cmd h', hm, hA1, hC1⟩
  | _, _, _, _, .cmd (c := .call _ _ _) h, _, _, _, _ => h.elim
  | _, _, _, _, .ite_true (ess := ess) hc h, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', o', h', hm, hO⟩ := dd_run hE (live := Block.idents (deadDefElim live ess) ++ live)
      h hC (hA.mono fun y hy => by simp only [List.mem_append] at hy ⊢; grind)
    exact ⟨evs', _, .ite_true ((ev_agree hE hC hA fun _ => List.mem_append_left _).trans hc) h',
      hm, (hO.mono fun y hy => List.mem_append_right _ hy).proj (hA.mono fun y hy => by simp [hy])⟩
  | _, _, _, _, .ite_false hc h, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', o', h', hm, hO⟩ := dd_run hE (live := live) h hC
      (hA.mono fun y hy => by rcases List.mem_append.1 hy with hb | hb <;> simp [hb])
    exact ⟨evs', _, .ite_false ((ev_agree hE hC hA fun _ => List.mem_append_left _).trans hc) h',
      hm, hO.proj (hA.mono fun y hy => by simp [hy])⟩
  | _, _, _, _, .ite_nondet_true (ess := ess) h, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', o', h', hm, hO⟩ := dd_run hE (live := Block.idents (deadDefElim live ess) ++ live)
      h hC (hA.mono fun y hy => by simp only [List.mem_append] at hy ⊢; grind)
    exact ⟨evs', _, .ite_nondet_true h', hm,
      (hO.mono fun y hy => List.mem_append_right _ hy).proj (hA.mono fun y hy => by simp [hy])⟩
  | _, _, _, _, .ite_nondet_false h, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', o', h', hm, hO⟩ := dd_run hE (live := live) h hC
      (hA.mono fun y hy => by rcases List.mem_append.1 hy with hb | hb <;> simp [hb])
    exact ⟨evs', _, .ite_nondet_false h', hm, hO.proj (hA.mono fun y hy => by simp [hy])⟩
  | _, _, _, _, .block (l := l) h, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents] at hA ⊢
    obtain ⟨evs', o', h', hm, hO⟩ := dd_run hE h hC hA
    exact ⟨evs', _, .block h', hm, hO.block l (hA.mono fun y hy => by simp [hy])⟩
  | _, _, _, _, .exit, live, σ', hC, hA =>
    ⟨[], _, .exit, .nil, rfl, hA.mono fun y hy => List.mem_append_right _ hy, hC⟩
  | _, _, _, _, .typeDecl, live, σ', hC, hA =>
    ⟨[], _, .typeDecl, .nil, hA.mono fun y hy => List.mem_append_right _ hy, hC⟩
end

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] [LawfulHasVal P]

mutual
/-- A run of a list emitting a nonempty trace reaches the end of that trace. -/
private theorem brun_breach : ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRun F ss σ evs o → evs ≠ [] → BReach F ss σ evs
  | _, _, _, _, .nil, h => absurd rfl h
  | _, _, _, _, .cons_normal (evs1 := evs1) (evs2 := evs2) h1 h2, h => by
    by_cases h2e : evs2 = []
    · subst h2e
      rw [List.append_nil] at h ⊢
      exact .here (brun_breachS h1 h)
    · exact .later h1 (brun_breach h2 h2e)
  | _, _, _, _, .cons_exit h1, h => .here (brun_breachS h1 h)
/-- A run of a statement emitting a nonempty trace reaches the end of that trace. -/
private theorem brun_breachS : ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRunS F s σ evs o → evs ≠ [] → BReachS F s σ evs
  | _, _, _, _, .cmd h, _ => .cmd h
  | _, _, _, _, .ite_true hc h, he => .ite_true hc (brun_breach h he)
  | _, _, _, _, .ite_false hc h, he => .ite_false hc (brun_breach h he)
  | _, _, _, _, .ite_nondet_true h, he => .ite_nondet_true (brun_breach h he)
  | _, _, _, _, .ite_nondet_false h, he => .ite_nondet_false (brun_breach h he)
  | _, _, _, _, .block h, he => .block (brun_breach h he)
  | _, _, _, _, .exit, he => absurd rfl he
  | _, _, _, _, .typeDecl, he => absurd rfl he
end
end

omit [LawfulBEq P.Ident] in
mutual
/-- **A reach of a list, replayed without the unread `init`s.**  A reach of `ss` from the
    value-valued `σ` emitting a nonempty trace gives a reach of `deadDefElim live ss` from
    any store agreeing with `σ` on the identifiers of the output and on `live`, observed
    alike. -/
private theorem dd_reach [LawfulBEq P.Ident] (hE : EvCongr F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}, BReach F ss σ evs →
    evs ≠ [] → ∀ {live : List P.Ident} {σ' : SemanticStore P}, WellFormedStore σ F →
    Agree (Block.idents (deadDefElim live ss) ++ live) σ σ' →
    ∃ evs', BReach F (deadDefElim live ss) σ' evs' ∧ List.Rel₂ (EvReplay F) evs evs'
  | _, _, _, .here (s := s) (rest := rest) h, hne, live, σ', hC, hA => by
    simp only [deadDefElim] at hA ⊢
    split at hA
    next he =>
      obtain ⟨x, ty, e, md, rfl, hx⟩ := erasable_inv he
      cases h with
      | cmd h => exact absurd (evalE_init_inv h).choose_spec.2.2.2.2 hne
    next he =>
      rw [ite_eq_right he]
      obtain ⟨evs', h', hm⟩ :=
        dd_reachS hE (live := Block.idents (deadDefElim live rest) ++ live) h hne hC
          (hA.mono fun y hy => by simpa [Block.idents] using hy)
      exact ⟨evs', .here h', hm⟩
  | _, _, _, .later (s := s) (rest := rest) (evs1 := evs1) (evs2 := evs2) h1 h2, hne, live, σ',
      hC, hA => by
    simp only [deadDefElim] at hA ⊢
    split at hA
    next he =>
      obtain ⟨x, ty, e, md, hs, hx⟩ := erasable_inv he
      obtain ⟨rfl, hA1, hC1⟩ := erase_init hs hx h1 hC hA
      rw [ite_eq_left he]
      exact dd_reach hE h2 (by simpa using hne) hC1 hA1
    next he =>
      rw [ite_eq_right he]
      obtain ⟨evs1', o1', h1', hm1, hO1⟩ :=
        dd_runS hE (live := Block.idents (deadDefElim live rest) ++ live) h1 hC
          (hA.mono fun y hy => by simpa [Block.idents] using hy)
      rcases o1' with σ1' | _ <;> simp only [OAgree] at hO1
      by_cases h2e : evs2 = []
      · subst h2e
        have hne1 : evs1' ≠ [] := hm1.ne_nil (by simpa using hne)
        exact ⟨evs1', .here (brun_breachS h1' hne1), by simpa using hm1⟩
      · obtain ⟨evs2', h2', hm2⟩ := dd_reach hE h2 h2e hO1.2 hO1.1
        exact ⟨evs1' ++ evs2', .later h1' h2', hm1.append hm2⟩
/-- **A reach of a statement, replayed without the unread `init`s** of its branches or body:
    `dd_reach` for one statement. -/
private theorem dd_reachS [LawfulBEq P.Ident] (hE : EvCongr F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}, BReachS F s σ evs →
    evs ≠ [] → ∀ {live : List P.Ident} {σ' : SemanticStore P}, WellFormedStore σ F →
    Agree (Stmt.idents (deadDefElimS live s) ++ live) σ σ' →
    ∃ evs', BReachS F (deadDefElimS live s) σ' evs' ∧ List.Rel₂ (EvReplay F) evs evs'
  | _, _, _, .cmd (c := .cmd c) h, _, _, _, hC, hA => by
    obtain ⟨σ1', evs', h', hm, -⟩ := cmd_sim hE h hC hA
    exact ⟨evs', .cmd h', hm⟩
  | _, _, _, .cmd (c := .call _ _ _) h, _, _, _, _, _ => h.elim
  | _, _, _, .ite_true (ess := ess) hc h, hne, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', h', hm⟩ := dd_reach hE (live := Block.idents (deadDefElim live ess) ++ live) h
      hne hC (hA.mono fun y hy => by simp only [List.mem_append] at hy ⊢; grind)
    exact ⟨evs', .ite_true ((ev_agree hE hC hA fun _ => List.mem_append_left _).trans hc) h', hm⟩
  | _, _, _, .ite_false hc h, hne, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', h', hm⟩ := dd_reach hE (live := live) h hne hC
      (hA.mono fun y hy => by rcases List.mem_append.1 hy with hb | hb <;> simp [hb])
    exact ⟨evs', .ite_false ((ev_agree hE hC hA fun _ => List.mem_append_left _).trans hc) h', hm⟩
  | _, _, _, .ite_nondet_true (ess := ess) h, hne, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', h', hm⟩ := dd_reach hE (live := Block.idents (deadDefElim live ess) ++ live) h
      hne hC (hA.mono fun y hy => by simp only [List.mem_append] at hy ⊢; grind)
    exact ⟨evs', .ite_nondet_true h', hm⟩
  | _, _, _, .ite_nondet_false h, hne, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents, List.append_assoc] at hA ⊢
    obtain ⟨evs', h', hm⟩ := dd_reach hE (live := live) h hne hC
      (hA.mono fun y hy => by rcases List.mem_append.1 hy with hb | hb <;> simp [hb])
    exact ⟨evs', .ite_nondet_false h', hm⟩
  | _, _, _, .block h, hne, live, σ', hC, hA => by
    simp only [deadDefElimS, Stmt.idents] at hA ⊢
    obtain ⟨evs', h', hm⟩ := dd_reach hE h hne hC hA
    exact ⟨evs', .block h', hm⟩
end

/-- **Erasing unread definitions keeps failures (big-step).**  If the statement list `ss`
    fails the target `t` from the value-valued store `σ` (`Fails`: a run reaches a failing
    occurrence of `t`, every earlier assumption holding), then `deadDefElim live ss` (the
    list without the `init`s that no later statement, nor `live`, mentions) fails `t` from
    `σ`, for any factory evaluating alike on well-formed stores agreeing on the free variables
    (`WellFormedSemanticEvalExprCongr`). -/
theorem deadDefElim_fails (hcong : WellFormedSemanticEvalExprCongr F)
    (live : List P.Ident) {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P}
    (hC : WellFormedStore σ F) (h : Fails F ss σ t) : Fails F (deadDefElim live ss) σ t := by
  obtain ⟨evs, e, hb, hfeas, hfe⟩ := h
  have hE := evCongr_of_congr hcong
  obtain ⟨evs', hb', hm⟩ :=
    dd_reach hE hb (by simp) hC ⟨fun _ _ => rfl, StoreProjected.refl _⟩
  obtain ⟨a, e', rfl, ha, he⟩ := hm.append_singleton
  exact ⟨a, e', hb', feasible_obs (ha.map_obs hE) hfeas, failsAt_obs (he.obs hE) hfe⟩

/-- **Erasing unread definitions keeps failures (reference event semantics).**  If the
    statement list `ss` without loops (`Block.noLoops`) fails the target `t` from the value-valued
    store `σ` under the reference event semantics (`FailsE`, with failure flag `hf`), then
    `deadDefElim live ss` fails `t` from `σ` under it (with any failure flag `hf'`), for any
    factory evaluating alike on well-formed stores agreeing on the free variables
    (`WellFormedSemanticEvalExprCongr`) and evaluating Boolean guards to Booleans. -/
theorem deadDefElim_failsE [HasBoolOps P] (hcong : WellFormedSemanticEvalExprCongr F)
    (hWB : WellFormedSemanticEvalBool (P := P) F)
    (live : List P.Ident) {ss : PStmts P} (hss : Block.noLoops ss = true) {σ : SemanticStore P}
    {t : AssertId P} (hC : WellFormedStore σ F) {hf : Bool} (h : FailsE F hf ss σ t) (hf' : Bool) :
    FailsE F hf' (deadDefElim live ss) σ t :=
  fails_failsE hWB hf' (deadDefElim_fails hcong live hC (failsE_fails_noLoops hss h))

/-! ## Traces of the output related event by event

`DDEventRel` relates a source event to the event the run of the output emits in its place,
`DDOutcomeRel` a source outcome to the output's.  Neither depends on the program: a target
store is the source store with some bindings removed, and agrees with it on the free
variables of the condition. -/

section

/-- The argument `a'` of an event of the output of `deadDefElim` corresponds to the argument
    `a` of the source event: same factory, label, condition and metadata; the store of `a'` is
    the store of `a` with some bindings removed, and agrees with it on the free variables of
    the condition; the store of `a` is well formed and the factory evaluates alike on well-formed
    stores agreeing on the free variables. -/
structure DDArgRel (a a' : EventArg P) : Prop where
  factory_eq : a'.factory = a.factory
  label_eq : a'.label = a.label
  expr_eq : a'.expr = a.expr
  metadata_eq : a'.metadata = a.metadata
  store_projected : StoreProjected a.store a'.store
  store_fv : StoreAgreesOnFvars a'.store a.store a.expr
  storeWF : WellFormedStore a.store a.factory
  exprCongr : WellFormedSemanticEvalExprCongr a.factory

/-- Same-kind event matching induced by `DDArgRel`. -/
abbrev DDEventRel : Event P → Event P → Prop := Event.Matches DDArgRel

end

/-- The outcome `o'` of the output corresponds to the source outcome `o`: both end normally,
    or both exit with the same label, and the store of `o'` is the store of `o` with some
    bindings removed. -/
@[expose] def DDOutcomeRel : Outcome P → Outcome P → Prop
  | .normal σ, .normal σ' => StoreProjected σ σ'
  | .exit l σ, .exit l' σ' => l' = l ∧ StoreProjected σ σ'
  | _, _ => False

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P]
    [HasFvars P] in
/-- Outcomes agreeing on some names correspond. -/
private theorem OAgree.dd {N : List P.Ident} {o o' : Outcome P} (h : OAgree F N o o') :
    DDOutcomeRel o o' := by
  rcases o with _ | _ <;> rcases o' with _ | _ <;> simp only [OAgree, DDOutcomeRel] at h ⊢
  · exact h.1.2
  · exact ⟨h.1.symm, h.2.1.2⟩

section

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A replaying event of a factory evaluating alike on well-formed stores agreeing on the free
    variables corresponds to the event it replays. -/
private theorem EvReplay.dd (hcong : WellFormedSemanticEvalExprCongr F) {e e' : Event P}
    (h : EvReplay F e e') : DDEventRel e e' := by
  have key : ∀ {a a' : EventArg P}, ArgReplay F a a' → DDArgRel a a' := by
    rintro a a' ⟨hF, hF', hl, hx, hm, hA, hC⟩
    exact ⟨hF'.trans hF.symm, hl, hx, hm, hA.2, hA.1, hF ▸ hC,
      hF ▸ hcong⟩
  rcases e with a | a | a <;> rcases e' with a' | a' | a' <;> simp only [EvReplay] at h <;>
    exact key h

/-- **A reach of a list, and of its output.**  A reach of `ss` from the value-valued `σ`
    emitting a nonempty trace gives a reach of `deadDefElim live ss` from `σ` whose trace
    corresponds to it event by event (`DDEventRel`), for a factory evaluating alike on
    well-formed stores agreeing on the free variables. -/
theorem deadDefElim_reach_rel (hcong : WellFormedSemanticEvalExprCongr F) (live : List P.Ident)
    {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} (h : BReach F ss σ evs)
    (hne : evs ≠ []) (hC : WellFormedStore σ F) :
    ∃ evs', BReach F (deadDefElim live ss) σ evs' ∧ List.Rel₂ (DDEventRel) evs evs' := by
  have hE := evCongr_of_congr hcong
  obtain ⟨evs', h', hm⟩ := dd_reach hE h hne hC ⟨fun _ _ => rfl, StoreProjected.refl _⟩
  exact ⟨evs', h', hm.imp fun _ _ hr => hr.dd hcong⟩

/-- **A run of a list, and of its output.**  A run of `ss` from the value-valued `σ` gives a
    run of `deadDefElim live ss` from `σ` whose trace corresponds to it event by event
    (`DDEventRel`) and whose outcome corresponds to its outcome (`DDOutcomeRel`), for a
    factory evaluating alike on well-formed stores agreeing on the free variables. -/
theorem deadDefElim_run_rel (hcong : WellFormedSemanticEvalExprCongr F) (live : List P.Ident)
    {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P}
    (h : BRun F ss σ evs o) (hC : WellFormedStore σ F) :
    ∃ evs' o', BRun F (deadDefElim live ss) σ evs' o' ∧ List.Rel₂ (DDEventRel) evs evs' ∧
      DDOutcomeRel o o' := by
  have hE := evCongr_of_congr hcong
  obtain ⟨evs', o', h', hm, hO⟩ := dd_run hE h hC ⟨fun _ _ => rfl, StoreProjected.refl _⟩
  exact ⟨evs', o', h', hm.imp fun _ _ hr => hr.dd hcong, hO.dd⟩

end

/-! ## Assertion validity is reflected by the event correspondence -/

section

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P]
    [LawfulHasVal P] in
/-- Evaluation to `true` is stable under `DDArgRel`: corresponding event
arguments evaluate alike because the projected store agrees on the condition's
free variables. -/
theorem evalInterp_stableUnder :
    ConditionInterp.StableUnder (P := P) evalInterp DDArgRel := by
  intro _ a a' h
  have hwf' : WellFormedStore a'.store a.factory := fun x v hv =>
    h.storeWF x v (h.store_projected.supplies_mono_premise x v hv)
  simp only [evalInterp, h.factory_eq, h.expr_eq,
    h.exprCongr a.expr _ _ hwf' h.storeWF h.store_fv]

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P]
    [LawfulHasVal P] in
/-- **The event correspondence reflects assertion validity.** If `I` is
    stable under `DDArgRel`, validity of every occurrence of `aid` in `trace'`
    reflects to an event-by-event corresponding `trace`. -/
theorem dd_assertValid_reflect {I : ConditionInterp P} (hI : I.StableUnder DDArgRel) :
    ∀ trace trace', List.Rel₂ (DDEventRel) trace trace' → ∀ aid,
      Trace.AssertionValid P I aid trace' → Trace.AssertionValid P I aid trace :=
  fun _ _ h aid =>
    Trace.AssertionValidFrom_matches_reflect hI
      (fun h => ⟨h.label_eq.symm, h.expr_eq.symm⟩) aid .nil h

end

/-! ## The executable pass

`deadDefElimH`, the pass that runs, returns `deadDefElim`'s list (`deadDefElimH_eq`), so it has
every property of `deadDefElim`. -/

section
variable [Hashable P.Ident]

/-- **The executable pass keeps failures (big-step)**: if the statement list `ss` fails the
    target `t` from the value-valued store `σ` (`Fails`), so does `deadDefElimH live ss`, for any
    factory evaluating alike on well-formed stores agreeing on the free variables
    (`WellFormedSemanticEvalExprCongr`) (`deadDefElim_fails` for `deadDefElimH`). -/
theorem deadDefElimH_fails (hcong : WellFormedSemanticEvalExprCongr F)
    (live : List P.Ident) {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P}
    (hC : WellFormedStore σ F) (h : Fails F ss σ t) : Fails F (deadDefElimH live ss) σ t :=
  deadDefElimH_eq live ss ▸ deadDefElim_fails hcong live hC h

/-- **The executable pass keeps failures (reference event semantics)**: if the statement list
    `ss` without loops fails the target `t` from the value-valued store `σ` under the reference
    event semantics, so does `deadDefElimH live ss`, for any factory satisfying
    `WellFormedSemanticEvalExprCongr` and evaluating Boolean guards to Booleans
    (`deadDefElim_failsE` for `deadDefElimH`). -/
theorem deadDefElimH_failsE [HasBoolOps P] (hcong : WellFormedSemanticEvalExprCongr F)
    (hWB : WellFormedSemanticEvalBool (P := P) F)
    (live : List P.Ident) {ss : PStmts P} (hss : Block.noLoops ss = true) {σ : SemanticStore P}
    {t : AssertId P} (hC : WellFormedStore σ F) {hf : Bool} (h : FailsE F hf ss σ t) (hf' : Bool) :
    FailsE F hf' (deadDefElimH live ss) σ t :=
  deadDefElimH_eq live ss ▸ deadDefElim_failsE hcong hWB live hss hC h hf'

/-- **A reach of a list, and of the executable pass's output**: a reach of `ss` from the
    value-valued `σ` emitting a nonempty trace gives a reach of `deadDefElimH live ss` from `σ`
    whose trace corresponds to it event by event (`DDEventRel`), for a factory evaluating alike
    on well-formed stores agreeing on the free variables (`deadDefElim_reach_rel` for
    `deadDefElimH`). -/
theorem deadDefElimH_reach_rel (hcong : WellFormedSemanticEvalExprCongr F) (live : List P.Ident)
    {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} (h : BReach F ss σ evs)
    (hne : evs ≠ []) (hC : WellFormedStore σ F) :
    ∃ evs', BReach F (deadDefElimH live ss) σ evs' ∧ List.Rel₂ (DDEventRel) evs evs' :=
  deadDefElimH_eq live ss ▸ deadDefElim_reach_rel hcong live h hne hC

/-- **A run of a list, and of the executable pass's output**: a run of `ss` from the
    value-valued `σ` gives a run of `deadDefElimH live ss` from `σ` whose trace corresponds to
    it event by event (`DDEventRel`) and whose outcome corresponds to its outcome
    (`DDOutcomeRel`), for a factory evaluating alike on well-formed stores agreeing on the free
    variables (`deadDefElim_run_rel` for `deadDefElimH`). -/
theorem deadDefElimH_run_rel (hcong : WellFormedSemanticEvalExprCongr F) (live : List P.Ident)
    {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P}
    (h : BRun F ss σ evs o) (hC : WellFormedStore σ F) :
    ∃ evs' o', BRun F (deadDefElimH live ss) σ evs' o' ∧ List.Rel₂ (DDEventRel) evs evs' ∧
      DDOutcomeRel o o' :=
  deadDefElimH_eq live ss ▸ deadDefElim_run_rel hcong live h hC

end

end -- public section

end DeadDefElim
end Imperative
