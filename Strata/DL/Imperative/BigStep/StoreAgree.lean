/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.Util.ListUtils

/-! # Replaying a run from an agreeing store

A run of the reference event semantics from a value-valued store `σ` can be replayed from a store
`σ'` that agrees with `σ` on the variables the run reads and elsewhere agrees with it or is
undefined (`Agree`, `OAgree` for outcomes): every condition evaluates alike, for a factory
evaluating alike on well-formed stores agreeing on the free variables (`EvCongr`).  Agreement is
kept by leaving a scope or a block, by restricting the agreed variables, and by defining a
variable as a value in both stores (`agree_def`); a command step is replayed event by event
(`cmd_sim`, events related by `EvReplay`).  A failure check observes of an event its kind, label,
condition, metadata and the condition's value (`Event.obs`, defined in `CmdTrace`): replaying
events are observed alike (`List.Rel₂.map_obs`), and traces observed alike have the same
feasibility (`feasible_obs`) and the same failing occurrences (`failsAt_obs`).

Key definitions: `Agree`, `OAgree`, `EvCongr`, `ArgReplay`, `EvReplay`.

Key theorems: `cmd_sim`, `ev_agree`, `agree_def`, `List.Rel₂.map_obs`, `feasible_obs`,
`failsAt_obs`, `WellFormedStore.proj`. -/

namespace Imperative

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasBool P] [HasFvar P] [HasFvars P] [LawfulHasVal P]

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P]
    [HasFvars P] in
/-- Assumptions evaluating to `true` along a trace evaluate to `true` along every trace observed
    like it. -/
theorem feasible_obs {evs evs' : List (Event P)}
    (hm : evs'.map Event.obs = evs.map Event.obs) (h : Trace.AssumptionsHold P evalInterp () evs) :
    Trace.AssumptionsHold P evalInterp () evs' := by
  intro a ha
  obtain ⟨e, he, heq⟩ := List.mem_map.1 (hm ▸ List.mem_map_of_mem (f := Event.obs) ha)
  cases e with
  | assume a' =>
    simp only [Event.obs, Prod.mk.injEq] at heq
    show P.eval _ _ _ = _
    rw [← heq.2.2.2.2.2, ← heq.2.2.2.2.1]
    exact h a' he
  | assert | cover => simp [Event.obs] at heq

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P]
    [HasFvars P] in
/-- An event observed like a failing occurrence of `t` with the condition `e` is one. -/
theorem failsAt_obs {t : AssertId P} {e : P.Expr} {ev ev' : Event P}
    (hm : Event.obs ev' = Event.obs ev) (h : FailsAt t e ev) : FailsAt t e ev' := by
  cases ev <;> cases ev' <;> simp only [Event.obs, FailsAt, Prod.mk.injEq] at hm h ⊢ <;> grind

/-- `σ'` agrees with `σ` on `N`, and wherever `σ'` is defined (`StoreAgreement σ' σ`). -/
@[expose] def Agree (N : List P.Ident) (σ σ' : SemanticStore P) : Prop :=
  (∀ y ∈ N, σ' y = σ y) ∧ StoreAgreement σ' σ

/-- The outcomes have the same kind and label, their stores agree on `N`, and the first
    store is value-valued. -/
@[expose] def OAgree (F : P.Factory) (N : List P.Ident) : Outcome P → Outcome P → Prop
  | .normal σ, .normal σ' => Agree N σ σ' ∧ WellFormedStore σ F
  | .exit l σ, .exit l' σ' => l = l' ∧ Agree N σ σ' ∧ WellFormedStore σ F
  | _, _ => False

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [LawfulHasVal P] [HasFvars P] in
/-- Agreement on `N` gives agreement on any subset of `N`. -/
theorem Agree.mono {N N' : List P.Ident} {σ σ' : SemanticStore P}
    (h : Agree N σ σ') (hN : ∀ y ∈ N', y ∈ N) : Agree N' σ σ' :=
  ⟨fun y hy => h.1 y (hN y hy), h.2⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [LawfulHasVal P] [HasFvars P] in
/-- Leaving a scope keeps agreement. -/
theorem Agree.proj {N : List P.Ident} {σp σp' σ σ' : SemanticStore P}
    (hp : Agree N σp σp') (h : Agree N σ σ') :
    Agree N (projectStore σp σ) (projectStore σp' σ') := by
  grind [projectStore, Agree, storeAgreement_iff]

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P]
  [LawfulHasVal P]

omit [HasFvars P] in
/-- Leaving a scope keeps the store value-valued. -/
theorem WellFormedStore.proj {F : P.Factory} {σp σ : SemanticStore P}
    (h : WellFormedStore σ F) : WellFormedStore (projectStore σp σ) F :=
  fun x v hx => h x v (by grind [projectStore])

omit [HasFvars P] in
/-- Leaving an `ite` branch keeps outcome agreement. -/
theorem OAgree.proj {F : P.Factory} {N : List P.Ident} {σ σ' : SemanticStore P}
    {o o' : Outcome P} (hA : Agree N σ σ') (h : OAgree F N o o') :
    OAgree F N (o.proj σ) (o'.proj σ') := by
  cases o <;> cases o' <;> simp_all [OAgree, Outcome.proj, Agree.proj, WellFormedStore.proj]

omit [HasFvars P] in
/-- Leaving a block keeps outcome agreement. -/
theorem OAgree.block {F : P.Factory} {N : List P.Ident} {σ σ' : SemanticStore P}
    {o o' : Outcome P} (l : String) (hA : Agree N σ σ') (h : OAgree F N o o') :
    OAgree F N (o.block l σ) (o'.block l σ') := by
  cases o <;> cases o' <;> grind [OAgree, Outcome.block, Agree.proj hA, WellFormedStore.proj]

omit [HasFvars P] in
/-- Outcome agreement on `N` gives outcome agreement on any subset of `N`. -/
theorem OAgree.mono {F : P.Factory} {N N' : List P.Ident} {o o' : Outcome P}
    (h : OAgree F N o o') (hN : ∀ y ∈ N', y ∈ N) : OAgree F N' o o' := by
  cases o <;> cases o' <;> simp only [OAgree] at h ⊢ <;> grind [Agree.mono]

omit [HasFvars P] in
/-- A store agreeing with a value-valued store, elsewhere undefined, is value-valued. -/
theorem Agree.canon {F : P.Factory} {N : List P.Ident} {σ σ' : SemanticStore P}
    (hA : Agree N σ σ') (hC : WellFormedStore σ F) : WellFormedStore σ' F := fun y v hv =>
  hC y v (storeAgreement_supplies_mono_premise _ _ hA.2 y v hv)

end

variable {F : P.Factory}

/-- Value-valued stores agreeing on the free variables of an expression evaluate it alike
    under the factory `F`. -/
@[expose] def EvCongr (F : P.Factory) : Prop :=
  ∀ ⦃σ σ' : SemanticStore P⦄, WellFormedStore σ F → WellFormedStore σ' F → ∀ e : P.Expr,
    (∀ y ∈ HasFvars.getFvars e, σ' y = σ y) → P.eval F σ' e = P.eval F σ e

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A factory evaluating alike on well-formed stores agreeing on the free variables
    (`WellFormedSemanticEvalExprCongr`) evaluates alike in value-valued stores agreeing on the
    free variables. -/
theorem evCongr_of_congr (hcong : WellFormedSemanticEvalExprCongr F) : EvCongr F :=
  fun _ _ hC hC' e he => hcong e _ _ hC' hC he

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- An expression whose free variables are in `N` evaluates alike in two stores agreeing on
    `N`, the first value-valued. -/
theorem ev_agree (hE : EvCongr F) {N : List P.Ident} {σ σ' : SemanticStore P}
    (hC : WellFormedStore σ F) (hA : Agree N σ σ') {e : P.Expr}
    (he : ∀ y ∈ HasFvars.getFvars e, y ∈ N) :
    P.eval F σ' e = P.eval F σ e :=
  hE hC (hA.canon hC) e fun y hy => hA.1 y (he y hy)

/-- The argument `a'` replays the argument `a` of an event of factory `F`: both have factory
    `F` and the same label, condition and metadata; the store of `a` is value-valued, and the
    store of `a'` agrees with it on the free variables of the condition and elsewhere agrees
    with it or is undefined. -/
@[expose] def ArgReplay (F : P.Factory) (a a' : EventArg P) : Prop :=
  a.factory = F ∧ a'.factory = F ∧ a'.label = a.label ∧ a'.expr = a.expr ∧
    a'.metadata = a.metadata ∧ Agree (HasFvars.getFvars a.expr) a.store a'.store ∧
    WellFormedStore a.store F

/-- The event `e'` replays the event `e` of factory `F`: same kind, with replaying
    arguments (`ArgReplay`). -/
@[expose] def EvReplay (F : P.Factory) : Event P → Event P → Prop
  | .assert a, .assert a' => ArgReplay F a a'
  | .assume a, .assume a' => ArgReplay F a a'
  | .cover a, .cover a' => ArgReplay F a a'
  | _, _ => False

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A replaying event is observed like the event it replays. -/
theorem EvReplay.obs (hE : EvCongr F) {e e' : Event P} (h : EvReplay F e e') :
    Event.obs e' = Event.obs e := by
  have key : ∀ {a a' : EventArg P}, ArgReplay F a a' →
      (a'.label, a'.expr, a'.metadata, a'.factory, P.eval a'.factory a'.store a'.expr) =
        (a.label, a.expr, a.metadata, a.factory, P.eval a.factory a.store a.expr) := by
    rintro ⟨f, s, l, x, m⟩ ⟨f', s', l', x', m'⟩ ⟨rfl, rfl, rfl, rfl, rfl, hA, hC⟩
    exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (ev_agree hE hC hA fun _ hy => hy))))
  rcases e with a | a | a <;> rcases e' with a' | a' | a' <;> simp only [EvReplay] at h <;>
    simp only [Event.obs, key h]

omit [LawfulHasVal P] [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] in
/-- A trace replaying a trace event by event is observed like it. -/
theorem _root_.List.Rel₂.map_obs (hE : EvCongr F) {evs evs' : List (Event P)} :
    List.Rel₂ (EvReplay F) evs evs' → evs'.map Event.obs = evs.map Event.obs
  | .nil => rfl
  | .cons h hs => by simp only [List.map_cons, h.obs hE, hs.map_obs hE]

omit [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [LawfulHasVal P] [HasFvars P] in
/-- Defining `x` as the value `v` in both stores keeps agreement and value-validity. -/
theorem agree_def {N : List P.Ident} {σ σ1 σ' : SemanticStore P}
    {x : P.Ident} {v : P.Val} (hA : Agree (x :: N) σ σ') (hC : WellFormedStore σ F)
    (hv : HasVal.value F v) (h1 : σ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y) :
    Agree N σ1 (SemanticStore.update σ' x v) ∧ WellFormedStore σ1 F := by
  grind [Agree, SemanticStore.update, WellFormedStore, storeAgreement_iff]

omit [BEq P.Ident] [LawfulBEq P.Ident] in
/-- **A command step, replayed.**  A command step from the value-valued `σ`, replayed from
    a store agreeing with `σ` on the identifiers of the command and on `N`: a step of the
    same command, observed alike, to a store agreeing on `N` with the value-valued result. -/
theorem cmd_sim (hE : EvCongr F) {c : Cmd P} {σ σ1 σ' : SemanticStore P}
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

end -- public section

end Imperative
