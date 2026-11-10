/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.InsertLoopInvariantAssertsProps
public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.StoreRelationsProps
import all Strata.Transform.InsertLoopInvariantAsserts
import all Strata.DL.Imperative.Cmd

/-! # Inserting loop invariant checks over-approximates (big-step)

A list `ss'` that is `ss` with the checks of its loops inserted (`InsertLoopInvAsserts.BlockRel
[] ss ss'`, as each body that `Core.insertLoopInvariantAsserts` returns is) replays every run and
every reach of `ss` from a value-valued store, when `ss` is def-use well formed there, mentions
no reserved variable (no measure snapshot variable is one of its), its free-variable annotations
agree with a typing of the store, and each of its measures evaluates to an integer where its
annotations agree with the store:

* a run of `ss` gives a run of `ss'` with the same outcome, whose trace is the source's with
  each event's condition captured in a store extended with measure snapshots and assertions
  inserted (`Trace.InsertsAsserts`), and then assumptions inserted that evaluate to `true` or
  that follow an assertion of an invariant with the same value (`Trace.InsertsCheckedAssumes`)
  — `run_sim`;
* a reach of `ss` gives a reach of `ss'` with a trace so related — `reach_sim`.

The checked form of a loop asserts and then assumes its invariants before it, and assumes them
at the start of each iteration and after it, where the last assertion of them, at the end of the
previous iteration or before the loop, has the same value: their free variables are defined
where the loop starts (def-use well-formedness), so leaving an iteration keeps their values.  It
records the measure at the start of an iteration in a fresh variable, defined only in the
target's store: an `init` of the measure's value, which is an integer where the store has the
types of the measure's annotations.  After the loop, it assumes the negation of a deterministic
guard, which evaluates to `true` where the loop stops.

Key theorems: `InsertLoopInvAsserts.run_sim`, `InsertLoopInvAsserts.reach_sim`. -/

namespace Imperative
namespace InsertLoopInvAsserts

open BigStep

public section

-- The label prefixes are opaque to the proofs: unfolding them makes unification compute with
-- string literals.
attribute [local irreducible] Core.insertLoopInvAssertPrefix Core.insertLoopInvAssumePrefix
  Core.insertLoopInvAssertReservedPrefix

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P]
  [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P]

/-- The measure `m` evaluates under `F` to an integer in every store conforming to a typing that
    gives each annotated free variable of `m` its annotation. -/
@[expose] def MeasureEvaluates (F : P.Factory) (m : P.Expr) : Prop :=
  ∀ (Γ : VarTyping P) (σ : SemanticStore P), StoreHasTyping F σ Γ →
    Γ.annotates (HasFvars.getTypedFvars m) →
    ∃ v, P.eval F σ m = some v ∧ HasVal.valueOfTy F v HasInt.intTy

/-- How a trace of the checked form relates to a trace of the source, under the factory `F`,
    following the target events `before`: each event's condition captured with the same value,
    and assertions, assumptions evaluating to `true` and assumptions of an earlier inserted
    invariant assertion inserted, in any order.  It is inserting the assertions
    (`Trace.InsertsAsserts`) and then the assumptions (`Trace.InsertsCheckedAssumes`), which
    `Ins.split` shows. -/
private inductive Ins (F : P.Factory) : Trace P → Trace P → Trace P → Prop where
  | nil {before : Trace P} : Ins F before [] []
  | keep {before : Trace P} {e e' : Event P} {t t' : Trace P} :
      Event.SameValue (· = F) e e' → Ins F (before ++ [e']) t t' →
      Ins F before (e :: t) (e' :: t')
  | assert {before : Trace P} {a : EventArg P} {t t' : Trace P} :
      Ins F (before ++ [.assert a]) t t' → Ins F before t (.assert a :: t')
  | assumeTrue {before : Trace P} {a : EventArg P} {t t' : Trace P} :
      a.factory = F → P.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) →
      Ins F (before ++ [.assume a]) t t' → Ins F before t (.assume a :: t')
  | assumeChecked {before : Trace P} {a c : EventArg P} {t t' : Trace P} :
      Event.assert c ∈ before → InvCheck c → EventArg.SameValue (· = F) c a →
      Ins F (before ++ [.assume a]) t t' → Ins F before t (.assume a :: t')

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- `Ins` is closed under concatenation, the second part following the target events of the
    first. -/
private theorem Ins.append {F : P.Factory} {before t₁ t₁' t₂ t₂' : Trace P}
    (h₁ : Ins F before t₁ t₁') (h₂ : Ins F (before ++ t₁') t₂ t₂') :
    Ins F before (t₁ ++ t₂) (t₁' ++ t₂') := by
  induction h₁ with
  | nil => simpa using h₂
  | keep he _ ih => exact .keep he (ih (by simpa using h₂))
  | assert _ ih => exact .assert (ih (by simpa using h₂))
  | assumeTrue hf he _ ih => exact .assumeTrue hf he (ih (by simpa using h₂))
  | assumeChecked hc hC hs _ ih => exact .assumeChecked hc hC hs (ih (by simpa using h₂))

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- `Ins` is inserting the assertions and then the assumptions. -/
private theorem Ins.split {F : P.Factory} {before t t' : Trace P} (h : Ins F before t t') :
    ∃ m, Trace.InsertsAsserts (· = F) t m ∧
      Trace.InsertsCheckedAssumes (· = F) InvCheck before m t' := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | keep he _ ih =>
    obtain ⟨m, h₁, h₂⟩ := ih
    exact ⟨_, .keep he h₁, .keep h₂⟩
  | assert _ ih =>
    obtain ⟨m, h₁, h₂⟩ := ih
    exact ⟨_, .assert h₁, .keep h₂⟩
  | assumeTrue hf he _ ih =>
    obtain ⟨m, h₁, h₂⟩ := ih
    exact ⟨m, h₁, .assumeTrue hf he h₂⟩
  | assumeChecked hc hC hs _ ih =>
    obtain ⟨m, h₁, h₂⟩ := ih
    exact ⟨m, h₁, .assumeChecked hc hC hs h₂⟩

variable {F : P.Factory}

/-! ## Stores extended with measure snapshots -/

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- A store extending `σ` with variables in `E` agrees with `σ` outside `E`. -/
private theorem ext_agree {E : List P.Ident} {σ τ : SemanticStore P}
    (hext : StoreExtendsWith (· ∈ E) σ τ) {x : P.Ident} (hx : x ∉ E) : τ x = σ x := by
  rcases storeAgreement_iff.1 hext.1 x with h | h
  · exact h.symm
  · rw [h]
    cases hτ : τ x with
    | none => rfl
    | some _ =>
      rcases hext.2 x (by simp [hτ]) with hs | hs
      · simp [h] at hs
      · exact absurd hs hx

omit [HasFvar P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- An expression without free variables in `E` evaluates alike in a value-valued store and in
    a value-valued store extending it with variables in `E`. -/
private theorem ext_eval (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    {E : List P.Ident} {σ τ : SemanticStore P} (hext : StoreExtendsWith (· ∈ E) σ τ)
    (hT : WellFormedStore σ F) (hT' : WellFormedStore τ F) {e : P.Expr}
    (he : ∀ x ∈ HasFvars.getFvars e, x ∉ E) : P.eval F τ e = P.eval F σ e :=
  hcong e τ σ hT' hT fun x hx => ext_agree hext (he x hx)

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Changing the same variable `x` the same way in both stores keeps the extension. -/
private theorem ext_update {E : List P.Ident} {σ τ σ1 τ1 : SemanticStore P} {x : P.Ident}
    {v : P.Val} (hext : StoreExtendsWith (· ∈ E) σ τ) (h1 : σ1 x = some v)
    (h1' : τ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y) (hfr' : ∀ y, x ≠ y → τ1 y = τ y) :
    StoreExtendsWith (· ∈ E) σ1 τ1 := by
  refine ⟨storeAgreement_iff.2 fun y => ?_, fun y hy => ?_⟩
  · by_cases hxy : x = y
    · subst hxy; exact .inl (h1.trans h1'.symm)
    · rw [hfr y hxy, hfr' y hxy]; exact storeAgreement_iff.1 hext.1 y
  · by_cases hxy : x = y
    · subst hxy; exact .inl (by simp [h1])
    · rw [hfr' y hxy] at hy; rw [hfr y hxy]; exact hext.2 y hy

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Defining an undefined variable `x` in the extending store only extends it with `x`. -/
private theorem ext_init {E : List P.Ident} {σ τ : SemanticStore P} {x : P.Ident} {v : P.Val}
    (hext : StoreExtendsWith (· ∈ E) σ τ) (hx : τ x = none) :
    StoreExtendsWith (· ∈ x :: E) σ (SemanticStore.update τ x v) := by
  obtain ⟨hU1, hU2⟩ := update_facts τ x v
  refine ⟨storeAgreement_iff.2 fun y => ?_, fun y hy => ?_⟩
  · by_cases hxy : x = y
    · subst hxy
      rcases storeAgreement_iff.1 hext.1 x with h | h
      · exact .inr (h.trans hx)
      · exact .inr h
    · rw [hU2 y hxy]; exact storeAgreement_iff.1 hext.1 y
  · by_cases hxy : x = y
    · exact .inr (hxy ▸ List.mem_cons_self ..)
    · rw [hU2 y hxy] at hy; exact (hext.2 y hy).imp_right (List.mem_cons_of_mem _)

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Leaving a scope keeps the extension, with the variables of the entry store, when the
    source's scope keeps those of its entry store. -/
private theorem ext_proj {E E' : List P.Ident} {σ τ σ1 τ1 : SemanticStore P}
    (hext : StoreExtendsWith (· ∈ E) σ τ) (hext1 : StoreExtendsWith (· ∈ E') σ1 τ1)
    (hdom : ∀ x, (σ x).isSome → (σ1 x).isSome) :
    StoreExtendsWith (· ∈ E) (projectStore σ σ1) (projectStore τ τ1) := by
  refine ⟨storeAgreement_iff.2 fun y => ?_, fun y hy => ?_⟩
  · simp only [projectStore]
    cases hs : (σ y).isSome
    · exact .inr rfl
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
      have ht : (τ y).isSome = Bool.true := by
        rw [storeAgreement_supplies_mono_premise _ _ hext.1 y w hw]; rfl
      simp only [ht, ite_true]
      exact storeAgreement_iff.1 hext1.1 y
  · simp only [projectStore] at hy ⊢
    split at hy
    · rename_i ht
      cases hs : (σ y).isSome
      · exact .inr ((hext.2 y ht).resolve_left (by simp [hs]))
      · exact .inl (by simp [hdom y hs])
    · cases hy

/-- The outcomes have the same kind and label, the second's store extending the first's with
    variables in `E`. -/
private def OExt (E : List P.Ident) : Outcome P → Outcome P → Prop
  | .normal σ, .normal τ => StoreExtendsWith (· ∈ E) σ τ
  | .exit l σ, .exit l' τ => l' = l ∧ StoreExtendsWith (· ∈ E) σ τ
  | _, _ => False

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Leaving an `ite` branch keeps outcome extension. -/
private theorem OExt.proj {E E' : List P.Ident} {σ τ : SemanticStore P} {o o' : Outcome P}
    (hext : StoreExtendsWith (· ∈ E) σ τ) (h : OExt E' o o')
    (hdom : ∀ x, (σ x).isSome → (o.store x).isSome) : OExt E (o.proj σ) (o'.proj τ) := by
  cases o <;> cases o' <;> simp only [OExt, Outcome.proj, Outcome.store] at h hdom ⊢
  · exact ext_proj hext h hdom
  · exact ⟨h.1, ext_proj hext h.2 hdom⟩

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Leaving a block keeps outcome extension. -/
private theorem OExt.block {E E' : List P.Ident} {σ τ : SemanticStore P} {o o' : Outcome P}
    (l : String) (hext : StoreExtendsWith (· ∈ E) σ τ) (h : OExt E' o o')
    (hdom : ∀ x, (σ x).isSome → (o.store x).isSome) : OExt E (o.block l σ) (o'.block l τ) := by
  rcases o with σ1 | ⟨l1, σ1⟩ <;> rcases o' with τ1 | ⟨l2, τ1⟩ <;>
    simp only [OExt, Outcome.block, Outcome.store] at h hdom ⊢
  · exact ext_proj hext h hdom
  · obtain ⟨rfl, h⟩ := h
    by_cases hl : l2 = l
    · simp only [hl, ite_true]; exact ext_proj hext h hdom
    · simp only [hl, ite_false]; exact ⟨trivial, ext_proj hext h hdom⟩

/-! ## Commands -/

omit [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- **A command step, replayed in a store extending its store** with variables none of whose
    the command mentions: a step of the same command to a store so extending the source's, its
    events those of the source with their conditions captured in the extending store. -/
private theorem cmd_sim (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    {E : List P.Ident} {c : Cmd P} {σ σ1 τ : SemanticStore P} {evs : List (Event P)}
    (h : EvalE F σ (.cmd c) σ1 evs) (hext : StoreExtendsWith (· ∈ E) σ τ)
    (hT : WellFormedStore σ F) (hT' : WellFormedStore τ F)
    (hid : ∀ x ∈ Stmt.idents (.cmd (.cmd c) : PStmt P), x ∉ E) :
    ∃ τ1 evs', EvalE F τ (.cmd c) τ1 evs' ∧ StoreExtendsWith (· ∈ E) σ1 τ1 ∧
      ∀ B, Ins F B evs evs' := by
  change EvalCmdE P F σ c σ1 evs at h
  have hev : ∀ e, (∀ x ∈ HasFvars.getFvars e, x ∈ Stmt.idents (.cmd (.cmd c) : PStmt P)) →
      P.eval F τ e = P.eval F σ e := fun e he =>
    ext_eval hcong hext hT hT' fun x hx => hid x (he x hx)
  -- A variable the command mentions has the same value in both stores.
  have hag : ∀ x ∈ Stmt.idents (.cmd (.cmd c) : PStmt P), τ x = σ x :=
    fun x hx => ext_agree hext (hid x hx)
  have hsv : ∀ (a : EventArg P), a.factory = F → a.store = σ →
      (∀ x ∈ HasFvars.getFvars a.expr, x ∈ Stmt.idents (.cmd (.cmd c) : PStmt P)) →
      EventArg.SameValue (· = F) a { a with store := τ } := by
    rintro ⟨f, s, l, e, md⟩ hf hs he
    simp only at hf hs he
    subst hf hs
    exact ⟨rfl, rfl, rfl, hev e he⟩
  have hone : ∀ (e e' : Event P), Event.SameValue (· = F) e e' → ∀ B, Ins F B [e] [e'] :=
    fun _ _ h _ => .keep h .nil
  cases h with
  | eval_init he hinit hty hwf =>
    rename_i e v x ty md
    obtain ⟨h0, h1, hfr⟩ := hinit
    obtain ⟨hU1, hU2⟩ := update_facts τ x v
    have hx : τ x = none := (hag x (by simp [Stmt.idents])).trans h0
    exact ⟨_, [], .eval_init ((hev e fun y hy => by simp [Stmt.idents, hy]).trans he)
      (.init hx hU1 hU2) hty hwf, ext_update hext h1 hU1 hfr hU2, fun _ => .nil⟩
  | eval_init_unconstrained hinit hty hwf =>
    rename_i x v ty md
    obtain ⟨h0, h1, hfr⟩ := hinit
    obtain ⟨hU1, hU2⟩ := update_facts τ x v
    have hx : τ x = none := (hag x (by simp [Stmt.idents])).trans h0
    exact ⟨_, [], .eval_init_unconstrained (.init hx hU1 hU2) hty hwf,
      ext_update hext h1 hU1 hfr hU2, fun _ => .nil⟩
  | eval_set he hup hst hwf =>
    rename_i e v x md
    obtain ⟨h0, h1, hfr⟩ := hup
    obtain ⟨prev, ty, hprev, hpty, hvty⟩ := hst
    obtain ⟨hU1, hU2⟩ := update_facts τ x v
    have hx : τ x = σ x := hag x (by simp [Stmt.idents])
    exact ⟨_, [], .eval_set ((hev e fun y hy => by simp [Stmt.idents, hy]).trans he)
      (.update (hx.trans h0) hU1 hU2) ⟨prev, ty, hx.trans hprev, hpty, hvty⟩ hwf,
      ext_update hext h1 hU1 hfr hU2, fun _ => .nil⟩
  | eval_set_nondet hup hst hwf =>
    rename_i x v md
    obtain ⟨h0, h1, hfr⟩ := hup
    obtain ⟨prev, ty, hprev, hpty, hvty⟩ := hst
    obtain ⟨hU1, hU2⟩ := update_facts τ x v
    have hx : τ x = σ x := hag x (by simp [Stmt.idents])
    exact ⟨_, [], .eval_set_nondet (.update (hx.trans h0) hU1 hU2)
      ⟨prev, ty, hx.trans hprev, hpty, hvty⟩ hwf, ext_update hext h1 hU1 hfr hU2, fun _ => .nil⟩
  | eval_assert =>
    exact ⟨τ, _, .eval_assert, hext, hone _ _
      ⟨rfl, rfl, hsv _ rfl rfl fun y hy => by simpa [Stmt.idents] using hy⟩⟩
  | eval_assume =>
    exact ⟨τ, _, .eval_assume, hext, hone _ _
      ⟨rfl, rfl, hsv _ rfl rfl fun y hy => by simpa [Stmt.idents] using hy⟩⟩
  | eval_cover =>
    exact ⟨τ, _, .eval_cover, hext, hone _ _
      ⟨rfl, rfl, hsv _ rfl rfl fun y hy => by simpa [Stmt.idents] using hy⟩⟩

/-! ## The inserted commands -/

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- A list of assertions runs from `τ` to `τ`, emitting their conditions captured in `τ`. -/
private theorem asserts_run {α : Type} (τ : SemanticStore P)
    (f : Nat → α → String × P.Expr × MetaData P) :
    ∀ (L : List α), BRun F (L.mapIdx fun i a =>
        Stmt.cmd (CmdExt.cmd (Cmd.assert (f i a).1 (f i a).2.1 (f i a).2.2)))
      τ (L.mapIdx fun i a => Event.assert ⟨F, τ, (f i a).1, (f i a).2.1, (f i a).2.2⟩)
      (.normal τ)
  | [] => .nil
  | a :: L => by
    simp only [List.mapIdx_cons]
    exact .cons_normal (evs1 := [_]) (.cmd .eval_assert)
      (asserts_run τ (fun i => f (i + 1)) L)

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- A list of assumptions runs from `τ` to `τ`, emitting their conditions captured in `τ`. -/
private theorem assumes_run {α : Type} (τ : SemanticStore P)
    (f : Nat → α → String × P.Expr × MetaData P) :
    ∀ (L : List α), BRun F (L.mapIdx fun i a =>
        Stmt.cmd (CmdExt.cmd (Cmd.assume (f i a).1 (f i a).2.1 (f i a).2.2)))
      τ (L.mapIdx fun i a => Event.assume ⟨F, τ, (f i a).1, (f i a).2.1, (f i a).2.2⟩)
      (.normal τ)
  | [] => .nil
  | a :: L => by
    simp only [List.mapIdx_cons]
    exact .cons_normal (evs1 := [_]) (.cmd .eval_assume)
      (assumes_run τ (fun i => f (i + 1)) L)

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- Assertions inserted before related traces keep them related. -/
private theorem ins_asserts {B t t' : Trace P} :
    ∀ {ins : Trace P}, (∀ e ∈ ins, ∃ a, e = .assert a) → Ins F (B ++ ins) t t' →
      Ins F B t (ins ++ t')
  | [], _, h => by simpa using h
  | e :: ins, hins, h => by
    obtain ⟨a, rfl⟩ := hins e List.mem_cons_self
    exact .assert (ins_asserts (fun e he => hins e (List.mem_cons_of_mem _ he))
      (by simpa using h))

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- Assumptions inserted before related traces, each of the condition and value of a checking
    assertion before them, keep them related. -/
private theorem ins_checkedAssumes {B t t' : Trace P} :
    ∀ {ins : Trace P}, (∀ e ∈ ins, ∃ a c, e = .assume a ∧ Event.assert c ∈ B ∧ InvCheck c ∧
      EventArg.SameValue (· = F) c a) → Ins F (B ++ ins) t t' → Ins F B t (ins ++ t')
  | [], _, h => by simpa using h
  | e :: ins, hins, h => by
    obtain ⟨a, c, rfl, hc, hC, hs⟩ := hins e List.mem_cons_self
    exact .assumeChecked hc hC hs (ins_checkedAssumes (fun e he => by
        obtain ⟨a, c, h1, h2, h3, h4⟩ := hins e (List.mem_cons_of_mem _ he)
        exact ⟨a, c, h1, List.mem_append_left _ h2, h3, h4⟩)
      (by simpa using h))

/-! ## What the simulation assumes -/

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- The measure snapshot variables of a loop, and variables in `E`, satisfy `Res` when every
    measure snapshot variable and every variable in `E` does. -/
private theorem res_measureVars_append {Res : P.Ident → Prop} {E : List P.Ident} {n : String}
    {m : Option P.Expr} (hres : ∀ k, Res (measureIdent (P := P) k)) (hE : ∀ x ∈ E, Res x) :
    ∀ x ∈ measureVars n m ++ E, Res x := fun x hx => by
  rcases List.mem_append.1 hx with hx | hx
  · cases m with
    | none => cases hx
    | some _ => rw [List.mem_singleton.1 hx]; exact hres n
  · exact hE x hx


/-- What the simulation of the statement list `ss` from the source store `σ` and the target
    store `τ` assumes: `τ` extends `σ` with variables in `E`, which satisfy `Res`, as no variable
    of `σ` or of `ss` does; both stores hold values; `ss` is def-use well formed from `σ`; the
    free-variable annotations of `ss` agree with a typing of `σ`; and the measures of `ss`
    evaluate to integers. -/
private structure Inv (F : P.Factory) (Res : P.Ident → Prop) (df : P.Ident → Bool)
    (E : List P.Ident) (ss : PStmts P) (σ τ : SemanticStore P) : Prop where
  ext : StoreExtendsWith (· ∈ E) σ τ
  srcWF : WellFormedStore σ F
  tgtWF : WellFormedStore τ F
  resE : ∀ x ∈ E, Res x
  srcRes : ∀ x, (σ x).isSome → ¬ Res x
  idents : ∀ x ∈ Block.idents ss, ¬ Res x
  defUse : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = Bool.true
  typing : ∃ Γ, StoreHasTyping F σ Γ ∧ Block.fvarTypesWellAnnotated Γ ss
  meas : ∀ m ∈ Block.measures ss, MeasureEvaluates F m

/-- `Inv` for one statement. -/
private structure InvS (F : P.Factory) (Res : P.Ident → Prop) (df : P.Ident → Bool)
    (E : List P.Ident) (s : PStmt P) (σ τ : SemanticStore P) : Prop where
  ext : StoreExtendsWith (· ∈ E) σ τ
  srcWF : WellFormedStore σ F
  tgtWF : WellFormedStore τ F
  resE : ∀ x ∈ E, Res x
  srcRes : ∀ x, (σ x).isSome → ¬ Res x
  idents : ∀ x ∈ Stmt.idents s, ¬ Res x
  defUse : Stmt.defUseWellFormed (fun x => (σ x).isSome) df s = Bool.true
  typing : ∃ Γ, StoreHasTyping F σ Γ ∧ Stmt.fvarTypesWellAnnotated Γ s
  meas : ∀ m ∈ Stmt.measures s, MeasureEvaluates F m

variable {Res : P.Ident → Prop} {df : P.Ident → Bool}

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- No variable of the extension is one the source mentions. -/
private theorem InvS.notE {E : List P.Ident} {s : PStmt P} {σ τ : SemanticStore P}
    (h : InvS F Res df E s σ τ) : ∀ x ∈ Stmt.idents s, x ∉ E :=
  fun x hx hE => h.idents x hx (h.resE x hE)

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of a list give those of its first statement. -/
private theorem Inv.head {E : List P.Ident} {s : PStmt P} {rest : PStmts P}
    {σ τ : SemanticStore P} (h : Inv F Res df E (s :: rest) σ τ) : InvS F Res df E s σ τ := by
  have hdu := h.defUse
  simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨Γ, hΓ, hw⟩ := h.typing
  exact ⟨h.ext, h.srcWF, h.tgtWF, h.resE, h.srcRes,
    fun x hx => h.idents x (by simp [Block.idents, hx]), hdu.1, ⟨Γ, hΓ, hw.1⟩,
    fun m hm => h.meas m (by simp [Block.measures, hm])⟩

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] in
/-- Values typed alike with those of a store conforming to `Γ`, in a store defining its
    variables, conform to `Γ`. -/
private theorem storeHasTyping_of_typeAgree {σ σ' : SemanticStore P} {Γ : VarTyping P}
    (hΓ : StoreHasTyping F σ Γ) (hdom : ∀ x, (σ x).isSome → (σ' x).isSome)
    (hTA : TypeAgree F σ σ') : StoreHasTyping F σ' Γ := by
  intro x ty hx
  obtain ⟨p, hp, hpt⟩ := hΓ x ty hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hdom x (by simp [hp]))
  obtain ⟨ty', hp', hv'⟩ := hTA x p v hp hv
  exact ⟨v, hv, LawfulHasVal.valueOfTy_congr F p v ty ty' hpt hp' hv'⟩

omit [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] in
/-- A statement ending normally from a value-valued store conforming to `Γ` ends in a store
    conforming to `Γ` extended by the declared types of its top-level definitions. -/
private theorem brunS_storeHasTyping {s : PStmt P} {σ σ1 : SemanticStore P}
    {evs : List (Event P)} {Γ : VarTyping P} (h : BRunS F s σ evs (.normal σ1))
    (hT : WellFormedStore σ F) (hΓ : StoreHasTyping F σ Γ) :
    StoreHasTyping F σ1 (Γ.extend (Stmt.typedDefinedVars s)) := by
  have hnc : StoreHasTyping F σ1 Γ := storeHasTyping_of_typeAgree hΓ
    (fun x hx => by rw [brunS_normal_isSome h x, hx]; rfl) (brunS_typed h hT).2
  cases s with
  | cmd c =>
    cases h with
    | cmd hE =>
      cases c with
      | call => exact hE.elim
      | cmd c =>
        change EvalCmdE P F σ c σ1 evs at hE
        cases c with
        | init x ty e md =>
          have hi := EvalCmdE.init_storeHasTyping hE hΓ
          intro y ty' hy
          apply hi y ty'
          by_cases hxy : y = x
          · subst hxy
            simpa [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
              CmdExt.typedDefinedVars, Cmd.typedDefinedVars, VarTyping.extend] using hy
          · simpa [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
              CmdExt.typedDefinedVars, Cmd.typedDefinedVars, VarTyping.extend, hxy,
              Ne.symm hxy] using hy
        | set | assert | assume | cover =>
          exact EvalCmdE.preserves_storeHasTyping hE (by intros; simp) hΓ
  | _ => exact hnc

omit [HasIdent P] [HasIntOps P] in
/-- The assumptions of a list whose first statement ends normally give those of the rest, at the
    stores the first statement ends with. -/
private theorem Inv.tail {E : List P.Ident} {s : PStmt P} {rest : PStmts P}
    {σ τ σ1 τ1 : SemanticStore P} {evs : List (Event P)} (h : Inv F Res df E (s :: rest) σ τ)
    (h1 : BRunS F s σ evs (.normal σ1)) (hext : StoreExtendsWith (· ∈ E) σ1 τ1)
    (hT1 : WellFormedStore τ1 F) : Inv F Res df E rest σ1 τ1 := by
  have hdu := h.defUse
  simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨Γ, hΓ, hw⟩ := h.typing
  have hstore : (fun x => (σ1 x).isSome) =
      (fun x => (σ x).isSome || decide (x ∈ Stmt.definedVars s true)) :=
    funext (brunS_normal_isSome h1)
  refine ⟨hext, (brunS_typed h1 h.srcWF).1, hT1, h.resE, fun x hx => ?_,
    fun x hx => h.idents x (by simp [Block.idents, hx]), hstore ▸ hdu.2,
    ⟨_, brunS_storeHasTyping h1 h.srcWF hΓ, hw.2⟩,
    fun m hm => h.meas m (by simp [Block.measures, hm])⟩
  rw [brunS_normal_isSome h1 x] at hx
  rcases Bool.or_eq_true_iff.1 hx with hx | hx
  · exact h.srcRes x hx
  · exact h.idents x (by
      simp only [Block.idents, List.mem_append]
      exact .inl (Stmt.definedVars_subset_idents s true x (by simpa using hx)))

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of a block give those of its body. -/
private theorem InvS.block {E : List P.Ident} {l : String} {bss : PStmts P}
    {md : MetaData P} {σ τ : SemanticStore P} (h : InvS F Res df E (.block l bss md) σ τ) :
    Inv F Res df E bss σ τ :=
  ⟨h.ext, h.srcWF, h.tgtWF, h.resE, h.srcRes, fun x hx => h.idents x (by simpa [Stmt.idents]),
    by simpa [Stmt.defUseWellFormed] using h.defUse,
    by obtain ⟨Γ, hΓ, hw⟩ := h.typing; exact ⟨Γ, hΓ, by simpa [Stmt.fvarTypesWellAnnotated]⟩,
    fun m hm => h.meas m (by simpa [Stmt.measures])⟩

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of an `ite` give those of its first branch. -/
private theorem InvS.ite_then {E : List P.Ident} {c : ExprOrNondet P} {tss ess : PStmts P}
    {md : MetaData P} {σ τ : SemanticStore P} (h : InvS F Res df E (.ite c tss ess md) σ τ) :
    Inv F Res df E tss σ τ := by
  have hdu := h.defUse
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨Γ, hΓ, hw⟩ := h.typing
  simp only [Stmt.fvarTypesWellAnnotated] at hw
  exact ⟨h.ext, h.srcWF, h.tgtWF, h.resE, h.srcRes,
    fun x hx => h.idents x (by simp [Stmt.idents, hx]), hdu.1.2, ⟨Γ, hΓ, hw.2.1⟩,
    fun m hm => h.meas m (by simp [Stmt.measures, hm])⟩

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of an `ite` give those of its second branch. -/
private theorem InvS.ite_else {E : List P.Ident} {c : ExprOrNondet P} {tss ess : PStmts P}
    {md : MetaData P} {σ τ : SemanticStore P} (h : InvS F Res df E (.ite c tss ess md) σ τ) :
    Inv F Res df E ess σ τ := by
  have hdu := h.defUse
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨Γ, hΓ, hw⟩ := h.typing
  simp only [Stmt.fvarTypesWellAnnotated] at hw
  exact ⟨h.ext, h.srcWF, h.tgtWF, h.resE, h.srcRes,
    fun x hx => h.idents x (by simp [Stmt.idents, hx]), hdu.2, ⟨Γ, hΓ, hw.2.2⟩,
    fun m hm => h.meas m (by simp [Stmt.measures, hm])⟩

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of a loop give those of its body, from a target store extending the source
    store with variables in `E'`, satisfying `Res`. -/
private theorem InvS.loop_body {E E' : List P.Ident} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P}
    {σ τ τ' : SemanticStore P} (h : InvS F Res df E (.loop g m inv body md) σ τ)
    (hext : StoreExtendsWith (· ∈ E') σ τ') (hT' : WellFormedStore τ' F)
    (hE' : ∀ x ∈ E', Res x) : Inv F Res df E' body σ τ' := by
  have hdu := h.defUse
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨Γ, hΓ, hw⟩ := h.typing
  simp only [Stmt.fvarTypesWellAnnotated] at hw
  exact ⟨hext, h.srcWF, hT', hE', h.srcRes,
    fun x hx => h.idents x (by simp [Stmt.idents, hx]), hdu.2, ⟨Γ, hΓ, hw.2.2.2⟩,
    fun m hm => h.meas m (by simp [Stmt.measures, hm])⟩

omit [HasIdent P] [HasIntOps P] in
/-- The assumptions of a loop hold again at the start of the next iteration: the stores of the
    end of an iteration, projected on those of its start. -/
private theorem InvS.loop_next {E E' : List P.Ident} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P}
    {σ τ σ1 τ1 : SemanticStore P} {evs : List (Event P)}
    (h : InvS F Res df E (.loop g m inv body md) σ τ) (h1 : BRun F body σ evs (.normal σ1))
    (hext : StoreExtendsWith (· ∈ E') σ1 τ1) (hT1 : WellFormedStore τ1 F) :
    InvS F Res df E (.loop g m inv body md) (projectStore σ σ1) (projectStore τ τ1) := by
  have hdom := brun_dom h1
  have hTy := brun_typed h1 h.srcWF
  simp only [Outcome.store] at hdom hTy
  have hsame : ∀ x, ((projectStore σ σ1) x).isSome = (σ x).isSome := fun x => by
    cases hs : (σ x).isSome
    · simp [projectStore, hs]
    · simp [projectStore, hs, hdom x hs]
  obtain ⟨Γ, hΓ, hw⟩ := h.typing
  refine ⟨ext_proj h.ext hext hdom, WellFormedStore.proj hTy.1, WellFormedStore.proj hT1,
    h.resE, fun x hx => h.srcRes x (by rwa [hsame x] at hx), h.idents,
    by rw [show (fun x => ((projectStore σ σ1) x).isSome) = (fun x => (σ x).isSome) from
      funext hsame]; exact h.defUse,
    ⟨Γ, storeHasTyping_of_typeAgree hΓ (fun x hx => by rwa [hsame x]) hTy.2.proj, hw⟩,
    h.meas⟩

/-! ## The checks of a loop -/

/-- Each invariant in `inv` has the value it has in `τ` in the condition of an assertion of it
    among the events `B` (`InvCheck`), captured under `F`: the assumption of the invariants
    in `τ` follows a checking assertion of them. -/
private def Justified (F : P.Factory) (inv : List (String × P.Expr)) (B : Trace P)
    (τ : SemanticStore P) : Prop :=
  ∀ p ∈ inv, ∃ c, Event.assert c ∈ B ∧ InvCheck c ∧ c.factory = F ∧ c.expr = p.2 ∧
    P.eval F c.store p.2 = P.eval F τ p.2

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Justification holds after more events. -/
private theorem Justified.append {inv : List (String × P.Expr)} {B : Trace P}
    {τ : SemanticStore P} (h : Justified F inv B τ) (X : Trace P) :
    Justified F inv (B ++ X) τ := fun p hp =>
  have ⟨c, hc, h⟩ := h p hp; ⟨c, List.mem_append_left _ hc, h⟩

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Checking assertions of the invariants `inv`, captured in `τ1`, justify their assumption in a
    store `τ2` where they have the same values. -/
private theorem justified_asserts {inv : List (String × P.Expr)} (B : Trace P)
    {τ1 τ2 : SemanticStore P} (lab : Nat → String × P.Expr → String)
    (mdf : Nat → MetaData P) (hlab : ∀ i a, invCheckLabel (lab i a) = Bool.true)
    (heq : ∀ p ∈ inv, P.eval F τ1 p.2 = P.eval F τ2 p.2) :
    Justified F inv (B ++ inv.mapIdx fun i a => Event.assert ⟨F, τ1, lab i a, a.2, mdf i⟩) τ2 :=
  fun p hp => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact ⟨_, List.mem_append_right _ (List.mem_mapIdx.2 ⟨i, hi, rfl⟩), hlab _ _, rfl, rfl,
      heq _ hp⟩

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- Assumptions of the invariants `inv` captured in `τ`, inserted before related traces, keep
    them related when justified. -/
private theorem ins_invAssumes {inv : List (String × P.Expr)} {B t t' : Trace P}
    {τ : SemanticStore P} (lab : Nat → String × P.Expr → String) (mdf : Nat → MetaData P)
    (hJ : Justified F inv B τ)
    (h : Ins F (B ++ inv.mapIdx fun i a => Event.assume ⟨F, τ, lab i a, a.2, mdf i⟩) t t') :
    Ins F B t ((inv.mapIdx fun i a => Event.assume ⟨F, τ, lab i a, a.2, mdf i⟩) ++ t') := by
  refine ins_checkedAssumes (fun e he => ?_) h
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 he
  obtain ⟨c, hc, hC, hf, hx, hv⟩ := hJ _ (List.getElem_mem hi)
  exact ⟨_, c, rfl, hc, hC, ⟨hf ▸ rfl, hf.symm, hx.symm, by simp only [hf, hx, hv]⟩⟩

/-- The label of the assertion of an invariant before loop `n` is a checking one. -/
private theorem invCheckLabel_entry (n : String) (i : Nat) (lbl : String) :
    invCheckLabel (entryAssertLabel n i lbl) = Bool.true := by
  simp only [invCheckLabel, entryAssertLabel, Bool.or_eq_true]
  refine .inl ?_
  rw [String.startsWith_string_iff]
  simp only [String.toList_append, toString]
  simp [List.append_assoc]

/-- The label of the assertion of an invariant at the end of an iteration of loop `n` is a
    checking one. -/
private theorem invCheckLabel_maintain (n : String) (i : Nat) (lbl : String) :
    invCheckLabel (maintainAssertLabel n i lbl) = Bool.true := by
  simp only [invCheckLabel, maintainAssertLabel, Bool.or_eq_true]
  refine .inr ?_
  rw [String.startsWith_string_iff]
  simp only [String.toList_append, toString]
  simp [List.append_assoc]

/-! ## Runs of the inserted statements -/

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- The assertions of the invariants before loop `n` run from `τ` to `τ`. -/
private theorem entryAsserts_run (n : String) (inv : List (String × P.Expr)) (md : MetaData P)
    (τ : SemanticStore P) :
    BRun F (entryAsserts n inv md) τ
      (inv.mapIdx fun i a => Event.assert ⟨F, τ, entryAssertLabel n i a.1, a.2, md.invariantMd i⟩)
      (.normal τ) :=
  asserts_run τ (fun i a => (entryAssertLabel n i a.1, a.2, md.invariantMd i)) inv

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of the invariants before loop `n` run from `τ` to `τ`. -/
private theorem entryAssumes_run (n : String) (inv : List (String × P.Expr)) (md : MetaData P)
    (τ : SemanticStore P) :
    BRun F (entryAssumes n inv md) τ
      (inv.mapIdx fun i a => Event.assume ⟨F, τ, entryAssumeLabel n i a.1, a.2, md.invariantMd i⟩)
      (.normal τ) :=
  assumes_run τ (fun i a => (entryAssumeLabel n i a.1, a.2, md.invariantMd i)) inv

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of the invariants at the start of an iteration of loop `n` run from `τ` to
    `τ`. -/
private theorem midAssumes_run (n : String) (inv : List (String × P.Expr)) (md : MetaData P)
    (τ : SemanticStore P) :
    BRun F (midAssumes n inv md) τ
      (inv.mapIdx fun i a => Event.assume ⟨F, τ, midAssumeLabel n i a.1, a.2, md.invariantMd i⟩)
      (.normal τ) :=
  assumes_run τ (fun i a => (midAssumeLabel n i a.1, a.2, md.invariantMd i)) inv

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- The assertions of the invariants at the end of an iteration of loop `n` run from `τ` to
    `τ`. -/
private theorem maintainAsserts_run (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) (τ : SemanticStore P) :
    BRun F (maintainAsserts n inv md) τ
      (inv.mapIdx fun i a =>
        Event.assert ⟨F, τ, maintainAssertLabel n i a.1, a.2, md.invariantMd i⟩)
      (.normal τ) :=
  asserts_run τ (fun i a => (maintainAssertLabel n i a.1, a.2, md.invariantMd i)) inv

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- A list built by `List.mapIdx` from assertions has only assertions. -/
private theorem mapIdx_asserts {α : Type} (L : List α) (f : Nat → α → EventArg P) :
    ∀ e ∈ L.mapIdx (fun i a => Event.assert (f i a)), ∃ c, e = .assert c := fun _ he => by
  obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.1 he
  exact ⟨_, rfl⟩

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- The checks after loop `n` run from a store where the loop stops: they emit the assumptions of
    the invariants and, for a deterministic guard, of its negation, which evaluates to `true`,
    and, inserted after justified events, keep related traces related. -/
private theorem exitAssumes_run (hbool : WellFormedSemanticEvalBool (P := P) F) (n : String)
    {g : ExprOrNondet P} (inv : List (String × P.Expr)) (md : MetaData P) {τ : SemanticStore P}
    (hg : guardExits F τ g) :
    ∃ evs, BRun F (exitAssumes n g inv md) τ evs (.normal τ) ∧
      ∀ {B t t' : Trace P}, Justified F inv B τ → Ins F (B ++ evs) t t' →
        Ins F B t (evs ++ t') := by
  have hinv := assumes_run (F := F) τ
    (fun i a => (exitAssumeLabel n i a.1, a.2, md.invariantMd i)) inv
  cases g with
  | nondet =>
    refine ⟨_, by simp only [exitAssumes, List.append_nil]; exact hinv, fun hJ h => ?_⟩
    exact ins_invAssumes (fun i a => exitAssumeLabel n i a.1) md.invariantMd hJ h
  | det g =>
    have htt : P.eval F τ (HasBoolOps.not g) = some (HasBool.ttVal F) := (hbool τ g).2.1 hg
    have hgr : BRun F [Stmt.cmd (CmdExt.cmd (Cmd.assume
        s!"{Core.insertLoopInvAssumePrefix}exit_not_guard_{n}" (HasBoolOps.not g) md))] τ
        ([.assume ⟨F, τ, s!"{Core.insertLoopInvAssumePrefix}exit_not_guard_{n}",
          HasBoolOps.not g, md⟩] ++ []) (.normal τ) := .cons_normal (.cmd .eval_assume) .nil
    refine ⟨_, brun_append hinv hgr, fun hJ h => ?_⟩
    rw [List.append_assoc]
    refine ins_invAssumes (fun i a => exitAssumeLabel n i a.1) md.invariantMd hJ ?_
    exact .assumeTrue rfl htt (by simpa using h)

omit [HasFvar P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- A guard admitting entering at a value-valued store admits it at a value-valued store
    extending it with variables the guard does not read. -/
private theorem guardEnters_ext (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    {E : List P.Ident} {σ τ : SemanticStore P} {g : ExprOrNondet P}
    (hext : StoreExtendsWith (· ∈ E) σ τ) (hT : WellFormedStore σ F)
    (hT' : WellFormedStore τ F) (hg : ∀ x ∈ g.getVars, x ∉ E) (h : guardEnters F σ g) :
    guardEnters F τ g := by
  cases g with
  | nondet => trivial
  | det g =>
    simp only [guardEnters] at h ⊢
    rw [ext_eval hcong hext hT hT' (by simpa [ExprOrNondet.getVars] using hg)]; exact h

omit [HasFvar P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- A guard admitting stopping at a value-valued store admits it at a value-valued store
    extending it with variables the guard does not read. -/
private theorem guardExits_ext (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    {E : List P.Ident} {σ τ : SemanticStore P} {g : ExprOrNondet P}
    (hext : StoreExtendsWith (· ∈ E) σ τ) (hT : WellFormedStore σ F)
    (hT' : WellFormedStore τ F) (hg : ∀ x ∈ g.getVars, x ∉ E) (h : guardExits F σ g) :
    guardExits F τ g := by
  cases g with
  | nondet => trivial
  | det g =>
    simp only [guardExits] at h ⊢
    rw [ext_eval hcong hext hT hT' (by simpa [ExprOrNondet.getVars] using hg)]; exact h

/-- At the start of an iteration of loop `n`, the snapshot of its measure and the assertion that
    it is not negative run from the target store, to one extending the source store with the
    snapshot variable as well. -/
private theorem measurePre_run (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {E : List P.Ident} {n : String}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)} {body : PStmts P}
    {md : MetaData P} {σ τ : SemanticStore P}
    (h : InvS F Res df E (.loop g m inv body md) σ τ) (hfresh : ∀ x ∈ measureVars n m, x ∉ E) :
    ∃ τ' evs, BRun F (measurePre n m md) τ evs (.normal τ') ∧
      StoreExtendsWith (· ∈ measureVars n m ++ E) σ τ' ∧ WellFormedStore τ' F ∧
      ∀ e ∈ evs, ∃ c, e = .assert c := by
  cases m with
  | none => exact ⟨τ, [], .nil, h.ext, h.tgtWF, by simp⟩
  | some D =>
    obtain ⟨Γ, hΓ, hw⟩ := h.typing
    simp only [Stmt.fvarTypesWellAnnotated, Option.map_some, Option.getD_some] at hw
    obtain ⟨v, hv, hvt⟩ := h.meas D (by simp [Stmt.measures]) Γ σ hΓ hw.2.1
    have hevD : P.eval F τ D = P.eval F σ D :=
      ext_eval hcong h.ext h.srcWF h.tgtWF fun x hx => h.notE x (by simp [Stmt.idents, hx])
    have hnone : τ (measureIdent n) = none := by
      cases hτ : τ (measureIdent n) with
      | none => rfl
      | some _ =>
        rcases h.ext.2 (measureIdent n) (by rw [hτ]; rfl) with hs | hs
        · exact absurd (hres n) (h.srcRes _ hs)
        · exact absurd hs (hfresh _ (List.mem_singleton_self _))
    obtain ⟨hU1, hU2⟩ := update_facts τ (measureIdent n) v
    refine ⟨_, _, .cons_normal
      (.cmd (EvalCmdE.eval_init (P := P) (hevD.trans hv) (.init hnone hU1 hU2) hvt hvar))
      (.cons_normal (.cmd (EvalCmdE.eval_assert (P := P))) .nil), ext_init h.ext hnone,
      fun y w hy => ?_, by simp⟩
    by_cases hxy : measureIdent n = y
    · subst hxy; rw [hU1] at hy; cases hy; exact LawfulHasVal.valueOfTy_isVal F v _ hvt
    · rw [hU2 y hxy] at hy; exact h.tgtWF y w hy

omit [HasOps P] [LawfulHasVal P] in
/-- At the end of an iteration of loop `n`, the assertion that its measure decreased runs from
    `τ` to `τ`. -/
private theorem measurePost_run (n : String) (m : Option P.Expr) (md : MetaData P)
    (τ : SemanticStore P) :
    ∃ evs, BRun F (measurePost n m md) τ evs (.normal τ) ∧ ∀ e ∈ evs, ∃ c, e = .assert c := by
  cases m with
  | none => exact ⟨[], .nil, by simp⟩
  | some D => exact ⟨_, .cons_normal (.cmd (EvalCmdE.eval_assert (P := P))) .nil, by simp⟩

/-! ## Replaying a loop -/

/-- A run of the target list `ss'` from `τ` replays a run of the source from a store `τ`
    extends, emitting `evs` and ending with `o`: it ends the same way in a store extending the
    source's with variables in `E`, emitting a trace related to `evs` after any events. -/
private def RunRes (F : P.Factory) (E : List P.Ident) (ss' : PStmts P) (τ : SemanticStore P)
    (evs : List (Event P)) (o : Outcome P) : Prop :=
  ∃ evs' o', BRun F ss' τ evs' o' ∧ OExt E o o' ∧ ∀ B, Ins F B evs evs'

/-- A run of the checked loop `n` from `τ`, the store of the start of an iteration, replays a
    run of the source loop emitting `evs` and ending with `o`, as in `RunRes`, the trace related
    after events justifying the invariants at `τ`, and, when it ends normally, those events and
    its own justifying the invariants where it ends, where the guard admits stopping. -/
private def LoopRes (F : P.Factory) (E : List P.Ident) (n : String) (g : ExprOrNondet P)
    (m : Option P.Expr) (inv : List (String × P.Expr)) (body' : PStmts P) (md : MetaData P)
    (τ : SemanticStore P) (evs : List (Event P)) (o : Outcome P) : Prop :=
  ∃ evs' o', BRunS F (.loop g none [] (loopBody n m inv body' md) md) τ evs' o' ∧ OExt E o o' ∧
    ∀ B, Justified F inv B τ → Ins F B evs evs' ∧
      ∀ τ1, o' = .normal τ1 → Justified F inv (B ++ evs') τ1 ∧ guardExits F τ1 g

omit [LawfulHasVal P] in
/-- **A stopping loop, replayed.** -/
private theorem LoopRes.exit (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    {E : List P.Ident} {n : String} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body body' : PStmts P} {md : MetaData P}
    {σ τ : SemanticStore P} (hg : guardExits F σ g)
    (h : InvS F Res df E (.loop g m inv body md) σ τ) :
    LoopRes F E n g m inv body' md τ [] (.normal σ) := by
  have hgτ := guardExits_ext hcong h.ext h.srcWF h.tgtWF
    (fun x hx => h.notE x (by simp [Stmt.idents, hx])) hg
  exact ⟨[], .normal τ, .loop_exit hgτ, h.ext, fun B hJ =>
    ⟨.nil, fun τ1 h1 => by cases h1; exact ⟨by simpa using hJ, hgτ⟩⟩⟩

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The variables the invariants of a def-use well-formed loop read are defined where the loop
    starts. -/
private theorem InvS.inv_defined {E : List P.Ident} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P} {σ τ : SemanticStore P}
    (h : InvS F Res df E (.loop g m inv body md) σ τ) :
    ∀ p ∈ inv, ∀ y ∈ HasFvars.getFvars p.2, (τ y).isSome := by
  have hdu := h.defUse
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true, List.all_eq_true] at hdu
  intro p hp y hy
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
    (hdu.1.1.2 y (List.mem_flatMap.2 ⟨p, hp, hy⟩))
  rw [storeAgreement_supplies_mono_premise _ _ h.ext.1 y w hw]; rfl

/-- **An iteration of a loop, replayed.**  If the loop runs an iteration from `σ` (where the
    guard admits entering) ending normally at `σ1`, the body's output replays it from every
    target store satisfying the assumptions of the body, and the rest of the loop is replayed
    from every target store satisfying those of the loop at the start of the next iteration,
    then the loop from `σ` is replayed. -/
private theorem LoopRes.iter (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {E : List P.Ident} {n : String}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body body' : PStmts P} {md : MetaData P} {σ τ σ1 : SemanticStore P}
    {evs1 evs2 : List (Event P)} {o : Outcome P}
    (hg : guardEnters F σ g) (h : InvS F Res df E (.loop g m inv body md) σ τ)
    (hfresh : ∀ x ∈ measureVars n m, x ∉ E) (h1 : BRun F body σ evs1 (.normal σ1))
    (hbody : ∀ τ', Inv F Res df (measureVars n m ++ E) body σ τ' →
      RunRes F (measureVars n m ++ E) body' τ' evs1 (.normal σ1))
    (hnext : ∀ τ2, InvS F Res df E (.loop g m inv body md) (projectStore σ σ1) τ2 →
      LoopRes F E n g m inv body' md τ2 evs2 o) :
    LoopRes F E n g m inv body' md τ (evs1 ++ evs2) o := by
  obtain ⟨τ', evsMP, hMP, hext', hT', hMPa⟩ := measurePre_run hvar hcong hres h hfresh
  have hE' := res_measureVars_append (n := n) (m := m) hres h.resE
  obtain ⟨evs1', o1', h1', hO1, hk1⟩ := hbody τ' (h.loop_body hext' hT' hE')
  rcases o1' with τ1 | ⟨_, _⟩ <;> simp only [OExt] at hO1
  have hT1 : WellFormedStore τ1 F := (brun_typed h1' hT').1
  obtain ⟨evsMPost, hMPost, hMPosta⟩ := measurePost_run (F := F) n m md τ1
  have hNB := brun_append (brun_append (brun_append (brun_append
    (midAssumes_run (F := F) n inv md τ) hMP) h1') (maintainAsserts_run (F := F) n inv md τ1))
    hMPost
  obtain ⟨evs2', o', h2', hO2, hk2⟩ := hnext _ (h.loop_next h1 hO1 hT1)
  have hgτ := guardEnters_ext hcong h.ext h.srcWF h.tgtWF
    (fun x hx => h.notE x (by simp [Stmt.idents, hx])) hg
  refine ⟨_, o', .loop_iter hgτ hNB h2', hO2, fun B hJ => ?_⟩
  -- The assertions of the invariants at the end of the iteration justify their assumption at the
  -- start of the next one: their variables are defined in `τ`, so leaving the iteration keeps
  -- their values.
  have hTp : WellFormedStore (projectStore τ τ1) F := WellFormedStore.proj hT1
  have hJ2 := justified_asserts (F := F) (inv := inv)
    ((((B ++ inv.mapIdx fun i a =>
        Event.assume ⟨F, τ, midAssumeLabel n i a.1, a.2, md.invariantMd i⟩) ++ evsMP) ++ evs1'))
    (τ1 := τ1) (τ2 := projectStore τ τ1) (fun i a => maintainAssertLabel n i a.1)
    md.invariantMd (fun _ _ => invCheckLabel_maintain _ _ _) fun p hp =>
      hcong p.2 τ1 _ hT1 hTp fun y hy => by simp [projectStore, h.inv_defined p hp y hy]
  obtain ⟨hk2a, hk2b⟩ := hk2 _ (hJ2.append evsMPost)
  refine ⟨?_, fun τ1' h' => by simpa only [List.append_assoc] using hk2b τ1' h'⟩
  have hins := ins_invAssumes (fun i a => midAssumeLabel n i a.1) md.invariantMd hJ
    (ins_asserts hMPa ((hk1 _).append
      (ins_asserts (mapIdx_asserts inv _) (ins_asserts hMPosta hk2a))))
  simpa only [List.append_assoc] using hins

/-- **A breaking iteration of a loop, replayed.**  If the loop runs an iteration from `σ` (where
    the guard admits entering) exiting, and the body's output replays it from every target store
    satisfying the assumptions of the body, then the loop from `σ` is replayed. -/
private theorem LoopRes.break (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {E : List P.Ident} {n : String}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body body' : PStmts P} {md : MetaData P} {σ τ σ1 : SemanticStore P}
    {evs : List (Event P)} {l : String}
    (hg : guardEnters F σ g) (h : InvS F Res df E (.loop g m inv body md) σ τ)
    (hfresh : ∀ x ∈ measureVars n m, x ∉ E) (h1 : BRun F body σ evs (.exit l σ1))
    (hbody : ∀ τ', Inv F Res df (measureVars n m ++ E) body σ τ' →
      RunRes F (measureVars n m ++ E) body' τ' evs (.exit l σ1)) :
    LoopRes F E n g m inv body' md τ evs (.exit l (projectStore σ σ1)) := by
  obtain ⟨τ', evsMP, hMP, hext', hT', hMPa⟩ := measurePre_run hvar hcong hres h hfresh
  have hE' := res_measureVars_append (n := n) (m := m) hres h.resE
  obtain ⟨evs1', o1', h1', hO1, hk1⟩ := hbody τ' (h.loop_body hext' hT' hE')
  rcases o1' with _ | ⟨l', τ1⟩ <;> simp only [OExt] at hO1
  obtain ⟨rfl, hO1⟩ := hO1
  have hNB : BRun F (loopBody n m inv body' md) τ _ (.exit l' τ1) :=
    brun_append_exit (brun_append_exit (brun_append (brun_append
      (midAssumes_run (F := F) n inv md τ) hMP) h1'))
  have hgτ := guardEnters_ext hcong h.ext h.srcWF h.tgtWF
    (fun x hx => h.notE x (by simp [Stmt.idents, hx])) hg
  have hdom := brun_dom h1
  simp only [Outcome.store] at hdom
  refine ⟨_, _, .loop_break hgτ hNB, ⟨rfl, ext_proj h.ext hO1 hdom⟩, fun B hJ =>
    ⟨?_, fun _ h => by cases h⟩⟩
  have hins := ins_invAssumes (fun i a => midAssumeLabel n i a.1) md.invariantMd hJ
    (ins_asserts hMPa (hk1 _))
  simpa only [List.append_assoc] using hins

omit [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P] [LawfulHasVal P] in
/-- A statement run is a run of the list of it alone. -/
private theorem brun_single {s : PStmt P} {τ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P} (h : BRunS F s τ evs o) : BRun F [s] τ evs o := by
  cases o with
  | normal τ1 => simpa using BRun.cons_normal h .nil
  | exit l τ1 => exact .cons_exit h

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of a checked loop from its start store, with the checks before and after it, is a
    replay of the loop's checked form. -/
private theorem LoopRes.checked (hbool : WellFormedSemanticEvalBool (P := P) F)
    {E : List P.Ident} {n : String} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body' : PStmts P} {md : MetaData P} {τ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}
    (h : LoopRes F E n g m inv body' md τ evs o) :
    RunRes F E (Stmt.invChecked n g m inv body' md) τ evs o := by
  obtain ⟨evs', o', hloop, hO, hk⟩ := h
  have hEA := entryAsserts_run (F := F) n inv md τ
  have hEAs := entryAssumes_run (F := F) n inv md τ
  have hJ0 : ∀ B, Justified F inv (B ++ inv.mapIdx fun i a =>
      Event.assert ⟨F, τ, entryAssertLabel n i a.1, a.2, md.invariantMd i⟩) τ := fun B =>
    justified_asserts B (fun i a => entryAssertLabel n i a.1) md.invariantMd
      (fun _ _ => invCheckLabel_entry _ _ _) fun _ _ => rfl
  rcases o' with τ1 | ⟨l, τ1⟩
  · obtain ⟨evsXA, hXA, hXAk⟩ := exitAssumes_run hbool n inv md
      ((hk _ (hJ0 [])).2 τ1 rfl).2
    refine ⟨_, _, brun_append (brun_append (brun_append hEA hEAs) (brun_single hloop)) hXA, hO,
      fun B => ?_⟩
    have hJ1 := (hJ0 B).append (inv.mapIdx fun i a =>
      Event.assume ⟨F, τ, entryAssumeLabel n i a.1, a.2, md.invariantMd i⟩)
    obtain ⟨hk1, hk2⟩ := hk _ hJ1
    have hX := hXAk (B := _ ++ evs') (hk2 τ1 rfl).1 (t := []) (t' := []) (by simpa using .nil)
    have hins := ins_asserts (mapIdx_asserts inv _)
      (ins_invAssumes (fun i a => entryAssumeLabel n i a.1)
        md.invariantMd (hJ0 B) (by simpa only [List.append_assoc] using hk1.append hX))
    simpa only [List.append_assoc, List.append_nil] using hins
  · refine ⟨_, _, brun_append_exit (brun_append (brun_append hEA hEAs) (.cons_exit hloop)), hO,
      fun B => ?_⟩
    have hJ1 := (hJ0 B).append (inv.mapIdx fun i a =>
      Event.assume ⟨F, τ, entryAssumeLabel n i a.1, a.2, md.invariantMd i⟩)
    have hins := ins_asserts (mapIdx_asserts inv _)
      (ins_invAssumes (fun i a => entryAssumeLabel n i a.1)
        md.invariantMd (hJ0 B) (by simpa only [List.append_assoc] using (hk _ hJ1).1))
    simpa only [List.append_assoc] using hins

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of a loop without invariants and measure is a replay of the loop alone. -/
private theorem LoopRes.bare {E : List P.Ident} {n : String} {g : ExprOrNondet P}
    {body' : PStmts P} {md : MetaData P} {τ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P} (h : LoopRes F E n g none [] body' md τ evs o) :
    RunRes F E [.loop g none [] body' md] τ evs o := by
  have heq : loopBody (C := CmdExt P) n none [] body' md = body' := by
    simp [loopBody, midAssumes, measurePre, maintainAsserts, measurePost]
  obtain ⟨evs', o', hloop, hO, hk⟩ := h
  rw [heq] at hloop
  exact ⟨evs', o', brun_single hloop, hO, fun B => (hk B fun _ hp => by cases hp).1⟩

/-! ## The simulation of runs -/

omit [HasOps P] [LawfulHasVal P] in
/-- A loop and the statements with its checks inserted: a loop without invariants and measure
    and its body with checks inserted, or the checked form of the loop.  For the first, the
    facts about the measure variables hold of any loop number `n`, since there is no measure;
    the equations on the measure and invariants come last, so that a proof can use them after
    the recursive calls, which keep the sub-derivations unchanged. -/
private theorem StmtRel.loop_cases {E : List P.Ident} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P} {ss₁ : PStmts P}
    (h : StmtRel E (.loop g m inv body md) ss₁) :
    (∃ n body', (∀ x ∈ measureVars n m, x ∉ E) ∧ BlockRel (measureVars n m ++ E) body body' ∧
      m = none ∧ inv = [] ∧ ss₁ = [.loop g none [] body' md]) ∨
    ∃ n body', (∀ x ∈ measureVars n m, x ∉ E) ∧ BlockRel (measureVars n m ++ E) body body' ∧
      ss₁ = Stmt.invChecked n g m inv body' md := by
  cases h with
  | loopBare hb => exact .inl ⟨"", _, by simp [measureVars], hb, rfl, rfl, rfl⟩
  | loop n hf hb => exact .inr ⟨n, _, hf, hb, rfl⟩

mutual
/-- **A run of a list, replayed by the list with its loops' checks inserted** from a target
    store satisfying the assumptions of the simulation (`RunRes`). -/
private theorem run_sim' (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRun F ss σ evs o → ∀ {E : List P.Ident} {ss' : PStmts P} {τ : SemanticStore P},
    BlockRel E ss ss' → Inv F Res df E ss σ τ → RunRes F E ss' τ evs o
  | _, _, _, _, .nil, _, _, τ, hr, h => by
    cases hr
    exact ⟨[], .normal τ, .nil, h.ext, fun _ => .nil⟩
  | _, _, _, _, .cons_normal h1 h2, _, _, _, hr, h => by
    cases hr with
    | cons hs hr =>
      obtain ⟨evs1', o1', h1', hO1, hk1⟩ := runS_sim hvar hbool hcong hres h1 hs h.head
      rcases o1' with τ1 | ⟨_, _⟩ <;> simp only [OExt] at hO1
      obtain ⟨evs2', o', h2', hO, hk2⟩ := run_sim' hvar hbool hcong hres h2 hr
        (h.tail h1 hO1 (brun_typed h1' h.tgtWF).1)
      exact ⟨_, o', brun_append h1' h2', hO, fun B => (hk1 B).append (hk2 _)⟩
  | _, _, _, _, .cons_exit h1, _, _, _, hr, h => by
    cases hr with
    | cons hs hr =>
      obtain ⟨evs1', o1', h1', hO1, hk1⟩ := runS_sim hvar hbool hcong hres h1 hs h.head
      rcases o1' with _ | ⟨l, τ1⟩ <;> simp only [OExt] at hO1
      obtain ⟨rfl, hO1⟩ := hO1
      exact ⟨evs1', _, brun_append_exit h1', ⟨rfl, hO1⟩, hk1⟩

/-- **A run of a statement, replayed by the statements with its loops' checks inserted**, as
    `run_sim'`. -/
private theorem runS_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {E : List P.Ident} {ss₁ : PStmts P} {τ : SemanticStore P},
    StmtRel E s ss₁ → InvS F Res df E s σ τ → RunRes F E ss₁ τ evs o
  | _, _, _, _, .cmd (c := .cmd c) hE, _, _, _, hr, h => by
    cases hr
    obtain ⟨τ1, evs', hE', hext, hk⟩ := cmd_sim hcong hE h.ext h.srcWF h.tgtWF h.notE
    exact ⟨evs', .normal τ1, brun_single (.cmd hE'), hext, hk⟩
  | _, _, _, _, .cmd (c := .call _ _ _) hE, _, _, _, _, _ => hE.elim
  | _, _, _, _, .ite_true hc hb, _, _, _, hr, h => by
    cases hr with
    | ite ht _ =>
      obtain ⟨evs', o', hb', hO, hk⟩ := run_sim' hvar hbool hcong hres hb ht h.ite_then
      have hcτ := (ext_eval hcong h.ext h.srcWF h.tgtWF fun x hx =>
        h.notE x (by simp [Stmt.idents, ExprOrNondet.getVars, hx])).trans hc
      exact ⟨evs', _, brun_single (.ite_true hcτ hb'), OExt.proj h.ext hO (brun_dom hb), hk⟩
  | _, _, _, _, .ite_false hc hb, _, _, _, hr, h => by
    cases hr with
    | ite _ he =>
      obtain ⟨evs', o', hb', hO, hk⟩ := run_sim' hvar hbool hcong hres hb he h.ite_else
      have hcτ := (ext_eval hcong h.ext h.srcWF h.tgtWF fun x hx =>
        h.notE x (by simp [Stmt.idents, ExprOrNondet.getVars, hx])).trans hc
      exact ⟨evs', _, brun_single (.ite_false hcτ hb'), OExt.proj h.ext hO (brun_dom hb), hk⟩
  | _, _, _, _, .ite_nondet_true hb, _, _, _, hr, h => by
    cases hr with
    | ite ht _ =>
      obtain ⟨evs', o', hb', hO, hk⟩ := run_sim' hvar hbool hcong hres hb ht h.ite_then
      exact ⟨evs', _, brun_single (.ite_nondet_true hb'), OExt.proj h.ext hO (brun_dom hb), hk⟩
  | _, _, _, _, .ite_nondet_false hb, _, _, _, hr, h => by
    cases hr with
    | ite _ he =>
      obtain ⟨evs', o', hb', hO, hk⟩ := run_sim' hvar hbool hcong hres hb he h.ite_else
      exact ⟨evs', _, brun_single (.ite_nondet_false hb'), OExt.proj h.ext hO (brun_dom hb),
        hk⟩
  | _, _, _, _, .block (l := l) hb, _, _, _, hr, h => by
    cases hr with
    | block hb'' =>
      obtain ⟨evs', o', hb', hO, hk⟩ := run_sim' hvar hbool hcong hres hb hb'' h.block
      exact ⟨evs', _, brun_single (.block hb'), OExt.block l h.ext hO (brun_dom hb), hk⟩
  | _, _, _, _, .exit, _, _, _, hr, h => by
    cases hr
    exact ⟨[], _, brun_single .exit, ⟨rfl, h.ext⟩, fun _ => .nil⟩
  | _, _, _, _, .typeDecl, _, _, _, hr, h => by
    cases hr
    exact ⟨[], _, brun_single .typeDecl, h.ext, fun _ => .nil⟩
  | _, _, _, _, .loop_exit hg, _, _, _, hr, h => by
    rcases hr.loop_cases with ⟨n, body', -, -, rfl, rfl, rfl⟩ | ⟨n, body', -, -, rfl⟩
    · exact (LoopRes.exit hcong (n := n) (body' := body') hg h).bare
    · exact (LoopRes.exit hcong hg h).checked hbool
  | _, _, _, _, .loop_iter (m := m) (inv := inv) (body := body) hg h1 h2, E, _, _, hr, h => by
    rcases hr.loop_cases with ⟨n, body', hfr, hb', hm, hinv, rfl⟩ | ⟨n, body', hfresh, hb, rfl⟩
    · -- A loop without checks is replayed by the checked loop of any number without checks.
      have hres' := LoopRes.iter hvar hcong hres hg h hfr h1
        (fun _ hI => run_sim' hvar hbool hcong hres h1 hb' hI)
        (fun _ hI => loop_sim hvar hbool hcong hres h2 rfl hfr hb' hI)
      subst hm hinv
      exact hres'.bare
    · exact (LoopRes.iter hvar hcong hres hg h hfresh h1
        (fun _ hI => run_sim' hvar hbool hcong hres h1 hb hI)
        (fun _ hI => loop_sim hvar hbool hcong hres h2 rfl hfresh hb hI)).checked hbool
  | _, _, _, _, .loop_break (m := m) (inv := inv) (body := body) hg h1, E, _, _, hr, h => by
    rcases hr.loop_cases with ⟨n, body', hfr, hb', hm, hinv, rfl⟩ | ⟨n, body', hfresh, hb, rfl⟩
    · -- A loop without checks is replayed by the checked loop of any number without checks.
      have hres' := LoopRes.break hvar hcong hres hg h hfr h1
        (fun _ hI => run_sim' hvar hbool hcong hres h1 hb' hI)
      subst hm hinv
      exact hres'.bare
    · exact (LoopRes.break hvar hcong hres hg h hfresh h1
        (fun _ hI => run_sim' hvar hbool hcong hres h1 hb hI)).checked hbool

/-- **A run of a loop from the start of an iteration, replayed by its checked loop** from a
    target store satisfying the assumptions of the loop (`LoopRes`). -/
private theorem loop_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P},
    s = .loop g m inv body md → ∀ {E : List P.Ident} {n : String} {body' : PStmts P},
    (∀ x ∈ measureVars n m, x ∉ E) → BlockRel (measureVars n m ++ E) body body' →
    ∀ {τ : SemanticStore P}, InvS F Res df E (.loop g m inv body md) σ τ →
    LoopRes F E n g m inv body' md τ evs o
  | _, _, _, _, .loop_exit hg, _, _, _, _, _, hs, _, _, _, _, _, _, h => by
    cases hs
    exact LoopRes.exit hcong hg h
  | _, _, _, _, .loop_iter hg h1 h2, _, _, _, _, _, hs, _, _, _, hfresh, hb, _, h => by
    cases hs
    exact LoopRes.iter hvar hcong hres hg h hfresh h1
      (fun _ hI => run_sim' hvar hbool hcong hres h1 hb hI)
      (fun _ hI => loop_sim hvar hbool hcong hres h2 rfl hfresh hb hI)
  | _, _, _, _, .loop_break hg h1, _, _, _, _, _, hs, _, _, _, hfresh, hb, _, h => by
    cases hs
    exact LoopRes.break hvar hcong hres hg h hfresh h1
      (fun _ hI => run_sim' hvar hbool hcong hres h1 hb hI)
end

/-! ## The simulation of reaches -/

omit [HasFvar P] [HasFvars P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- A target trace related to a nonempty source trace is nonempty. -/
private theorem Ins.ne_nil {B t t' : Trace P} (h : Ins F B t t') (ht : t ≠ []) : t' ≠ [] := by
  cases h with
  | nil => exact absurd rfl ht
  | keep _ _ | assert _ | assumeTrue _ _ _ | assumeChecked _ _ _ _ => simp

/-- A reach of the target list `ss'` from `τ` replays a reach of the source from a store `τ`
    extends emitting `evs`: its trace is related to `evs` after any events. -/
private def ReachRes (F : P.Factory) (ss' : PStmts P) (τ : SemanticStore P)
    (evs : List (Event P)) : Prop :=
  ∃ evs', BReach F ss' τ evs' ∧ ∀ B, Ins F B evs evs'

/-- A reach of the checked loop `n` from `τ`, the store of the start of an iteration, replays a
    reach of the source loop emitting `evs`, the trace related after events justifying the
    invariants at `τ`. -/
private def LoopReachRes (F : P.Factory) (n : String) (g : ExprOrNondet P) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body' : PStmts P) (md : MetaData P) (τ : SemanticStore P)
    (evs : List (Event P)) : Prop :=
  ∃ evs', BReachS F (.loop g none [] (loopBody n m inv body' md) md) τ evs' ∧
    ∀ B, Justified F inv B τ → Ins F B evs evs'

/-- **A reach of an iteration of a loop, replayed.** -/
private theorem LoopReachRes.here (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {E : List P.Ident} {n : String}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body body' : PStmts P} {md : MetaData P} {σ τ : SemanticStore P} {evs : List (Event P)}
    (hg : guardEnters F σ g) (h : InvS F Res df E (.loop g m inv body md) σ τ)
    (hfresh : ∀ x ∈ measureVars n m, x ∉ E)
    (hbody : ∀ τ', Inv F Res df (measureVars n m ++ E) body σ τ' → ReachRes F body' τ' evs) :
    LoopReachRes F n g m inv body' md τ evs := by
  obtain ⟨τ', evsMP, hMP, hext', hT', hMPa⟩ := measurePre_run hvar hcong hres h hfresh
  have hE' := res_measureVars_append (n := n) (m := m) hres h.resE
  obtain ⟨evs1', h1', hk1⟩ := hbody τ' (h.loop_body hext' hT' hE')
  have hNB : BReach F (loopBody n m inv body' md) τ _ :=
    breach_append_left (breach_append_left (breach_append_run (brun_append
      (midAssumes_run (F := F) n inv md τ) hMP) h1'))
  have hgτ := guardEnters_ext hcong h.ext h.srcWF h.tgtWF
    (fun x hx => h.notE x (by simp [Stmt.idents, hx])) hg
  refine ⟨_, .loop_here hgτ hNB, fun B hJ => ?_⟩
  have hins := ins_invAssumes (fun i a => midAssumeLabel n i a.1) md.invariantMd hJ
    (ins_asserts hMPa (hk1 _))
  simpa only [List.append_assoc] using hins

/-- **A reach of a later iteration of a loop, replayed.** -/
private theorem LoopReachRes.later (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {E : List P.Ident} {n : String}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body body' : PStmts P} {md : MetaData P} {σ τ σ1 : SemanticStore P}
    {evs1 evs2 : List (Event P)}
    (hg : guardEnters F σ g) (h : InvS F Res df E (.loop g m inv body md) σ τ)
    (hfresh : ∀ x ∈ measureVars n m, x ∉ E) (h1 : BRun F body σ evs1 (.normal σ1))
    (hbody : ∀ τ', Inv F Res df (measureVars n m ++ E) body σ τ' →
      RunRes F (measureVars n m ++ E) body' τ' evs1 (.normal σ1))
    (hnext : ∀ τ2, InvS F Res df E (.loop g m inv body md) (projectStore σ σ1) τ2 →
      LoopReachRes F n g m inv body' md τ2 evs2) :
    LoopReachRes F n g m inv body' md τ (evs1 ++ evs2) := by
  obtain ⟨τ', evsMP, hMP, hext', hT', hMPa⟩ := measurePre_run hvar hcong hres h hfresh
  have hE' := res_measureVars_append (n := n) (m := m) hres h.resE
  obtain ⟨evs1', o1', h1', hO1, hk1⟩ := hbody τ' (h.loop_body hext' hT' hE')
  rcases o1' with τ1 | ⟨_, _⟩ <;> simp only [OExt] at hO1
  have hT1 : WellFormedStore τ1 F := (brun_typed h1' hT').1
  obtain ⟨evsMPost, hMPost, hMPosta⟩ := measurePost_run (F := F) n m md τ1
  have hNB := brun_append (brun_append (brun_append (brun_append
    (midAssumes_run (F := F) n inv md τ) hMP) h1') (maintainAsserts_run (F := F) n inv md τ1))
    hMPost
  obtain ⟨evs2', h2', hk2⟩ := hnext _ (h.loop_next h1 hO1 hT1)
  have hgτ := guardEnters_ext hcong h.ext h.srcWF h.tgtWF
    (fun x hx => h.notE x (by simp [Stmt.idents, hx])) hg
  refine ⟨_, .loop_later hgτ hNB h2', fun B hJ => ?_⟩
  have hTp : WellFormedStore (projectStore τ τ1) F := WellFormedStore.proj hT1
  have hJ2 := justified_asserts (F := F) (inv := inv)
    ((((B ++ inv.mapIdx fun i a =>
        Event.assume ⟨F, τ, midAssumeLabel n i a.1, a.2, md.invariantMd i⟩) ++ evsMP) ++ evs1'))
    (τ1 := τ1) (τ2 := projectStore τ τ1) (fun i a => maintainAssertLabel n i a.1)
    md.invariantMd (fun _ _ => invCheckLabel_maintain _ _ _) fun p hp =>
      hcong p.2 τ1 _ hT1 hTp fun y hy => by simp [projectStore, h.inv_defined p hp y hy]
  have hins := ins_invAssumes (fun i a => midAssumeLabel n i a.1) md.invariantMd hJ
    (ins_asserts hMPa ((hk1 _).append
      (ins_asserts (mapIdx_asserts inv _) (ins_asserts hMPosta (hk2 _ (hJ2.append evsMPost))))))
  simpa only [List.append_assoc] using hins

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of a reach of a checked loop from its start store, after the checks before it, is a
    replay of a reach of the loop's checked form. -/
private theorem LoopReachRes.checked {n : String} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body' : PStmts P} {md : MetaData P} {τ : SemanticStore P}
    {evs : List (Event P)} (h : LoopReachRes F n g m inv body' md τ evs) :
    ReachRes F (Stmt.invChecked n g m inv body' md) τ evs := by
  obtain ⟨evs', hloop, hk⟩ := h
  have hEA := entryAsserts_run (F := F) n inv md τ
  have hEAs := entryAssumes_run (F := F) n inv md τ
  refine ⟨_, breach_append_left (breach_append_run (brun_append hEA hEAs) (.here hloop)),
    fun B => ?_⟩
  have hJ0 := justified_asserts (F := F) (inv := inv) B (τ1 := τ) (τ2 := τ)
    (fun i a => entryAssertLabel n i a.1) md.invariantMd
    (fun _ _ => invCheckLabel_entry _ _ _) fun _ _ => rfl
  have hJ1 := hJ0.append (inv.mapIdx fun i a =>
    Event.assume ⟨F, τ, entryAssumeLabel n i a.1, a.2, md.invariantMd i⟩)
  have hins := ins_asserts (mapIdx_asserts inv _)
    (ins_invAssumes (fun i a => entryAssumeLabel n i a.1)
      md.invariantMd hJ0 (by simpa only [List.append_assoc] using hk _ hJ1))
  simpa only [List.append_assoc] using hins

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of a reach of a loop without invariants and measure is a replay of a reach of the
    loop alone. -/
private theorem LoopReachRes.bare {n : String} {g : ExprOrNondet P} {body' : PStmts P}
    {md : MetaData P} {τ : SemanticStore P} {evs : List (Event P)}
    (h : LoopReachRes F n g none [] body' md τ evs) :
    ReachRes F [.loop g none [] body' md] τ evs := by
  have heq : loopBody (C := CmdExt P) n none [] body' md = body' := by
    simp [loopBody, midAssumes, measurePre, maintainAsserts, measurePost]
  obtain ⟨evs', hloop, hk⟩ := h
  rw [heq] at hloop
  exact ⟨evs', .here hloop, fun B => hk B fun _ hp => by cases hp⟩

mutual
/-- **A reach of a list, replayed by the list with its loops' checks inserted** from a target
    store satisfying the assumptions of the simulation (`ReachRes`). -/
private theorem reach_sim' (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)},
    BReach F ss σ evs → ∀ {E : List P.Ident} {ss' : PStmts P} {τ : SemanticStore P},
    BlockRel E ss ss' → Inv F Res df E ss σ τ → ReachRes F ss' τ evs
  | _, _, _, .here h1, _, _, _, hr, h => by
    cases hr with
    | cons hs _ =>
      obtain ⟨evs', h1', hk⟩ := reachS_sim hvar hbool hcong hres h1 hs h.head
      exact ⟨evs', breach_append_left h1', hk⟩
  | _, _, _, .later h1 h2, _, _, _, hr, h => by
    cases hr with
    | cons hs hr =>
      obtain ⟨evs1', o1', h1', hO1, hk1⟩ := runS_sim hvar hbool hcong hres h1 hs h.head
      rcases o1' with τ1 | ⟨_, _⟩ <;> simp only [OExt] at hO1
      obtain ⟨evs2', h2', hk2⟩ := reach_sim' hvar hbool hcong hres h2 hr
        (h.tail h1 hO1 (brun_typed h1' h.tgtWF).1)
      exact ⟨_, breach_append_run h1' h2', fun B => (hk1 B).append (hk2 _)⟩

/-- **A reach of a statement, replayed by the statements with its loops' checks inserted**, as
    `reach_sim'`. -/
private theorem reachS_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {E : List P.Ident} {ss₁ : PStmts P} {τ : SemanticStore P},
    StmtRel E s ss₁ → InvS F Res df E s σ τ → ReachRes F ss₁ τ evs
  | _, _, _, .cmd (c := .cmd c) hE hne, _, _, _, hr, h => by
    cases hr
    obtain ⟨τ1, evs', hE', -, hk⟩ := cmd_sim hcong hE h.ext h.srcWF h.tgtWF h.notE
    exact ⟨evs', .here (.cmd hE' ((hk []).ne_nil hne)), hk⟩
  | _, _, _, .cmd (c := .call _ _ _) hE _, _, _, _, _, _ => hE.elim
  | _, _, _, .ite_true hc hb, _, _, _, hr, h => by
    cases hr with
    | ite ht _ =>
      obtain ⟨evs', hb', hk⟩ := reach_sim' hvar hbool hcong hres hb ht h.ite_then
      have hcτ := (ext_eval hcong h.ext h.srcWF h.tgtWF fun x hx =>
        h.notE x (by simp [Stmt.idents, ExprOrNondet.getVars, hx])).trans hc
      exact ⟨evs', .here (.ite_true hcτ hb'), hk⟩
  | _, _, _, .ite_false hc hb, _, _, _, hr, h => by
    cases hr with
    | ite _ he =>
      obtain ⟨evs', hb', hk⟩ := reach_sim' hvar hbool hcong hres hb he h.ite_else
      have hcτ := (ext_eval hcong h.ext h.srcWF h.tgtWF fun x hx =>
        h.notE x (by simp [Stmt.idents, ExprOrNondet.getVars, hx])).trans hc
      exact ⟨evs', .here (.ite_false hcτ hb'), hk⟩
  | _, _, _, .ite_nondet_true hb, _, _, _, hr, h => by
    cases hr with
    | ite ht _ =>
      obtain ⟨evs', hb', hk⟩ := reach_sim' hvar hbool hcong hres hb ht h.ite_then
      exact ⟨evs', .here (.ite_nondet_true hb'), hk⟩
  | _, _, _, .ite_nondet_false hb, _, _, _, hr, h => by
    cases hr with
    | ite _ he =>
      obtain ⟨evs', hb', hk⟩ := reach_sim' hvar hbool hcong hres hb he h.ite_else
      exact ⟨evs', .here (.ite_nondet_false hb'), hk⟩
  | _, _, _, .block hb, _, _, _, hr, h => by
    cases hr with
    | block hb'' =>
      obtain ⟨evs', hb', hk⟩ := reach_sim' hvar hbool hcong hres hb hb'' h.block
      exact ⟨evs', .here (.block hb'), hk⟩
  | _, _, _, .loop_here (m := m) (inv := inv) (body := body) hg hb, E, _, _, hr, h => by
    rcases hr.loop_cases with ⟨n, body', hfr, hb', hm, hinv, rfl⟩ | ⟨n, body', hfresh, hb'', rfl⟩
    · -- A loop without checks is replayed by the checked loop of any number without checks.
      have hres' := LoopReachRes.here hvar hcong hres hg h hfr
        (fun _ hI => reach_sim' hvar hbool hcong hres hb hb' hI)
      subst hm hinv
      exact hres'.bare
    · exact (LoopReachRes.here hvar hcong hres hg h hfresh
        (fun _ hI => reach_sim' hvar hbool hcong hres hb hb'' hI)).checked
  | _, _, _, .loop_later (m := m) (inv := inv) (body := body) hg h1 h2, E, _, _, hr, h => by
    rcases hr.loop_cases with ⟨n, body', hfr, hb', hm, hinv, rfl⟩ | ⟨n, body', hfresh, hb, rfl⟩
    · -- A loop without checks is replayed by the checked loop of any number without checks.
      have hres' := LoopReachRes.later hvar hcong hres hg h hfr h1
        (fun _ hI => run_sim' hvar hbool hcong hres h1 hb' hI)
        (fun _ hI => loopReach_sim hvar hbool hcong hres h2 rfl hfr hb' hI)
      subst hm hinv
      exact hres'.bare
    · exact (LoopReachRes.later hvar hcong hres hg h hfresh h1
        (fun _ hI => run_sim' hvar hbool hcong hres h1 hb hI)
        (fun _ hI => loopReach_sim hvar hbool hcong hres h2 rfl hfresh hb hI)).checked

/-- **A reach of a loop from the start of an iteration, replayed by its checked loop** from a
    target store satisfying the assumptions of the loop (`LoopReachRes`). -/
private theorem loopReach_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P},
    s = .loop g m inv body md → ∀ {E : List P.Ident} {n : String} {body' : PStmts P},
    (∀ x ∈ measureVars n m, x ∉ E) → BlockRel (measureVars n m ++ E) body body' →
    ∀ {τ : SemanticStore P}, InvS F Res df E (.loop g m inv body md) σ τ →
    LoopReachRes F n g m inv body' md τ evs
  | _, _, _, .loop_here hg hb, _, _, _, _, _, hs, _, _, _, hfresh, hb', _, h => by
    cases hs
    exact LoopReachRes.here hvar hcong hres hg h hfresh
      (fun _ hI => reach_sim' hvar hbool hcong hres hb hb' hI)
  | _, _, _, .loop_later hg h1 h2, _, _, _, _, _, hs, _, _, _, hfresh, hb, _, h => by
    cases hs
    exact LoopReachRes.later hvar hcong hres hg h hfresh h1
      (fun _ hI => run_sim' hvar hbool hcong hres h1 hb hI)
      (fun _ hI => loopReach_sim hvar hbool hcong hres h2 rfl hfresh hb hI)
end

/-! ## The simulation -/

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [HasIdent P] [HasInt P] [HasIntOps P]
  [LawfulHasVal P] in
/-- Outcomes extending one another with no variable are equal. -/
private theorem OExt.eq_nil {o o' : Outcome P} (h : OExt [] o o') : o' = o := by
  have key : ∀ {σ τ : SemanticStore P}, StoreExtendsWith (· ∈ ([] : List P.Ident)) σ τ →
      τ = σ := fun h =>
    (StoreExtendsWith.eq_of_false ⟨h.1, fun x hx => (h.2 x hx).imp_right (by simp)⟩).symm
  rcases o with σ | ⟨l, σ⟩ <;> rcases o' with τ | ⟨l', τ⟩ <;> simp only [OExt] at h
  · rw [key h]
  · rw [h.1, key h.2]

omit [HasIdent P] [HasIntOps P] [LawfulHasVal P] in
/-- The assumptions of the simulation hold at the start, where both stores are the same. -/
private theorem Inv.init {ss : PStmts P} {σ : SemanticStore P} (hT : WellFormedStore σ F)
    (hσ : ∀ x, (σ x).isSome → ¬ Res x) (hid : ∀ x ∈ Block.idents ss, ¬ Res x)
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = Bool.true)
    (hty : ∃ Γ, StoreHasTyping F σ Γ ∧ Block.fvarTypesWellAnnotated Γ ss)
    (hmeas : ∀ m ∈ Block.measures ss, MeasureEvaluates F m) : Inv F Res df [] ss σ σ :=
  ⟨⟨storeAgreement_iff.2 fun _ => .inl rfl, fun _ hx => .inl hx⟩, hT, hT, by simp, hσ, hid,
    hdu, hty, hmeas⟩

/-- **A run of a list, replayed by the list with its loops' checks inserted.**  For a list `ss`
    whose loops' checks inserted give `ss'` (`BlockRel [] ss ss'`), and whose measure snapshot
    variables satisfy `Res`: a run of `ss` from a value-valued store `σ`, where `ss` is def-use
    well formed, satisfying `Res` for no variable of `σ` or of `ss`, with free-variable
    annotations agreeing with a typing of `σ` and with each measure evaluating to an integer
    where its annotations agree with the store, has a run of `ss'` from `σ` with the same
    outcome, whose trace is the source's with its events' conditions captured in stores
    extended with measure snapshots and assertions inserted (`Trace.InsertsAsserts`), and then
    assumptions inserted that evaluate to `true` or follow an assertion of an invariant with the
    same value (`Trace.InsertsCheckedAssumes`), the factory being `F`. -/
theorem run_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {ss ss' : PStmts P} (hrel : BlockRel [] ss ss')
    {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P} (hrun : BRun F ss σ evs o)
    (hT : WellFormedStore σ F) (hσ : ∀ x, (σ x).isSome → ¬ Res x)
    (hid : ∀ x ∈ Block.idents ss, ¬ Res x)
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = Bool.true)
    (hty : ∃ Γ, StoreHasTyping F σ Γ ∧ Block.fvarTypesWellAnnotated Γ ss)
    (hmeas : ∀ m ∈ Block.measures ss, MeasureEvaluates F m) :
    ∃ evs', BRun F ss' σ evs' o ∧
      RComp (Trace.InsertsAsserts (· = F)) (Trace.InsertsCheckedAssumes (· = F) InvCheck [])
        evs evs' := by
  obtain ⟨evs', o', h', hO, hk⟩ :=
    run_sim' hvar hbool hcong hres hrun hrel (Inv.init hT hσ hid hdu hty hmeas)
  exact ⟨evs', hO.eq_nil ▸ h', (hk []).split⟩

/-- **A reach of a list, replayed by the list with its loops' checks inserted.**  For a list
    `ss` whose loops' checks inserted give `ss'` (`BlockRel [] ss ss'`), and whose measure
    snapshot variables satisfy `Res`: a reach of `ss` from a value-valued store `σ`, where `ss`
    is def-use well formed, satisfying `Res` for no variable of `σ` or of `ss`, with
    free-variable annotations agreeing with a typing of `σ` and with each measure evaluating to
    an integer where its annotations agree with the store, has a reach of `ss'` from `σ` whose
    trace is the source's with assertions inserted (`Trace.InsertsAsserts`) and then checked
    assumptions inserted (`Trace.InsertsCheckedAssumes`), as in `run_sim`. -/
theorem reach_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F)
    (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hres : ∀ k, Res (measureIdent (P := P) k)) {ss ss' : PStmts P} (hrel : BlockRel [] ss ss')
    {σ : SemanticStore P} {evs : List (Event P)} (hreach : BReach F ss σ evs)
    (hT : WellFormedStore σ F) (hσ : ∀ x, (σ x).isSome → ¬ Res x)
    (hid : ∀ x ∈ Block.idents ss, ¬ Res x)
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = Bool.true)
    (hty : ∃ Γ, StoreHasTyping F σ Γ ∧ Block.fvarTypesWellAnnotated Γ ss)
    (hmeas : ∀ m ∈ Block.measures ss, MeasureEvaluates F m) :
    ∃ evs', BReach F ss' σ evs' ∧
      RComp (Trace.InsertsAsserts (· = F)) (Trace.InsertsCheckedAssumes (· = F) InvCheck [])
        evs evs' := by
  obtain ⟨evs', h', hk⟩ :=
    reach_sim' hvar hbool hcong hres hreach hrel (Inv.init hT hσ hid hdu hty hmeas)
  exact ⟨evs', h', (hk []).split⟩

end -- public section

end InsertLoopInvAsserts
end Imperative
