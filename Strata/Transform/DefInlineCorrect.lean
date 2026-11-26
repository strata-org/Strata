/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInlineProps
public import Strata.Transform.GuardFwdCorrect
public import Strata.Transform.NormLawTyped

/-! # Inlining of single-use definitions keeps every run

The run of a statement list rewritten by `defInline` follows the run of the input from the same
store: every statement steps as the input's does, with the same store after it, and every event
corresponds to the input's (`GuardFwd.GFEvRel`): same kind, factory, store, label and metadata,
and a condition with the input's value (`defInline_run_rel`, `defInline_reach_rel`).

In a store satisfying the scope invariant of guard forwarding (`GuardFwd.ScopeInv`: every recorded
right-hand side evaluates to the value of its name), the rewrite of an expression has the
expression's value (`rwE_sem`): substituting expressions holding the values of the substituted
variables keeps the value (`WellFormedSemanticEvalSubstExprs`), and the substituting normalization
keeps the value of the substituted expression in a store holding at each of its annotated
free-variable occurrences a value of the annotated type (`SubstNormLawT`). The runs keep such a
store: it conforms to a typing that the annotations of the list agree with (`StoreHasTyping`,
`Block.fvarTypesWellAnnotated`), and every recorded right-hand side has its annotated occurrences
typed by it (`RecTyped`).

These are the run and reach relations of the inlining, not a correctness theorem of their own: the
trace over-approximation built from them is stated with `OverapproximatesTracesUptoWhen`
(`Core.DefInline.defInline_overapproximatesTraces`, in `Strata.Transform.DefInlineCoreCorrect`).

Key theorems: `rwE_sem`, `defInline_run_rel`, `defInline_reach_rel`.

Key definitions: `NormLaw`, `SubstNormLawT`, `DefInlineLaws`, `RecTyped`. -/

namespace Imperative
namespace DefInline

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [HasSubstFvar P] [WPLang P]

/-- The normalization `norm` keeps the value of every expression in every well-formed store of
    the factory `F` (both have none, or the same one). -/
@[expose] def NormLaw (F : P.Factory) (norm : P.Expr → P.Expr) : Prop :=
  ∀ {σ : SemanticStore P} (e : P.Expr), WellFormedStore σ F → P.eval F σ (norm e) = P.eval F σ e

/-- The substituting normalization `norm` keeps the value of the substituted expression: for every
    substitution `g`, `norm g e` has the value of `e` with `g` substituted in every well-formed
    store of the factory `F` typing the annotated occurrences of the latter (`StoreTypes`). -/
@[expose] def SubstNormLawT (F : P.Factory) (norm : SubstNorm P) : Prop :=
  ∀ {σ : SemanticStore P} (g : P.Ident → Option P.Expr) (e : P.Expr), WellFormedStore σ F →
    StoreTypes F σ (WPOps.substFn e g) → P.eval F σ (norm g e) = P.eval F σ (WPOps.substFn e g)

/-- A normalization that keeps values in typed stores, applied after the substitution. -/
theorem NormLawT.after {F : P.Factory} {n : P.Expr → P.Expr} (h : NormLawT F n) :
    SubstNormLawT F (.after n) :=
  fun _ _ hC hT => h _ hC hT

/-- **The laws of the inlining of single-use definitions.**  What its correctness proof needs from
    the factory `F` and the substituting normalization `norm`: evaluation depends only on the free
    variables, substituting expressions holding the values of the substituted variables preserves
    evaluation, and `norm` keeps the values of the substituted expressions and adds no free
    variable. -/
structure DefInlineLaws (F : P.Factory) (norm : SubstNorm P) : Prop where
  /-- Evaluation depends only on the free variables. -/
  congr : WellFormedSemanticEvalExprCongr (P := P) F
  /-- Substituting expressions holding the values of the substituted variables preserves
      evaluation. -/
  subst : WellFormedSemanticEvalSubstExprs (P := P) F
  /-- The normalization adds no free variable to the substituted expression. -/
  fvars : ∀ g e y, y ∈ HasFvars.getFvars (norm g e) → y ∈ HasFvars.getFvars (WPOps.substFn e g)
  /-- The normalization adds no annotated free-variable occurrence to the substituted
      expression. -/
  typed : ∀ g e p, p ∈ HasFvars.getTypedFvars (norm g e) →
    p ∈ HasFvars.getTypedFvars (WPOps.substFn e g)
  /-- The normalization keeps the values of the substituted expressions in the well-formed
      stores typing their annotated occurrences. -/
  norm : SubstNormLawT F norm

variable [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P]
  {F : P.Factory} {norm : SubstNorm P} {ini : Std.HashSet P.Ident} {σ : SemanticStore P}
  {sc : Scope P}

/-- Every recorded right-hand side of the scope `sc` has its annotated occurrences typed by the
    store `σ` (`StoreTypes`). -/
@[expose] def RecTyped (F : P.Factory) (σ : SemanticStore P) (sc : Scope P) : Prop :=
  ∀ (y : P.Ident) d, sc[y]? = some (some d) → StoreTypes F σ d

omit [DecidableEq P.Ident] [HasFvar P] [HasSubstFvar P] [WPLang P] [LawfulBEq P.Ident]
  [LawfulHasVal P] in
/-- `RecTyped` depends on the scope through its lookups. -/
theorem RecTyped.congr {sc sc' : Scope P} (hs : ∀ x : P.Ident, sc'[x]? = sc[x]?)
    (h : RecTyped F σ sc) : RecTyped F σ sc' :=
  fun y d hy => h y d ((hs y).symm.trans hy)

omit [DecidableEq P.Ident] [HasFvar P] [HasSubstFvar P] [WPLang P] [LawfulBEq P.Ident]
  [LawfulHasVal P] in
/-- `RecTyped` survives the growth of the store. -/
theorem RecTyped.grow {σ' : SemanticStore P} (h : RecTyped F σ sc)
    (hg : ∀ x v, σ x = some v → σ' x = some v) : RecTyped F σ' sc :=
  fun y d hy => (h y d hy).grow hg

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
/-- The substitution of the recorded right-hand sides into `e` has its annotated occurrences typed
    by a store conforming to a typing `Γ` that the annotations of `e` agree with, when the
    recorded right-hand sides have theirs typed. -/
theorem storeTypes_substFn {Γ : VarTyping P} (hΓ : StoreHasTyping F σ Γ)
    (hR : RecTyped F σ sc) {e : P.Expr} (ha : Γ.annotates (HasFvars.getTypedFvars e)) :
    StoreTypes F σ (WPOps.substFn e (look sc)) := by
  intro x ty hx
  rcases WPLang.getTypedFvars_substFn e (look sc) _ hx with ⟨hx, -⟩ | ⟨z, d, -, hz, hd⟩
  · exact hΓ x ty (ha x ty hx)
  · exact hR z d (look_some hz) x ty hd

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
/-- **The rewrite keeps the value**: in a well-formed store satisfying the scope invariant and
    typing the annotated occurrences of the substitution of the recorded right-hand sides into
    `e`, the rewrite of `e` evaluates as `e`. -/
theorem rwE_sem (hL : DefInlineLaws F norm) (hC : WellFormedStore σ F)
    (hI : ScopeInv F ini σ sc) (e : P.Expr) (hT : StoreTypes F σ (WPOps.substFn e (look sc))) :
    P.eval F σ (rwE norm sc e) = P.eval F σ e := by
  let sm := (HasFvars.getFvars e).filterMap fun y => (look sc y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, look sc x = Map.find? sm x :=
    fun x hx => (find?_filterMap (look sc) _ x (.inl hx)).symm
  rw [rwE, hL.norm _ _ hC hT, WPLang.substFn_eq e (look sc) sm hfind]
  refine hL.subst hC hC sm e (fun k hk v hv => ?_) fun _ _ _ => rfl
  obtain ⟨⟨w, hw, hdw⟩, -⟩ := hI.2 k _ (look_some ((hfind k hk).trans hv))
  exact ⟨by simp [hw], hdw.trans hw.symm⟩

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
/-- The free variables of the rewrite of `e` are in the scope or defined by no `init` of the list
    (`ini`) when those of `e` are, in a store satisfying the scope invariant: they are those of
    `e` and of the recorded right-hand sides it reads. -/
private theorem rwE_fvars (hL : DefInlineLaws F norm) (hI : ScopeInv F ini σ sc) {e : P.Expr}
    (he : ∀ z ∈ HasFvars.getFvars e, sc.contains z = true ∨ ini.contains z = false) :
    ∀ z ∈ HasFvars.getFvars (rwE norm sc e), sc.contains z = true ∨ ini.contains z = false := by
  let sm := (HasFvars.getFvars e).filterMap fun y => (look sc y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, look sc x = Map.find? sm x :=
    fun x hx => (find?_filterMap (look sc) _ x (.inl hx)).symm
  intro z hz
  replace hz := hL.fvars _ _ z hz
  rw [WPLang.substFn_eq e (look sc) sm hfind] at hz
  rcases WPLang.getFvars_substFvars e sm z hz with ⟨hz, -⟩ | ⟨x, v, hx, hv, hz⟩
  · exact he z hz
  · exact (hI.2 x _ (look_some ((hfind x hx).trans hv))).2 z hz

omit [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [BEq P.Ident] [LawfulBEq P.Ident]
  [Hashable P.Ident] [LawfulHasVal P] in
/-- An `init` of the undefined `x` to a value of type `ty` makes a store conforming to `Γ` conform
    to `Γ` extended by `x : ty`. -/
theorem storeHasTyping_init {Γ : VarTyping P} {σ1 : SemanticStore P} {x : P.Ident}
    {ty : P.Ty} {v : P.Val} (hΓ : StoreHasTyping F σ Γ) (h1 : σ1 x = some v)
    (hfr : ∀ y, x ≠ y → σ1 y = σ y) (hty : HasVal.valueOfTy F v ty) :
    StoreHasTyping F σ1 (Γ.extend [(x, ty)]) := by
  intro y t hy
  by_cases hxy : x = y
  · subst hxy
    simp only [VarTyping.extend, List.find?, beq_self_eq_true, Option.some.injEq] at hy
    exact hy ▸ ⟨v, h1, hty⟩
  · simp only [VarTyping.extend, beq_iff_eq, hxy, not_false_eq_true, List.find?_cons_of_neg,
      List.find?_nil] at hy
    exact (hfr y hxy).symm ▸ hΓ y t hy

omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- An `init` of the undefined `x` keeps every value the store holds. -/
private theorem init_grow {σ1 : SemanticStore P} {x : P.Ident} (h0 : σ x = none)
    (hfr : ∀ y, x ≠ y → σ1 y = σ y) : ∀ y w, σ y = some w → σ1 y = some w := fun y w hy => by
  rw [hfr y (by rintro rfl; simp [h0] at hy), hy]

omit [DecidableEq P.Ident] [HasFvar P] [HasSubstFvar P] [WPLang P] [LawfulHasVal P] in
/-- Entering `x` in the scope with an entry whose expression, if any, has its annotated
    occurrences typed keeps `RecTyped` in a grown store. -/
private theorem RecTyped.push {st : GSt P} {σ1 : SemanticStore P} {x : P.Ident}
    {val : Option P.Expr} (hR : RecTyped F σ st.scope)
    (hg : ∀ y w, σ y = some w → σ1 y = some w) (hval : ∀ d, val = some d → StoreTypes F σ1 d) :
    RecTyped F σ1 (st.push x val).scope := by
  obtain ⟨sc, tr, n⟩ := st
  intro y d hy
  simp only [GSt.push, Std.HashMap.getElem?_insert] at hy
  split at hy
  · cases hy
    exact hval d rfl
  · exact (hR y d hy).grow hg

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
mutual
/-- **A run of a list, replayed on its rewrite.**  A run of a list in passive form from a
    well-formed store satisfying the scope invariant, conforming to a typing `Γ` the annotations
    of the list agree with and typing the annotated occurrences of the recorded right-hand sides,
    has a run of the rewritten list from the same store with the same outcome and corresponding
    events. -/
private theorem di_run [LawfulBEq P.Ident] [LawfulHasVal P] (hL : DefInlineLaws F norm)
    (cx : ICtx P) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRun F ss σ evs o → ∀ {st : GSt P} {Γ : VarTyping P}, Block.passiveForm ss = true →
    (∀ x ∈ Block.assignedVars ss, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope → StoreHasTyping F σ Γ → Block.fvarTypesWellAnnotated Γ ss →
    RecTyped F σ st.scope →
    ∃ evs', BRun F (walk norm cx st ss).1 σ evs' o ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _ => ⟨[], .nil, .nil⟩
  | _, _, _, _, .cons_normal h1 h2, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    have hini' := fun x hx => hini x (List.mem_append_left _ hx)
    obtain ⟨evs1, h1', hr1, hpost⟩ := di_runS hL cx h1 (passive_cons hp).1 hini' hC hI hΓ hA.1 hR
    obtain ⟨hC1, hI1, hΓ1, hR1⟩ := hpost _ rfl
    obtain ⟨evs2, h2', hr2⟩ := di_run hL cx h2 (passive_cons hp).2
      (fun x hx => hini x (List.mem_append_right _ hx)) hC1 hI1 hΓ1 hA.2 hR1
    exact ⟨evs1 ++ evs2, .cons_normal h1' h2', hr1.append hr2⟩
  | _, _, _, _, .cons_exit h1, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    obtain ⟨evs1, h1', hr1, -⟩ := di_runS hL cx h1 (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hC hI hΓ hA.1 hR
    exact ⟨evs1, .cons_exit h1', hr1⟩
/-- **A run of a statement, replayed on its rewrite**: `di_run` for one statement, and the store
    after it satisfies the scope invariant for the state after the walk over it, conforms to `Γ`
    extended by the statement's definitions and types the annotated occurrences of the recorded
    right-hand sides of that state. -/
private theorem di_runS [LawfulBEq P.Ident] [LawfulHasVal P] (hL : DefInlineLaws F norm)
    (cx : ICtx P) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {st : GSt P} {Γ : VarTyping P}, Block.passiveForm [s] = true →
    (∀ x ∈ Stmt.assignedVars s, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope → StoreHasTyping F σ Γ → Stmt.fvarTypesWellAnnotated Γ s →
    RecTyped F σ st.scope →
    ∃ evs', BRunS F (walkS norm cx st s).1 σ evs' o ∧ List.Rel₂ GFEvRel evs evs' ∧
      ∀ σ', o = .normal σ' → WellFormedStore σ' F ∧
        ScopeInv F cx.ini σ' (walkS norm cx st s).2.scope ∧
        StoreHasTyping F σ' (Γ.extend (Stmt.typedDefinedVars s)) ∧
        RecTyped F σ' (walkS norm cx st s).2.scope
  | _, _, _, _, .cmd (c := .cmd (.init x ty (.det e) md)) h, st, _, _, hini, hC, hI, hΓ, hA,
    hR => by
    obtain ⟨v, hev, h0, h1, hfr, rfl, hty⟩ := EvalCmdE.init_det_inv h
    have hT := storeTypes_substFn hΓ hR (e := e) hA
    refine ⟨[], .cmd (evalE_init_replay h (rwE_sem hL hC hI e hT)), .nil, fun σ' ho => ?_⟩
    cases ho
    have hg := init_grow h0 hfr
    obtain ⟨hC1, hI1⟩ := hI.push hL.congr hC h0 h1 hfr (LawfulHasVal.valueOfTy_isVal _ _ _ hty)
      (val := entry cx st.scope x e (rwE norm st.scope e))
      (hini x (by simp [Stmt.assignedVars])) fun d hd =>
        (entry_some hd).1 ▸ ⟨(rwE_sem hL hC hI e hT).trans hev, rwE_fvars hL hI (entry_some hd).2⟩
    exact ⟨hC1, hI1, storeHasTyping_init hΓ h1 hfr hty, RecTyped.push hR hg fun d hd =>
      (entry_some hd).1 ▸ (hT.mono (hL.typed _ _)).grow hg⟩
  | _, _, _, _, .cmd (c := .cmd (.init x ty .nondet md)) h, st, _, _, hini, hC, hI, hΓ, _, hR => by
    obtain ⟨v, hty, h0, h1, hfr, rfl⟩ := EvalCmdE.init_nondet_inv h
    refine ⟨[], .cmd h, .nil, fun σ' ho => ?_⟩
    cases ho
    obtain ⟨hC1, hI1⟩ := hI.push hL.congr hC h0 h1 hfr (LawfulHasVal.valueOfTy_isVal _ _ _ hty)
      (val := none) (hini x (by simp [Stmt.assignedVars])) fun _ hd => by cases hd
    exact ⟨hC1, hI1, storeHasTyping_init hΓ h1 hfr hty,
      RecTyped.push hR (init_grow h0 hfr) fun _ hd => by cases hd⟩
  | _, _, _, _, .cmd (c := .cmd (.set _ _ _)) _, _, _, hp, _, _, _, _, _, _ => by
    simp [Block.passiveForm] at hp
  | _, _, _, _, .cmd (c := .cmd (.assume l e md)) h, st, _, _, _, hC, hI, hΓ, hA, hR => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assume_inv h
    have hT := storeTypes_substFn hΓ hR (e := e) hA
    exact ⟨_, .cmd .eval_assume, .cons ⟨rfl, rfl, rfl, rfl, fun he =>
      (rwE_sem hL hC hI e hT).trans he⟩ .nil, fun σ' ho => by cases ho; exact ⟨hC, hI, hΓ, hR⟩⟩
  | _, _, _, _, .cmd (c := .cmd (.assert l e md)) h, st, _, _, _, hC, hI, hΓ, hA, hR => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assert_inv h
    have hT := storeTypes_substFn hΓ hR (e := e) hA
    exact ⟨_, .cmd .eval_assert, .cons ⟨rfl, rfl, rfl, rfl, rwE_sem hL hC hI e hT⟩ .nil,
      fun σ' ho => by cases ho; exact ⟨hC, hI, hΓ, hR⟩⟩
  | _, _, _, _, .cmd (c := .cmd (.cover l e md)) h, st, _, _, _, hC, hI, hΓ, hA, hR => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.cover_inv h
    have hT := storeTypes_substFn hΓ hR (e := e) hA
    exact ⟨_, .cmd .eval_cover, .cons ⟨rfl, rfl, rfl, rfl, rwE_sem hL hC hI e hT⟩ .nil,
      fun σ' ho => by cases ho; exact ⟨hC, hI, hΓ, hR⟩⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _, _, _, _, _, _, _, _, _ => h.elim
  | _, _, _, _, .ite_true _ _, _, _, hp, _, _, _, _, _, _
  | _, _, _, _, .ite_false _ _, _, _, hp, _, _, _, _, _, _ => by
    simp [Block.passiveForm] at hp
  | _, σ, _, _, .ite_nondet_true (tss := tss) (ess := ess) (md := md) h, st, _, hp, hini, hC, hI,
    hΓ, hA, hR => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := di_run hL cx h hp.1.1
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC hI hΓ hA.2.1 hR
    refine ⟨evs', .ite_nondet_true h', hr, fun σ' ho => ?_⟩
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.1
    obtain rfl : σ' = σ := by
      cases ho
      exact funext fun x => by by_cases hx : (σ x).isSome <;> simp_all [projectStore]
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st tss).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame norm cx _ ess)).undo
    exact ⟨hC, hI.congr s2, hΓ, hR.congr s2⟩
  | _, σ, _, _, .ite_nondet_false (tss := tss) (ess := ess) (md := md) h, st, _, hp, hini, hC, hI,
    hΓ, hA, hR => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st tss).undo
    obtain ⟨evs', h', hr⟩ := di_run hL cx h (st := (walk norm cx st tss).2.undoTo st.trailLen)
      hp.1.2 (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC (hI.congr s1) hΓ hA.2.2
      (hR.congr s1)
    refine ⟨evs', .ite_nondet_false h', hr, fun σ' ho => ?_⟩
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.2
    obtain rfl : σ' = σ := by
      cases ho
      exact funext fun x => by by_cases hx : (σ x).isSome <;> simp_all [projectStore]
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame norm cx _ ess)).undo
    exact ⟨hC, hI.congr s2, hΓ, hR.congr s2⟩
  | _, _, _, _, .block _, _, _, hp, _, _, _, _, _, _
  | _, _, _, _, .exit, _, _, hp, _, _, _, _, _, _
  | _, _, _, _, .typeDecl, _, _, hp, _, _, _, _, _, _
  | _, _, _, _, .loop_exit _, _, _, hp, _, _, _, _, _, _
  | _, _, _, _, .loop_iter _ _ _, _, _, hp, _, _, _, _, _, _
  | _, _, _, _, .loop_break _ _, _, _, hp, _, _, _, _, _, _ => by simp [Block.passiveForm] at hp
end

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
/-- The walk over a command gives a command. -/
private theorem walkS_cmd (cx : ICtx P) (st : GSt P) (c : CmdExt P) :
    ∃ c', (walkS norm cx st (.cmd c)).1 = .cmd c' := by
  rcases c with ((_ | _ | _ | _ | _) | _)
  all_goals first | exact ⟨_, rfl⟩ | (rename_i e _; cases e <;> exact ⟨_, rfl⟩)

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] [Hashable P.Ident]
  [HasSubstFvar P] [WPLang P] [LawfulHasVal P] in
/-- A run of a command emitting events reaches the end of its events. -/
private theorem brunS_cmd_reach {c : CmdExt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P} (h : BRunS F (.cmd c) σ evs o) (hne : evs ≠ []) :
    BReachS F (.cmd c) σ evs := by
  cases h with
  | cmd h => exact .cmd h hne

mutual
/-- **A reach of a list, replayed on its rewrite.**  A reach of a list in passive form from a
    well-formed store satisfying the scope invariant, conforming to a typing `Γ` the annotations
    of the list agree with and typing the annotated occurrences of the recorded right-hand sides,
    has a reach of the rewritten list from the same store with corresponding events. -/
private theorem di_reach (hL : DefInlineLaws F norm) (cx : ICtx P) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)},
    BReach F ss σ evs → ∀ {st : GSt P} {Γ : VarTyping P}, Block.passiveForm ss = true →
    (∀ x ∈ Block.assignedVars ss, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope → StoreHasTyping F σ Γ → Block.fvarTypesWellAnnotated Γ ss →
    RecTyped F σ st.scope →
    ∃ evs', BReach F (walk norm cx st ss).1 σ evs' ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, .here h, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    obtain ⟨evs', h', hr⟩ := di_reachS hL cx h (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hC hI hΓ hA.1 hR
    exact ⟨evs', .here h', hr⟩
  | _, _, _, .later h1 h2, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    obtain ⟨evs1, h1', hr1, hpost⟩ := di_runS hL cx h1 (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hC hI hΓ hA.1 hR
    obtain ⟨hC1, hI1, hΓ1, hR1⟩ := hpost _ rfl
    obtain ⟨evs2, h2', hr2⟩ := di_reach hL cx h2 (passive_cons hp).2
      (fun x hx => hini x (List.mem_append_right _ hx)) hC1 hI1 hΓ1 hA.2 hR1
    exact ⟨evs1 ++ evs2, .later h1' h2', hr1.append hr2⟩
/-- **A reach of a statement, replayed on its rewrite**: `di_reach` for one statement. -/
private theorem di_reachS (hL : DefInlineLaws F norm) (cx : ICtx P) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {st : GSt P} {Γ : VarTyping P}, Block.passiveForm [s] = true →
    (∀ x ∈ Stmt.assignedVars s, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope → StoreHasTyping F σ Γ → Stmt.fvarTypesWellAnnotated Γ s →
    RecTyped F σ st.scope →
    ∃ evs', BReachS F (walkS norm cx st s).1 σ evs' ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, .cmd (c := c) h hne, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    obtain ⟨evs', h', hr, -⟩ := di_runS hL cx (.cmd h) hp hini hC hI hΓ hA hR
    obtain ⟨c', hc'⟩ := walkS_cmd (norm := norm) cx st c
    rw [hc'] at h' ⊢
    exact ⟨evs', brunS_cmd_reach h' fun h0 => hne (by subst h0; cases hr; rfl), hr⟩
  | _, _, _, .ite_true _ _, _, _, hp, _, _, _, _, _, _
  | _, _, _, .ite_false _ _, _, _, hp, _, _, _, _, _, _ => by
    simp [Block.passiveForm] at hp
  | _, _, _, .ite_nondet_true (tss := tss) h, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := di_reach hL cx h hp.1.1
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC hI hΓ hA.2.1 hR
    exact ⟨evs', .ite_nondet_true h', hr⟩
  | _, _, _, .ite_nondet_false (tss := tss) h, st, _, hp, hini, hC, hI, hΓ, hA, hR => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st tss).undo
    obtain ⟨evs', h', hr⟩ := di_reach hL cx h (st := (walk norm cx st tss).2.undoTo st.trailLen)
      hp.1.2 (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC (hI.congr s1) hΓ hA.2.2
      (hR.congr s1)
    exact ⟨evs', .ite_nondet_false h', hr⟩
  | _, _, _, .block _, _, _, hp, _, _, _, _, _, _
  | _, _, _, .loop_here _ _, _, _, hp, _, _, _, _, _, _
  | _, _, _, .loop_later _ _ _, _, _, hp, _, _, _, _, _, _ => by simp [Block.passiveForm] at hp
end

omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [LawfulHasVal P] in
/-- The names the context of `defInline` records as defined by an `init` of the list. -/
private theorem defInline_ctx (ss : PStmts P) :
    ∀ x ∈ Block.assignedVars ss,
      (Std.HashSet.ofList (Block.assignedVarsH ss)).contains x = true := fun x hx => by
  simpa [Std.HashSet.contains_ofList, Block.assignedVarsH_eq] using hx

/-- **A run of a list, and of its inlining.**  A run of a list in passive form from a well-formed
    store conforming to a typing `Γ` that the annotations of the list agree with has a run of
    `defInline norm ss` from the same store with the same outcome, whose events correspond to it
    one by one (`GFEvRel`), for a factory and a normalization satisfying `DefInlineLaws`. -/
theorem defInline_run_rel (hL : DefInlineLaws F norm) {ss : PStmts P}
    (hp : Block.passiveForm ss = true) {evs : List (Event P)} {o : Outcome P}
    (hC : WellFormedStore σ F) {Γ : VarTyping P} (hΓ : StoreHasTyping F σ Γ)
    (hA : Block.fvarTypesWellAnnotated Γ ss) (h : BRun F ss σ evs o) :
    ∃ evs', BRun F (defInline norm ss) σ evs' o ∧ List.Rel₂ GFEvRel evs evs' :=
  di_run hL _ h hp (defInline_ctx ss) hC scopeInv_empty hΓ hA fun _ _ h => by simp at h

/-- **A reach of a list, and of its inlining.**  A reach of a list in passive form from a
    well-formed store conforming to a typing `Γ` that the annotations of the list agree with has
    a reach of `defInline norm ss` from the same store whose events correspond to it one by one
    (`GFEvRel`), for a factory and a normalization satisfying `DefInlineLaws`. -/
theorem defInline_reach_rel (hL : DefInlineLaws F norm) {ss : PStmts P}
    (hp : Block.passiveForm ss = true) {evs : List (Event P)} (hC : WellFormedStore σ F)
    {Γ : VarTyping P} (hΓ : StoreHasTyping F σ Γ) (hA : Block.fvarTypesWellAnnotated Γ ss)
    (h : BReach F ss σ evs) :
    ∃ evs', BReach F (defInline norm ss) σ evs' ∧ List.Rel₂ GFEvRel evs evs' :=
  di_reach hL _ h hp (defInline_ctx ss) hC scopeInv_empty hΓ hA fun _ _ h => by simp at h

/-! ## The inlining at a caller's choice of names

`di_run` and `di_reach` are proved for an arbitrary context, with no hypothesis on its
occurrence counts: substituting a name by the right-hand side its `init` gave it keeps the value
whatever the name's count is, the count being only what keeps `defInline`'s output no larger
than its input.  So `defInlineWith norm sel` satisfies the same two theorems as `defInline norm`,
for every `sel`. -/

/-- **A run of a list, and of its inlining at a caller's choice of names**: `defInline_run_rel`
    for `defInlineWith norm sel`, for every `sel`. -/
theorem defInlineWith_run_rel (hL : DefInlineLaws F norm) {sel : Std.HashMap P.Ident Nat}
    {ss : PStmts P} (hp : Block.passiveForm ss = true) {evs : List (Event P)} {o : Outcome P}
    (hC : WellFormedStore σ F) {Γ : VarTyping P} (hΓ : StoreHasTyping F σ Γ)
    (hA : Block.fvarTypesWellAnnotated Γ ss) (h : BRun F ss σ evs o) :
    ∃ evs', BRun F (defInlineWith norm sel ss) σ evs' o ∧ List.Rel₂ GFEvRel evs evs' :=
  di_run hL _ h hp (defInline_ctx ss) hC scopeInv_empty hΓ hA fun _ _ h => by simp at h

/-- **A reach of a list, and of its inlining at a caller's choice of names**:
    `defInline_reach_rel` for `defInlineWith norm sel`, for every `sel`. -/
theorem defInlineWith_reach_rel (hL : DefInlineLaws F norm) {sel : Std.HashMap P.Ident Nat}
    {ss : PStmts P} (hp : Block.passiveForm ss = true) {evs : List (Event P)}
    (hC : WellFormedStore σ F) {Γ : VarTyping P} (hΓ : StoreHasTyping F σ Γ)
    (hA : Block.fvarTypesWellAnnotated Γ ss) (h : BReach F ss σ evs) :
    ∃ evs', BReach F (defInlineWith norm sel ss) σ evs' ∧ List.Rel₂ GFEvRel evs evs' :=
  di_reach hL _ h hp (defInline_ctx ss) hC scopeInv_empty hΓ hA fun _ _ h => by simp at h

end -- public section

end DefInline
end Imperative
