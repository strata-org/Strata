/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.RewritePassesProps

/-! # Guard forwarding keeps every run

The run of a statement list rewritten by guard forwarding follows the run of the input from the
same store: every statement steps as the input's does, with the same store after it, and every
event corresponds to the input's (`GFEvRel`): same kind, factory, store, label and metadata; an
assertion's or a cover's condition evaluates to the input's value; an assumption's condition
evaluates to `true` whenever the input's does (`guardFwd_run_rel`, `guardFwd_reach_rel`).

The rewrite of an expression evaluates, in a store satisfying the scope invariant `ScopeInv` and
with a memo of descents satisfying `MemoInv`, to a value of the type of the input's value, and to
the input's value when the guard map holds in the store (`rw_sem`).  The exact rewrite of an
assertion's or a cover's condition evaluates as the condition (`rwExact_sem`).  At the root of a
statement the guard map is empty, so the rewritten `init` right-hand side has the input's value
and the rewritten `assume` condition evaluates as the input's.  Inside a conditional whose guard
is false, its `then` arm is rewritten under a guard map that does not hold; under strict
evaluation (every part of a conditional must have a value) the rewrite still has a value of the
same type there, which is what keeps the conditional's value.

The laws of the expression language the proof uses are `GuardFwdLaws`: variables evaluate to their
value, evaluation depends on the free variables only, substituting expressions with the values of
the substituted variables preserves evaluation (`WellFormedSemanticEvalSubstExprs`), values have a
type, changing the values of the free variables to values of the same types keeps a value of the
same type (`retype`), the evaluation of a conditional (`ite_parts`, `ite_build`), and the
evaluation of an equality of a defined variable with itself (`eq_refl`).

These are the run and reach relations of guard forwarding, not a correctness theorem of their own:
the trace over-approximation built from them is stated with `OverapproximatesTracesUptoWhen`
(`Core.GuardFwd.guardFwd_overapproximatesTraces`, in `Strata.Transform.GuardFwdCoreCorrect`).

Key theorems: `rw_sem`, `rwExact_sem`, `guardFwd_run_rel`, `guardFwd_reach_rel`.

Key definitions: `MemoInv`, `GFEvRel`; `SameTy`, `GuardFwdLaws`, `ScopeInv` and `GCons` are in
`Strata.Transform.RewritePassesProps`. -/

namespace Imperative
namespace GuardFwd

open WP BigStep

public section

variable {P : PureExpr}
variable [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [GuardOps P]
variable [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P]
variable {F : P.Factory} {ini : Std.HashSet P.Ident} {σ : SemanticStore P} {sc : Scope P}

/-- **The memo invariant**: every atomic rewrite the memo records for a name has a value of the
    type of the name's value, and that value when the guard map holds. -/
@[expose] def MemoInv (F : P.Factory) (σ : SemanticStore P) (K : Guards P) (M : Memo P) : Prop :=
  ∀ (y : P.Ident) r, M[y]? = some (some r) →
    ∃ v w, σ y = some v ∧ P.eval F σ r = some w ∧ SameTy F v w ∧ (GCons F σ K → w = v)

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [LawfulBEq P.Ident] [LawfulHasVal P] [GuardOps P] in
/-- The memo invariant depends on the guard map through its lookups. -/
theorem MemoInv.congr {K K' : Guards P} {M : Memo P} (hK : ∀ x : P.Ident, K'[x]? = K[x]?)
    (h : MemoInv F σ K M) : MemoInv F σ K' M := fun y r hy =>
  (h y r hy).imp fun _ ⟨w, h1, h2, h3, h4⟩ =>
    ⟨w, h1, h2, h3, fun hk => h4 (hk.congr fun x => (hK x).symm)⟩

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [LawfulHasVal P] in
/-- The empty memo satisfies the memo invariant. -/
theorem MemoInv.empty {K : Guards P} : MemoInv F σ K ({} : Memo P) := fun _ _ h => by simp at h

omit [Hashable P.Ident] [LawfulHasVal P] in
/-- Two expressions that are the same variable or the same literal evaluate alike. -/
private theorem sameValue_eval (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) {a b : P.Expr}
    (h : sameValue a b = true) : P.eval F σ a = P.eval F σ b := by
  unfold sameValue at h
  split at h
  · rename_i x y hx hy
    rw [hL.var a x σ hC hx, hL.var b y σ hC hy, eq_of_beq h]
  · exact WPLang.sameLit_eval h

/-- **The rewrite keeps a value.**  In a well-formed store satisfying the scope invariant, with a
    memo satisfying the memo invariant, the rewrite of an expression with a value has a value of
    the same type, and the same value when the guard map holds in the store; the memo of the
    rewrite satisfies the memo invariant. -/
theorem rw_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) (hI : ScopeInv F ini σ sc)
    (fuel : Nat) (deep cond : Bool) (cnt : Std.HashMap P.Ident Nat) (K : Guards P) (M : Memo P)
    (e : P.Expr) : MemoInv F σ K M →
    (∀ {v : P.Val}, P.eval F σ e = some v →
      ∃ v', P.eval F σ (rw fuel deep cond sc cnt K M e).1 = some v' ∧ SameTy F v v' ∧
        (GCons F σ K → v' = v)) ∧ MemoInv F σ K (rw fuel deep cond sc cnt K M e).2.2 := by
  fun_induction rw fuel deep cond sc cnt K M e
  case case1 fuel deep cond K M e c t f hv hk iht | case2 K M e c t f hv hk iht =>
    intro hM
    obtain ⟨g, hg, hK⟩ : ∃ g, HasFvar.getFvar c = some g ∧ K[g]? = some _ := by
      split at hk <;> try cases hk
      exact ⟨_, ‹_›, hk⟩
    refine ⟨fun {v} he => ?_, (iht hM).2⟩
    rw [WPLang.iteView?_eval hv] at he
    obtain ⟨wc, wt, wf, hc, ht, hf, hb, htf, h1, h2⟩ := hL.ite_parts he
    have hcg : σ g = some wc := (hL.var c g σ hC hg).symm.trans hc
    first
    | obtain ⟨v', h', hs, hx⟩ := (iht hM).1 ht
      refine ⟨v', h', (ite_sameTy hL hb htf ht h1 h2).trans hs, fun hk => ?_⟩
      rw [hx hk, h1 (by simpa using hcg.symm.trans (hk g true hK))]
    | obtain ⟨v', h', hs, hx⟩ := (iht hM).1 hf
      refine ⟨v', h', ((ite_sameTy hL hb htf ht h1 h2).trans htf).trans hs, fun hk => ?_⟩
      rw [hx hk, h2 (by simpa using hcg.symm.trans (hk g false hK))]
  case case3 fuel deep cond K M e c t f hv hk c' K1 M1 hc' hl ihc iht
    | case4 fuel deep cond K M e c t f hv hk c' K1 M1 hc' hl ihc iht =>
    intro hM
    have hK1 := rw_guards fuel deep true sc cnt K M c
    rw [hc'] at ihc hK1
    obtain ⟨ihc1, hM1⟩ := ihc hM
    obtain ⟨iht1, hM2⟩ := iht (hM1.congr hK1)
    refine ⟨fun {v} he => ?_, hM2.congr fun x => (hK1 x).symm⟩
    rw [WPLang.iteView?_eval hv] at he
    obtain ⟨wc, wt, wf, hc, ht, hf, hb, htf, h1, h2⟩ := hL.ite_parts he
    obtain ⟨wc', hc2, hsc, hxc⟩ := ihc1 hc
    have hlit := WPLang.boolLit?_eval (F := F) (σ := σ) hl
    try simp only [↓reduceIte, Bool.false_eq_true] at hlit
    have hlv := hlit.symm.trans hc2
    first
    | have hw : wc' = HasBool.ttVal F := Option.some.inj (hlv.symm.trans (hL.val.eval_tt σ))
      obtain ⟨v', h', hs, hx⟩ := iht1 ht
      refine ⟨v', h', (ite_sameTy hL hb htf ht h1 h2).trans hs, fun hk => ?_⟩
      rw [hx (hk.congr hK1), h1 ((hxc hk).symm.trans hw)]
    | have hw : wc' = HasBool.ffVal F := Option.some.inj (hlv.symm.trans (hL.val.eval_ff σ))
      obtain ⟨v', h', hs, hx⟩ := iht1 hf
      refine ⟨v', h', ((ite_sameTy hL hb htf ht h1 h2).trans htf).trans hs, fun hk => ?_⟩
      rw [hx (hk.congr hK1), h2 ((hxc hk).symm.trans hw)]
  case case5 fuel deep cond K M e c t f hv hk c' K1 M1 hc' hl g hg t' K2 M2 ht' f' K3 M3 hf'
      ihc iht ihf =>
    intro hM
    have hK1 := rw_guards fuel deep true sc cnt K M c
    have hK2 := rw_guards fuel deep false sc cnt (K1.insert g true) ∅ t
    simp only [hc', ht', hf'] at ihc iht ihf hK1 hK2
    refine ⟨fun {v} he => ?_, MemoInv.empty⟩
    have hK0 : K[g]? = none := by simpa [hg] using hk
    rw [WPLang.iteView?_eval hv] at he
    obtain ⟨wc, wt, wf, hc, ht, hf, hb, htf, h1, h2⟩ := hL.ite_parts he
    have hcg : σ g = some wc := (hL.var c g σ hC hg).symm.trans hc
    obtain ⟨wc', hc2, hsc, hxc⟩ := (ihc hM).1 hc
    obtain ⟨wt', ht2, hst, hxt⟩ := (iht MemoInv.empty).1 ht
    obtain ⟨wf', hf2, hsf, hxf⟩ := (ihf MemoInv.empty).1 hf
    obtain ⟨v', hv', h1', h2'⟩ := hL.ite_build hc2 ht2 hf2 (hsc.symm.trans hb)
      ((hst.symm.trans htf).trans hsf)
    have hvs : SameTy F v v' := ((ite_sameTy hL hb htf ht h1 h2).trans hst).trans
      (ite_sameTy hL (hsc.symm.trans hb) ((hst.symm.trans htf).trans hsf) ht2 h1' h2').symm
    have hvx : GCons F σ K → v' = v := fun hk => by
      rw [hxc hk] at h1' h2'
      rcases hL.bool_cases hb with rfl | rfl
      · rw [h1' rfl, h1 rfl, hxt ((hk.congr hK1).insert (by simpa using hcg))]
      · refine (h2' rfl).trans ((hxf ?_).trans (h2 rfl).symm)
        refine (hk.insert (b := false) (by simpa using hcg)).congr fun x => ?_
        simp only [Std.HashMap.getElem?_insert, hK2, hK1]
        split <;> rfl
    split
    · rename_i hsa
      have hv'' : v' = wt' := (hL.bool_cases (hsc.symm.trans hb)).elim h1' fun h =>
        (h2' h).trans (Option.some.inj (hf2.symm.trans ((sameValue_eval hL hC hsa).symm.trans ht2)))
      exact ⟨wt', ht2, hv'' ▸ hvs, fun hk => hv'' ▸ hvx hk⟩
    · exact ⟨v', hv', hvs, hvx⟩
  case case6 fuel deep cond K M e c t f hv hk c' K1 M1 hc' hl hg t' K2 M2 ht' f' K3 M3 hf'
      ihc iht ihf =>
    intro hM
    have hK1 := rw_guards fuel deep true sc cnt K M c
    have hK2 := rw_guards fuel deep false sc cnt K1 M1 t
    simp only [hc', ht', hf'] at ihc iht ihf hK1 hK2
    obtain ⟨ihc1, hM1⟩ := ihc hM
    obtain ⟨iht1, hM2⟩ := iht (hM1.congr hK1)
    obtain ⟨ihf1, hM3⟩ := ihf (hM2.congr hK2)
    refine ⟨fun {v} he => ?_, (hM3.congr fun x => ((hK2 x).trans (hK1 x)).symm)⟩
    rw [WPLang.iteView?_eval hv] at he
    obtain ⟨wc, wt, wf, hc, ht, hf, hb, htf, h1, h2⟩ := hL.ite_parts he
    obtain ⟨wc', hc2, hsc, hxc⟩ := ihc1 hc
    obtain ⟨wt', ht2, hst, hxt⟩ := iht1 ht
    obtain ⟨wf', hf2, hsf, hxf⟩ := ihf1 hf
    obtain ⟨v', hv', h1', h2'⟩ := hL.ite_build hc2 ht2 hf2 (hsc.symm.trans hb)
      ((hst.symm.trans htf).trans hsf)
    have hvs : SameTy F v v' := ((ite_sameTy hL hb htf ht h1 h2).trans hst).trans
      (ite_sameTy hL (hsc.symm.trans hb) ((hst.symm.trans htf).trans hsf) ht2 h1' h2').symm
    have hvx : GCons F σ K → v' = v := fun hk => by
      rw [hxc hk] at h1' h2'
      rcases hL.bool_cases hb with rfl | rfl
      · rw [h1' rfl, h1 rfl, hxt (hk.congr hK1)]
      · rw [h2' rfl, h2 rfl, hxf ((hk.congr hK1).congr hK2)]
    split
    · rename_i hsa
      have hv'' : v' = wt' := (hL.bool_cases (hsc.symm.trans hb)).elim h1' fun h =>
        (h2' h).trans (Option.some.inj (hf2.symm.trans ((sameValue_eval hL hC hsa).symm.trans ht2)))
      exact ⟨wt', ht2, hv'' ▸ hvs, fun hk => hv'' ▸ hvx hk⟩
    · exact ⟨v', hv', hvs, hvx⟩
  case case7 fuel deep cond K M e hv y hy r hr =>
    intro hM
    refine ⟨fun {v} he => ?_, hM⟩
    obtain ⟨v0, w, hy0, hw, hs, hx⟩ := cand_sem hL hC hI hr
    obtain rfl : v0 = v := Option.some.inj (hy0.symm.trans ((hL.var e y σ hC hy).symm.trans he))
    split
    · exact ⟨w, hw, hs, hx⟩
    · exact ⟨v0, he, hL.refl he, fun _ => rfl⟩
  case case8 | case10 | case13 =>
    exact fun hM => ⟨fun he => ⟨_, he, hL.refl he, fun _ => rfl⟩, hM⟩
  case case9 fuel deep cond K M e hv y hy hr hK r hm =>
    intro hM
    refine ⟨fun {v} he => ?_, hM⟩
    obtain ⟨v0, w, hy0, hw, hs, hx⟩ := hM y r hm
    obtain rfl : v0 = v := Option.some.inj (hy0.symm.trans ((hL.var e y σ hC hy).symm.trans he))
    exact ⟨w, hw, hs, hx⟩
  case case11 fuel deep cond K M e hv y hy hr hK hm n d hd r K1 M1 hrw ha ih
    | case12 fuel deep cond K M e hv y hy hr hK hm n d hd r K1 M1 hrw ha ih =>
    intro hM
    simp only [wfParam] at hrw ih
    rw [hrw] at ih
    obtain ⟨⟨v0, hy0, hd0⟩, -⟩ := hI.2 y d hd
    obtain ⟨ih1, hM1⟩ := ih hM
    obtain ⟨w, hw, hs, hx⟩ := ih1 hd0
    have hins {o : Option P.Expr} (ho : ∀ r', o = some r' →
        ∃ v w, σ y = some v ∧ P.eval F σ r' = some w ∧ SameTy F v w ∧ (GCons F σ K → w = v)) :
        MemoInv F σ K (M1.insert y o) := fun z r' hz => by
      rw [Std.HashMap.getElem?_insert] at hz
      split at hz
      · obtain rfl : y = z := eq_of_beq ‹_›
        exact ho r' (Option.some.inj hz)
      · exact hM1 z r' hz
    first
    | refine ⟨fun {v} he => ?_, hins fun _ h => Option.some.inj h ▸ ⟨v0, w, hy0, hw, hs, hx⟩⟩
      obtain rfl : v0 = v := Option.some.inj (hy0.symm.trans ((hL.var e y σ hC hy).symm.trans he))
      exact ⟨w, hw, hs, hx⟩
    | exact ⟨fun he => ⟨_, he, hL.refl he, fun _ => rfl⟩, hins fun _ h => by cases h⟩
  case case14 fuel deep cond K M e hv hy =>
    intro hM
    refine ⟨fun {v} he => ?_, hM⟩
    let look : P.Ident → Option P.Expr := fun y => (cand sc K y).filter atomic
    have hlook {k r} (h : look k = some r) : cand sc K k = some r :=
      (Option.filter_eq_some_iff.1 h).1
    let sm := (HasFvars.getFvars e).filterMap fun y => (look y).map (y, ·)
    have hfind : ∀ x ∈ HasFvars.getFvars e, look x = Map.find? sm x :=
      fun x hx => (find?_filterMap look _ x (.inl hx)).symm
    let σs : SemanticStore P := fun k => match look k with
      | some r => P.eval F σ r
      | none => σ k
    have hσs {k} : look k = none → σs k = σ k := fun h => by simp only [σs, h]
    have hσs' {k r} : look k = some r → σs k = P.eval F σ r := fun h => by simp only [σs, h]
    have hCs : WellFormedStore σs F := fun k u hu => by
      cases hk : look k with
      | none => exact hC k u (hσs hk ▸ hu)
      | some r =>
        obtain ⟨v0, w, -, hw, ⟨ty, -, hty⟩, -⟩ := cand_sem hL hC hI (hlook hk)
        exact Option.some.inj (hw.symm.trans ((hσs' hk).symm.trans hu)) ▸
          LawfulHasVal.valueOfTy_isVal _ _ _ hty
    have hsub := hL.subst (σ := σs) (σ' := σ) hC hCs sm e
      (fun k hk r hr => by
        rw [← hfind k hk] at hr
        obtain ⟨v0, w, -, hw, -⟩ := cand_sem hL hC hI (hlook hr)
        rw [hσs' hr, hw]
        exact ⟨rfl, rfl⟩)
      (fun x hx hn => (hσs ((hfind x hx).trans hn)).symm)
    rw [WPLang.substFn_eq e look sm hfind, hsub]
    obtain ⟨v', hv', hs⟩ := hL.retype hC hCs (fun x _ => by
      cases hk : look x with
      | none => exact .inl (hσs hk).symm
      | some r =>
        obtain ⟨v0, w, hy0, hw, hs, -⟩ := cand_sem hL hC hI (hlook hk)
        exact .inr ⟨v0, w, hy0, (hσs' hk).trans hw, hs⟩) he
    refine ⟨v', hv', hs, fun hk => ?_⟩
    have hag : ∀ x ∈ HasFvars.getFvars e, σs x = σ x := fun x _ => by
      cases hx : look x with
      | none => exact hσs hx
      | some r =>
        obtain ⟨v0, w, hy0, hw, -, hx'⟩ := cand_sem hL hC hI (hlook hx)
        rw [hσs' hx, hw, hy0, hx' hk]
    exact Option.some.inj (hv'.symm.trans ((hL.congr e σs σ hCs hC hag).trans he))

omit [LawfulHasVal P] in
/-- **The exact rewrite keeps the value.**  In a well-formed store satisfying the scope
    invariant, the exact rewrite of an assertion's or a cover's condition evaluates as the
    condition. -/
theorem rwExact_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) (hI : ScopeInv F ini σ sc)
    (e : P.Expr) : P.eval F σ (rwExact sc e) = P.eval F σ e := by
  let look : P.Ident → Option P.Expr := fun y => match sc[y]? with
    | some (some d) => if atomic d then some d else none
    | _ => none
  have hlook {k r} (h : look k = some r) : sc[k]? = some (some r) := by
    simp only [look] at h
    split at h <;> try split at h
    all_goals cases h
    assumption
  let sm := (HasFvars.getFvars e).filterMap fun y => (look y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, look x = Map.find? sm x :=
    fun x hx => (find?_filterMap look _ x (.inl hx)).symm
  have h' : P.eval F σ (WPOps.substFn e look) = P.eval F σ e := by
    rw [WPLang.substFn_eq e look sm hfind]
    refine hL.subst hC hC sm e (fun k hk r hr => ?_) fun _ _ _ => rfl
    obtain ⟨⟨v, hv, hrv⟩, -⟩ := hI.2 k r (hlook ((hfind k hk).trans hr))
    exact ⟨by simp [hv], hrv.trans hv.symm⟩
  have hdef : rwExact sc e = match GuardOps.eqView? (WPOps.substFn e look) with
      | some (a, b) =>
        match HasFvar.getFvar a, HasFvar.getFvar b with
        | some x, some x' =>
          if (x == x' && sc.contains x) = true then HasBool.tt else WPOps.substFn e look
        | _, _ => WPOps.substFn e look
      | none => WPOps.substFn e look := rfl
  rw [hdef]
  repeat' split
  all_goals try exact h'
  rename_i hq _ _ x x' hx hx' hxx
  simp only [Bool.and_eq_true, beq_iff_eq] at hxx
  obtain ⟨rfl, hsc⟩ := hxx
  rw [← h', hL.eq_refl hq hx hx' hC (hI.1 x hsc), hL.val.eval_tt σ]

/-! ## Runs of the rewritten list -/

/-- The event `e'` of the rewritten list corresponds to the event `e` of the input: same kind,
    factory, store, label and metadata; an assertion's or a cover's condition evaluates to the
    input's value, an assumption's condition to `true` whenever the input's does. -/
@[expose] def GFEvRel : Event P → Event P → Prop
  | .assert a, .assert b | .cover a, .cover b =>
    b.factory = a.factory ∧ b.store = a.store ∧ b.label = a.label ∧ b.metadata = a.metadata ∧
      P.eval a.factory a.store b.expr = P.eval a.factory a.store a.expr
  | .assume a, .assume b =>
    b.factory = a.factory ∧ b.store = a.store ∧ b.label = a.label ∧ b.metadata = a.metadata ∧
      (P.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) →
        P.eval a.factory a.store b.expr = some (HasBool.ttVal a.factory))
  | _, _ => False

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [BEq P.Ident]
  [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] [GuardOps P] in
/-- An event corresponds to itself. -/
theorem GFEvRel.refl : ∀ e : Event P, GFEvRel e e
  | .assert _ | .cover _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | .assume _ => ⟨rfl, rfl, rfl, rfl, id⟩

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [BEq P.Ident]
  [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] [GuardOps P] in
/-- Corresponding events are counterparts under evaluation to `true`. -/
private theorem GFEvRel.weakensAssume : ∀ {e e' : Event P}, GFEvRel e e' →
    Event.WeakensAssume evalInterp e e'
  | .assert a, .assert b, ⟨hF, hσ, hl, hm, he⟩ | .cover a, .cover b, ⟨hF, hσ, hl, hm, he⟩ =>
    ⟨hl.symm, hm.symm, fun _ => by simp only [evalInterp, hF, hσ, he]⟩
  | .assume a, .assume b, ⟨hF, hσ, hl, hm, he⟩ =>
    ⟨hl.symm, hm.symm, fun _ h => by simp only [evalInterp, hF, hσ] at h ⊢; exact he h⟩
  | .assert _, .assume _, h | .assert _, .cover _, h | .assume _, .assert _, h
  | .assume _, .cover _, h | .cover _, .assert _, h | .cover _, .assume _, h => h.elim

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [BEq P.Ident]
  [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] [GuardOps P] in
/-- Traces corresponding event by event weaken assumptions under evaluation to `true`. -/
theorem GFEvRel.weakensAssumes : ∀ {t t' : Trace P}, List.Rel₂ GFEvRel t t' →
    Trace.WeakensAssumes evalInterp t t'
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h.weakensAssume (GFEvRel.weakensAssumes hs)

omit [HasSubstFvar P] [WPLang P] [LawfulHasVal P] [DecidableEq P.Ident] [HasBool P] [HasFvar P]
  [GuardOps P] in
/-- The scope invariant depends on the scope through its lookups. -/
theorem ScopeInv.congr {sc sc' : Scope P} (hs : ∀ x : P.Ident, sc'[x]? = sc[x]?)
    (h : ScopeInv F ini σ sc) : ScopeInv F ini σ sc' := by
  have hc : ∀ x, sc'.contains x = sc.contains x := fun x => by
    rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?, hs]
  refine ⟨fun x hx => h.1 x (hc x ▸ hx), fun y d hy => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 y d ((hs y).symm.trans hy)
  exact ⟨h1, fun z hz => (h2 z hz).imp_left fun h => (hc z).trans h⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] [Hashable P.Ident]
  [HasSubstFvar P] [WPLang P] [LawfulHasVal P] [HasBool P] [HasFvar P] [GuardOps P] in
/-- A list in passive form starts with a statement in passive form and goes on with a list in
    passive form. -/
theorem passive_cons {s : PStmt P} {rest : PStmts P} (h : Block.passiveForm (s :: rest) = true) :
    Block.passiveForm [s] = true ∧ Block.passiveForm rest = true := by
  rcases s with ((_ | _ | _ | _ | _) | _) | _ | ⟨_ | _⟩ | _ | _ | _
  all_goals simp_all [Block.passiveForm]

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident]
  [HasSubstFvar P] [WPLang P] [LawfulHasVal P] [HasFvars P] [GuardOps P] in
mutual
/-- A run of a list in passive form ends normally and keeps the variables defined at its start. -/
theorem passive_run : ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRun F ss σ evs o → Block.passiveForm ss = true →
    ∃ σ', o = .normal σ' ∧ ∀ x, (σ x).isSome → σ' x = σ x
  | _, _, _, _, .nil, _ => ⟨_, rfl, fun _ _ => rfl⟩
  | _, _, _, _, .cons_normal h1 h2, hp => by
    obtain ⟨σ1, ho1, hk1⟩ := passive_runS h1 (passive_cons hp).1
    cases ho1
    obtain ⟨σ2, rfl, hk2⟩ := passive_run h2 (passive_cons hp).2
    exact ⟨σ2, rfl, fun x hx => (hk2 x (hk1 x hx ▸ hx)).trans (hk1 x hx)⟩
  | _, _, _, _, .cons_exit h1, hp => by
    obtain ⟨σ1, ho1, -⟩ := passive_runS h1 (passive_cons hp).1
    cases ho1
/-- A run of a statement in passive form ends normally and keeps the variables defined at its
    start. -/
private theorem passive_runS : ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRunS F s σ evs o → Block.passiveForm [s] = true →
    ∃ σ', o = .normal σ' ∧ ∀ x, (σ x).isSome → σ' x = σ x
  | _, _, _, _, .cmd (c := .cmd (.init x _ (.det _) _)) h, _ => by
    obtain ⟨v, -, h0, -, hfr, -⟩ := EvalCmdE.init_det_inv h
    exact ⟨_, rfl, fun y hy => hfr y fun hxy => by simp [← hxy, h0] at hy⟩
  | _, _, _, _, .cmd (c := .cmd (.init x _ .nondet _)) h, _ => by
    obtain ⟨v, -, h0, -, hfr, -⟩ := EvalCmdE.init_nondet_inv h
    exact ⟨_, rfl, fun y hy => hfr y fun hxy => by simp [← hxy, h0] at hy⟩
  | _, _, _, _, .cmd (c := .cmd (.set _ _ _)) _, hp => by simp [Block.passiveForm] at hp
  | _, _, _, _, .cmd (c := .cmd (.assume _ _ _)) h, _ =>
    ⟨_, rfl, fun _ _ => congrFun (EvalCmdE.assume_inv h).1 _⟩
  | _, _, _, _, .cmd (c := .cmd (.assert _ _ _)) h, _ =>
    ⟨_, rfl, fun _ _ => congrFun (EvalCmdE.assert_inv h).1 _⟩
  | _, _, _, _, .cmd (c := .cmd (.cover _ _ _)) h, _ =>
    ⟨_, rfl, fun _ _ => congrFun (EvalCmdE.cover_inv h).1 _⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _ => h.elim
  | _, _, _, _, .ite_nondet_true h, hp => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.1
    exact ⟨_, rfl, fun x _ => congrFun (projectStore_keep hk) x⟩
  | _, _, _, _, .ite_nondet_false h, hp => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.2
    exact ⟨_, rfl, fun x _ => congrFun (projectStore_keep hk) x⟩
  | _, _, _, _, .ite_true _ _, hp | _, _, _, _, .ite_false _ _, hp | _, _, _, _, .block _, hp
  | _, _, _, _, .exit, hp | _, _, _, _, .typeDecl, hp | _, _, _, _, .loop_exit _, hp
  | _, _, _, _, .loop_iter _ _ _, hp | _, _, _, _, .loop_break _ _, hp => by
    simp [Block.passiveForm] at hp
end

omit [HasSubstFvar P] [WPLang P] [HasFvar P] [LawfulHasVal P] [GuardOps P] in
/-- **The scope invariant after an `init`.**  The `init` of the undefined `x`, a name some `init`
    of the list defines, to the value `v` keeps the invariant, with `x` entered in the scope with an
    entry whose expression has the value `v` and free variables in the scope or defined by no
    `init` of the list. -/
theorem ScopeInv.push (hcong : WellFormedSemanticEvalExprCongr (P := P) F)
    (hI : ScopeInv F ini σ sc) (hC : WellFormedStore σ F) {σ1 : SemanticStore P} {x : P.Ident}
    {v : P.Val} {val : Option P.Expr} (h0 : σ x = none) (h1 : σ1 x = some v)
    (hfr : ∀ y, x ≠ y → σ1 y = σ y) (hv : HasVal.value F v) (hx : ini.contains x = true)
    (hval : ∀ d, val = some d → P.eval F σ d = some v ∧
      ∀ z ∈ HasFvars.getFvars d, sc.contains z = true ∨ ini.contains z = false) :
    WellFormedStore σ1 F ∧ ScopeInv F ini σ1 (sc.insert x val) := by
  have hC1 : WellFormedStore σ1 F := fun y w hy => by
    rcases Classical.em (x = y) with rfl | hxy
    · exact Option.some.inj (h1.symm.trans hy) ▸ hv
    · exact hC y w ((hfr y hxy).symm.trans hy)
  have hne {z} (hz : sc.contains z = true ∨ ini.contains z = false) : x ≠ z := by
    rintro rfl
    exact hz.elim (fun hz => by simpa [h0] using hI.1 x hz) fun hz => by simp [hx] at hz
  have hag {d} (hd : ∀ z ∈ HasFvars.getFvars d, sc.contains z = true ∨ ini.contains z = false) :
      P.eval F σ1 d = P.eval F σ d :=
    hcong d σ1 σ hC1 hC fun z hz => hfr z (hne (hd z hz))
  refine ⟨hC1, fun z hz => ?_, fun y d hy => ?_⟩
  · by_cases hxz : x = z
    · simp [← hxz, h1]
    · exact hfr z hxz ▸ hI.1 z (by simpa [Std.HashMap.contains_insert, hxz] using hz)
  · rw [Std.HashMap.getElem?_insert] at hy
    split at hy
    · obtain rfl : x = y := eq_of_beq ‹_›
      obtain ⟨hev, hfv⟩ := hval d (Option.some.inj hy)
      exact ⟨⟨v, h1, (hag hfv).trans hev⟩, fun z hz =>
        (hfv z hz).imp_left fun h => by simp [Std.HashMap.contains_insert, h]⟩
    · rename_i hxy
      obtain ⟨⟨w, hw, hdw⟩, hfv⟩ := hI.2 y d hy
      refine ⟨⟨w, (hfr y (by simpa using hxy)).trans hw, (hag hfv).trans hdw⟩, fun z hz =>
        (hfv z hz).imp_left fun h => by simp [Std.HashMap.contains_insert, h]⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] [Hashable P.Ident]
  [HasSubstFvar P] [WPLang P] [LawfulHasVal P] [GuardOps P] in
/-- An `init` step replayed with a right-hand side of the same value. -/
theorem evalE_init_replay {σ σ1 : SemanticStore P} {x : P.Ident} {ty : P.Ty} {e e' : P.Expr}
    {md : MetaData P} {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty (.det e) md)) σ1 evs)
    (he : P.eval F σ e' = P.eval F σ e) : EvalE F σ (.cmd (.init x ty (.det e') md)) σ1 evs :=
  match h with | .eval_init hev hinit hty hvar => .eval_init (he.trans hev) hinit hty hvar

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
mutual
/-- **A run of a list, replayed on its rewrite.**  A run of a list in passive form from a
    well-formed store satisfying the scope invariant has a run of the rewritten list from the same
    store with the same outcome and corresponding events. -/
private theorem gf_run [LawfulBEq P.Ident] [LawfulHasVal P] (hL : GuardFwdLaws F) (cx : Ctx P) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRun F ss σ evs o → ∀ {st : GSt P}, Block.passiveForm ss = true →
    (∀ x ∈ Block.assignedVars ss, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope →
    ∃ evs', BRun F (walk cx st ss).1 σ evs' o ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, _, .nil, _, _, _, _, _ => ⟨[], .nil, .nil⟩
  | _, _, _, _, .cons_normal h1 h2, st, hp, hini, hC, hI => by
    have hini' := fun x hx => hini x (List.mem_append_left _ hx)
    obtain ⟨evs1, h1', hr1, hpost⟩ := gf_runS hL cx h1 (passive_cons hp).1 hini' hC hI
    obtain ⟨hC1, hI1⟩ := hpost _ rfl
    obtain ⟨evs2, h2', hr2⟩ := gf_run hL cx h2 (passive_cons hp).2
      (fun x hx => hini x (List.mem_append_right _ hx)) hC1 hI1
    exact ⟨evs1 ++ evs2, .cons_normal h1' h2', hr1.append hr2⟩
  | _, _, _, _, .cons_exit h1, st, hp, hini, hC, hI => by
    obtain ⟨evs1, h1', hr1, -⟩ := gf_runS hL cx h1 (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hC hI
    exact ⟨evs1, .cons_exit h1', hr1⟩
/-- **A run of a statement, replayed on its rewrite**: `gf_run` for one statement, and the store
    after it satisfies the scope invariant for the state after the walk over it. -/
private theorem gf_runS [LawfulBEq P.Ident] [LawfulHasVal P] (hL : GuardFwdLaws F) (cx : Ctx P) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {st : GSt P}, Block.passiveForm [s] = true →
    (∀ x ∈ Stmt.assignedVars s, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope →
    ∃ evs', BRunS F (walkS cx st s).1 σ evs' o ∧ List.Rel₂ GFEvRel evs evs' ∧
      ∀ σ', o = .normal σ' → WellFormedStore σ' F ∧ ScopeInv F cx.ini σ' (walkS cx st s).2.scope
  | _, _, _, _, .cmd (c := .cmd (.init x ty (.det e) md)) h, st, _, hini, hC, hI => by
    obtain ⟨v, hev, h0, h1, hfr, rfl, hty⟩ := EvalCmdE.init_det_inv h
    obtain ⟨v', hev', -, hx⟩ :=
      (rw_sem hL hC hI (initFuel cx st x) false false cx.cnt ∅ ∅ e MemoInv.empty).1 hev
    obtain rfl := hx GCons.empty
    refine ⟨[], .cmd (evalE_init_replay h (hev'.trans hev.symm)), .nil, fun σ' ho => ?_⟩
    cases ho
    refine hI.push hL.congr hC h0 h1 hfr (LawfulHasVal.valueOfTy_isVal _ _ _ hty)
      (hini x (by simp [Stmt.assignedVars])) fun d hd => ?_
    split at hd <;> cases hd
    rename_i hrec
    simp only [recordable, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hrec
    exact ⟨hev', hrec⟩
  | _, _, _, _, .cmd (c := .cmd (.init x ty .nondet md)) h, st, _, hini, hC, hI => by
    obtain ⟨v, hty, h0, h1, hfr, rfl⟩ := EvalCmdE.init_nondet_inv h
    refine ⟨[], .cmd h, .nil, fun σ' ho => ?_⟩
    cases ho
    exact hI.push hL.congr hC h0 h1 hfr (LawfulHasVal.valueOfTy_isVal _ _ _ hty)
      (hini x (by simp [Stmt.assignedVars])) fun _ hd => by cases hd
  | _, _, _, _, .cmd (c := .cmd (.assume l e md)) h, st, _, _, hC, hI => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assume_inv h
    refine ⟨_, .cmd .eval_assume, .cons ⟨rfl, rfl, rfl, rfl, fun he => ?_⟩ .nil,
      fun σ' ho => by cases ho; exact ⟨hC, hI⟩⟩
    obtain ⟨v', hev', -, hx⟩ :=
      (rw_sem hL hC hI st.trailLen false false cx.cnt ∅ ∅ e MemoInv.empty).1 he
    exact (hx GCons.empty) ▸ hev'
  | _, _, _, _, .cmd (c := .cmd (.assert l e md)) h, st, _, _, hC, hI => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assert_inv h
    exact ⟨_, .cmd .eval_assert, .cons ⟨rfl, rfl, rfl, rfl, rwExact_sem hL hC hI e⟩ .nil,
      fun σ' ho => by cases ho; exact ⟨hC, hI⟩⟩
  | _, _, _, _, .cmd (c := .cmd (.cover l e md)) h, st, _, _, hC, hI => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.cover_inv h
    exact ⟨_, .cmd .eval_cover, .cons ⟨rfl, rfl, rfl, rfl, rwExact_sem hL hC hI e⟩ .nil,
      fun σ' ho => by cases ho; exact ⟨hC, hI⟩⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _, _, _, _, _ => h.elim
  | _, σ, _, _, .ite_nondet_true (tss := tss) (ess := ess) (md := md) h, st, hp, hini, hC, hI => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := gf_run hL cx h hp.1.1
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC hI
    refine ⟨evs', .ite_nondet_true h', hr, fun σ' ho => ?_⟩
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.1
    cases ho
    rw [projectStore_keep hk]
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st tss).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame cx _ ess)).undo
    exact ⟨hC, hI.congr s2⟩
  | _, σ, _, _, .ite_nondet_false (tss := tss) (ess := ess) (md := md) h, st, hp, hini, hC, hI => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st tss).undo
    obtain ⟨evs', h', hr⟩ := gf_run hL cx h (st := (walk cx st tss).2.undoTo st.trailLen) hp.1.2
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC (hI.congr s1)
    refine ⟨evs', .ite_nondet_false h', hr, fun σ' ho => ?_⟩
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.2
    cases ho
    rw [projectStore_keep hk]
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame cx _ ess)).undo
    exact ⟨hC, hI.congr s2⟩
  | _, _, _, _, .cmd (c := .cmd (.set _ _ _)) _, _, hp, _, _, _
  | _, _, _, _, .ite_true _ _, _, hp, _, _, _ | _, _, _, _, .ite_false _ _, _, hp, _, _, _
  | _, _, _, _, .block _, _, hp, _, _, _ | _, _, _, _, .exit, _, hp, _, _, _
  | _, _, _, _, .typeDecl, _, hp, _, _, _ | _, _, _, _, .loop_exit _, _, hp, _, _, _
  | _, _, _, _, .loop_iter _ _ _, _, hp, _, _, _ | _, _, _, _, .loop_break _ _, _, hp, _, _, _ => by
    simp [Block.passiveForm] at hp
end

mutual
/-- **A reach of a list, replayed on its rewrite.**  A reach of a list in passive form from a
    well-formed store satisfying the scope invariant has a reach of the rewritten list from the
    same store with corresponding events. -/
private theorem gf_reach (hL : GuardFwdLaws F) (cx : Ctx P) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)},
    BReach F ss σ evs → ∀ {st : GSt P}, Block.passiveForm ss = true →
    (∀ x ∈ Block.assignedVars ss, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope →
    ∃ evs', BReach F (walk cx st ss).1 σ evs' ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, .here h, st, hp, hini, hC, hI => by
    obtain ⟨evs', h', hr⟩ := gf_reachS hL cx h (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hC hI
    exact ⟨evs', .here h', hr⟩
  | _, _, _, .later h1 h2, st, hp, hini, hC, hI => by
    obtain ⟨evs1, h1', hr1, hpost⟩ := gf_runS hL cx h1 (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hC hI
    obtain ⟨hC1, hI1⟩ := hpost _ rfl
    obtain ⟨evs2, h2', hr2⟩ := gf_reach hL cx h2 (passive_cons hp).2
      (fun x hx => hini x (List.mem_append_right _ hx)) hC1 hI1
    exact ⟨evs1 ++ evs2, .later h1' h2', hr1.append hr2⟩
/-- **A reach of a statement, replayed on its rewrite**: `gf_reach` for one statement. -/
private theorem gf_reachS (hL : GuardFwdLaws F) (cx : Ctx P) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {st : GSt P}, Block.passiveForm [s] = true →
    (∀ x ∈ Stmt.assignedVars s, cx.ini.contains x = true) → WellFormedStore σ F →
    ScopeInv F cx.ini σ st.scope →
    ∃ evs', BReachS F (walkS cx st s).1 σ evs' ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, .cmd (c := c) h hne, st, hp, hini, hC, hI => by
    obtain ⟨evs', h', hr, -⟩ := gf_runS hL cx (.cmd h) hp hini hC hI
    obtain ⟨c', hc'⟩ : ∃ c', (walkS cx st (.cmd c)).1 = .cmd c' := by
      rcases c with ((_ | _ | _ | _ | _) | _)
      all_goals first | exact ⟨_, rfl⟩ | (rename_i e _; cases e <;> exact ⟨_, rfl⟩)
    rw [hc'] at h' ⊢
    cases h' with
    | cmd h' => exact ⟨evs', .cmd h' fun h0 => hne (by subst h0; cases hr; rfl), hr⟩
  | _, _, _, .ite_nondet_true (tss := tss) h, st, hp, hini, hC, hI => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := gf_reach hL cx h hp.1.1
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC hI
    exact ⟨evs', .ite_nondet_true h', hr⟩
  | _, _, _, .ite_nondet_false (tss := tss) h, st, hp, hini, hC, hI => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st tss).undo
    obtain ⟨evs', h', hr⟩ := gf_reach hL cx h (st := (walk cx st tss).2.undoTo st.trailLen)
      hp.1.2 (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hC (hI.congr s1)
    exact ⟨evs', .ite_nondet_false h', hr⟩
  | _, _, _, .ite_true _ _, _, hp, _, _, _ | _, _, _, .ite_false _ _, _, hp, _, _, _
  | _, _, _, .block _, _, hp, _, _, _ | _, _, _, .loop_here _ _, _, hp, _, _, _
  | _, _, _, .loop_later _ _ _, _, hp, _, _, _ => by simp [Block.passiveForm] at hp
end

omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [LawfulHasVal P] [GuardOps P] in
/-- The context guard forwarding computes for a list. -/
private theorem guardFwd_ctx (ss : PStmts P) :
    ∀ x ∈ Block.assignedVars ss,
      (Std.HashSet.ofList (Block.assignedVarsH ss)).contains x = true := fun x hx => by
  simpa [Std.HashSet.contains_ofList, Block.assignedVarsH_eq] using hx

/-- **A run of a list, and of its guard forwarding.**  A run of a list in passive form from a
    well-formed store has a run of `guardFwd ss` from the same store with the same outcome, whose
    events correspond to it one by one (`GFEvRel`), for a factory satisfying `GuardFwdLaws`. -/
theorem guardFwd_run_rel (hL : GuardFwdLaws F) {ss : PStmts P} (hp : Block.passiveForm ss = true)
    {evs : List (Event P)} {o : Outcome P} (hC : WellFormedStore σ F) (h : BRun F ss σ evs o) :
    ∃ evs', BRun F (guardFwd ss) σ evs' o ∧ List.Rel₂ GFEvRel evs evs' :=
  gf_run hL _ h hp (guardFwd_ctx ss) hC scopeInv_empty

/-- **A reach of a list, and of its guard forwarding.**  A reach of a list in passive form from a
    well-formed store has a reach of `guardFwd ss` from the same store whose events correspond to
    it one by one (`GFEvRel`), for a factory satisfying `GuardFwdLaws`. -/
theorem guardFwd_reach_rel (hL : GuardFwdLaws F) {ss : PStmts P}
    (hp : Block.passiveForm ss = true) {evs : List (Event P)} (hC : WellFormedStore σ F)
    (h : BReach F ss σ evs) :
    ∃ evs', BReach F (guardFwd ss) σ evs' ∧ List.Rel₂ GFEvRel evs evs' :=
  gf_reach hL _ h hp (guardFwd_ctx ss) hC scopeInv_empty

end -- public section

end GuardFwd
end Imperative
