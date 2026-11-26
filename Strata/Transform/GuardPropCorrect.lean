/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardProp
public import Strata.Transform.GuardFwdCorrect
public import Strata.Transform.GuardPropProps

/-! # Guard propagation keeps every run

The run of a statement list rewritten by guard propagation follows the run of the input: every
statement steps as the input's does, and the events of the two runs correspond
(`Trace.KeepsWhileAssumed`): same kind, label and metadata, and, as long as every assumption
before an event holds, a condition that holds exactly when the input's does
(`guardProp_run_rel`, `guardProp_reach_rel`).  So every assertion of the input that fails after
assumptions that hold has a counterpart in the output that fails after assumptions that hold
(`Trace.KeepsWhileAssumed.assertValid_reflect`).

The simulation runs the rewritten list from any store that *follows* the input's (`Follows`):
one that holds, for every variable, the input's value or a value of its type; the stores are
equal while every assumption holds.

Two expressions are *sort-equivalent* in a store (`SortEq`) when each has a value exactly when the
other has one, the two values of a common type.  In a well-formed store satisfying the scope
invariant of guard forwarding (`GuardFwd.ScopeInv`), whose guards known in the guard map are
Boolean-valued (`KBool`), contextual simplification gives a sort-equivalent expression, and one
with the input's value when the guard map holds (`rwG_sem`).  At the root of a subterm the
replacement of each variable has a value of the type of the variable's value, and that value
when the guard map holds (`look_sem`), so the substitution evaluates as the subterm in a store
whose values have the same types (`substFn_sem`).  Under strict evaluation a conditional has a
value only when both arms do, so an arm rewritten under the guard value the store does not give
must keep a value of the same type, not the same value (`ite_rel`).

The facts of a position name variables of type `bool` defined earlier on the path, so they have
Boolean values (`WInv.kBool`), and they hold in the store when every assumption before the
position held: a fact enters the map after an assumption that holds and states it
(`factOf_sem`), and its variable keeps its value until the end of its scope.

These are the run and reach relations of guard propagation, not a correctness theorem of their
own: the trace over-approximation built from them is stated with `OverapproximatesTracesUptoWhen`
(`Core.GuardProp.guardProp_overapproximatesTraces`, in `Strata.Transform.GuardPropCoreCorrect`).

Key theorems: `rwG_sem`, `Trace.KeepsWhileAssumed.assertValid_reflect`, `guardProp_run_rel`,
`guardProp_reach_rel`.

Key definitions: `SortEq`, `KBool`, `WInv`, `Follows`, `Held`, `Trace.KeepsWhileAssumed`. -/

namespace Imperative
namespace GuardProp

open WP BigStep GuardFwd

public section

variable {P : PureExpr}

/-! ## The trace relation -/

section Trace

variable [HasBool P]

/-- The condition of the event argument `a` evaluates to `true`. -/
@[expose] def Held (a : EventArg P) : Prop :=
  P.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory)

/-- `target` corresponds to `source` event by event, as long as the assumptions of `source` hold:
    each event keeps its kind, label and metadata, and its condition holds exactly when the
    source's does; after an assumption of `source` that does not hold, the rest of the two
    traces is unconstrained. -/
inductive Trace.KeepsWhileAssumed : Trace P → Trace P → Prop where
  | nil : Trace.KeepsWhileAssumed [] []
  | assume {a a' : EventArg P} {t t' : Trace P} : a'.label = a.label →
      a'.metadata = a.metadata → (Held a' ↔ Held a) → (Held a → Trace.KeepsWhileAssumed t t') →
      Trace.KeepsWhileAssumed (.assume a :: t) (.assume a' :: t')
  | assert {a a' : EventArg P} {t t' : Trace P} : a'.label = a.label →
      a'.metadata = a.metadata → (Held a' ↔ Held a) → Trace.KeepsWhileAssumed t t' →
      Trace.KeepsWhileAssumed (.assert a :: t) (.assert a' :: t')
  | cover {a a' : EventArg P} {t t' : Trace P} : a'.label = a.label →
      a'.metadata = a.metadata → (Held a' ↔ Held a) → Trace.KeepsWhileAssumed t t' →
      Trace.KeepsWhileAssumed (.cover a :: t) (.cover a' :: t')

/-- Every assumption of the trace holds. -/
@[expose] def AllHeld (t : Trace P) : Prop := ∀ a, Event.assume a ∈ t → Held a

/-- **Concatenation.**  Two pairs of corresponding traces, the second corresponding whenever every
    assumption of the first source holds, concatenate to corresponding traces. -/
theorem Trace.KeepsWhileAssumed.append {t₁ t₁' t₂ t₂' : Trace P}
    (h₁ : Trace.KeepsWhileAssumed t₁ t₁') (h₂ : AllHeld t₁ → Trace.KeepsWhileAssumed t₂ t₂') :
    Trace.KeepsWhileAssumed (t₁ ++ t₂) (t₁' ++ t₂') := by
  induction h₁ with
  | nil => exact h₂ nofun
  | assume hl hm hh _ ih =>
    exact .assume hl hm hh fun ha => ih ha fun ha' => h₂ fun b hb =>
      (List.mem_cons.1 hb).elim (fun h => Event.assume.inj h ▸ ha) (ha' b)
  | assert hl hm hh _ ih =>
    exact .assert hl hm hh (ih fun ha => h₂ fun b hb => ha b (by simpa using hb))
  | cover hl hm hh _ ih =>
    exact .cover hl hm hh (ih fun ha => h₂ fun b hb => ha b (by simpa using hb))

omit [HasBool P] in
/-- After assumptions one of which holds in no world, every assertion of a trace is valid. -/
private theorem validFrom_of_failed {I : ConditionInterp P} {keep : EventArg P → Prop}
    {a : EventArg P} (hn : ∀ w, ¬ I.holds w a) :
    ∀ (t A : Trace P), Event.assume a ∈ A → Trace.AssertionsValidFromP P I keep A t
  | [], _, _ => trivial
  | .assume c :: t, A, hA =>
    validFrom_of_failed hn t (A ++ [.assume c]) (List.mem_append_left _ hA)
  | .assert _ :: t, A, hA =>
    ⟨fun _ w hw => absurd (hw a hA) (hn w), validFrom_of_failed hn t A hA⟩
  | .cover _ :: t, A, hA => validFrom_of_failed hn t A hA

/-- The worker of `assertValid_reflect`, with the assumptions accumulated before the traces. -/
private theorem keeps_reflectFrom {aid : AssertId P} :
    ∀ {t t' : Trace P}, Trace.KeepsWhileAssumed t t' → ∀ (A A' : Trace P),
    (∀ w, Trace.AssumptionsHold P evalInterp w A → Trace.AssumptionsHold P evalInterp w A') →
    Trace.AssertionValidFrom P evalInterp aid A' t' →
    Trace.AssertionValidFrom P evalInterp aid A t
  | _, _, .nil, _, _, _, _ => trivial
  | _, _, .assume (a := a) (a' := a') _ _ hh ht, A, A', hA, h => by
    by_cases ha : Held a
    · refine keeps_reflectFrom (ht ha) (A ++ [.assume a]) (A' ++ [.assume a'])
        (fun w hw c hc => (List.mem_append.1 hc).elim
          (hA w (fun d hd => hw d (List.mem_append_left _ hd)) c)
          fun hc => Event.assume.inj (List.mem_singleton.1 hc) ▸ hh.2 ha) h
    · exact validFrom_of_failed (I := evalInterp) (a := a) (fun _ h => ha h) _ (A ++ [.assume a])
        (List.mem_append_right _ (List.mem_singleton_self _))
  | _, _, .assert (a := a) (a' := a') hl hm hh ht, A, A', hA, ⟨h1, h2⟩ =>
    ⟨fun hk w hw => hh.1 (h1 ⟨hl.trans hk.1, hm.trans hk.2⟩ w (hA w hw)),
      keeps_reflectFrom ht A A' hA h2⟩
  | _, _, .cover _ _ _ ht, A, A', hA, h => keeps_reflectFrom ht A A' hA h

/-- **Corresponding traces reflect assertion validity**: if every occurrence of `aid` in `t'`
    holds whenever the assumptions before it do, so does every occurrence in `t`, when `t'`
    corresponds to `t` while the assumptions of `t` hold (`Trace.KeepsWhileAssumed`). -/
theorem Trace.KeepsWhileAssumed.assertValid_reflect {aid : AssertId P} {t t' : Trace P}
    (h : Trace.KeepsWhileAssumed t t') :
    Trace.AssertionValid P evalInterp aid t' → Trace.AssertionValid P evalInterp aid t :=
  keeps_reflectFrom h [] [] fun _ hw => hw

end Trace

/-! ## The rewrite of an expression -/

variable [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [GuardOps P] [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P]

variable {F : P.Factory} {ini : Std.HashSet P.Ident} {σ : SemanticStore P} {sc : Scope P}

/-- The value of the Boolean literal of `b`. -/
@[expose] def boolV (F : P.Factory) (b : Bool) : P.Val :=
  if b then HasBool.ttVal F else HasBool.ffVal F

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- The Boolean literal of `b` evaluates to the value of `b`. -/
theorem eval_boolE (hL : GuardFwdLaws F) (b : Bool) : P.eval F σ (boolE b) = some (boolV F b) := by
  cases b
  · exact hL.val.eval_ff σ
  · exact hL.val.eval_tt σ

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- The value of a Boolean literal is of the Boolean type. -/
theorem boolV_sameTy (b : Bool) : SameTy F (boolV F b) (HasBool.ttVal F) := by
  cases b
  · exact ⟨_, (HasBool.boolIsValOfTy F).2, (HasBool.boolIsValOfTy F).1⟩
  · exact ⟨_, (HasBool.boolIsValOfTy F).1, (HasBool.boolIsValOfTy F).1⟩

/-- The expressions `e` and `e'` are *sort-equivalent* in `σ`: each has a value exactly when the
    other has one, the two values of a common type. -/
@[expose] def SortEq (F : P.Factory) (σ : SemanticStore P) (e e' : P.Expr) : Prop :=
  (∀ v, P.eval F σ e = some v → ∃ v', P.eval F σ e' = some v' ∧ SameTy F v v') ∧
    ∀ v', P.eval F σ e' = some v' → ∃ v, P.eval F σ e = some v ∧ SameTy F v v'

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [LawfulBEq P.Ident] [LawfulHasVal P] [BEq P.Ident] [Hashable P.Ident] in
/-- **The conclusion of `rwG_sem` transports along an expression with the same value.**  Both
    conjuncts are stated through `P.eval F σ` of the input, so an input replaced by an expression
    with the same value leaves them unchanged.  This is what carries the conclusion from a
    conditional recognized by `iteView?` to the canonical conditional of its parts, whose root
    source location may differ. -/
private theorem rwG_goal_congr {C : Prop} {e e' x : P.Expr}
    (h : P.eval F σ e = P.eval F σ e') :
    (SortEq F σ e' x ∧ (C → P.eval F σ x = P.eval F σ e')) ↔
      (SortEq F σ e x ∧ (C → P.eval F σ x = P.eval F σ e)) := by
  simp only [SortEq, h]

/-- Every guard known in `K` has a Boolean value in `σ`. -/
@[expose] def KBool (F : P.Factory) (σ : SemanticStore P) (K : Guards P) : Prop :=
  ∀ g b, K[g]? = some b → ∃ w, σ g = some w ∧ SameTy F w (HasBool.ttVal F)

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [LawfulBEq P.Ident] [LawfulHasVal P] in
/-- A guard map that holds has Boolean values. -/
theorem GCons.kBool {K : Guards P} (h : GCons F σ K) : KBool F σ K :=
  fun g b hg => ⟨_, h g b hg, boolV_sameTy b⟩

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [LawfulHasVal P] in
/-- A guard map with Boolean values, extended by a guard with a Boolean value, has Boolean
    values. -/
theorem KBool.insert {K : Guards P} (h : KBool F σ K) {g : P.Ident} {w : P.Val} (b : Bool)
    (hg : σ g = some w) (hw : SameTy F w (HasBool.ttVal F)) : KBool F σ (K.insert g b) :=
  fun g' b' h' => by
    rw [Std.HashMap.getElem?_insert] at h'
    split at h'
    · exact eq_of_beq ‹_› ▸ ⟨w, hg, hw⟩
    · exact h g' b' h'

omit [LawfulBEq P.Ident] in
/-- **The replacement of a variable** has a value of the type of the variable's value, and that
    value when the guard map holds. -/
theorem look_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) (hI : ScopeInv F ini σ sc)
    {K : Guards P} (hK : KBool F σ K) :
    ∀ (n : Nat) (y : P.Ident) (r : P.Expr), look sc K n y = some r →
      ∃ v w, σ y = some v ∧ P.eval F σ r = some w ∧ SameTy F v w ∧ (GCons F σ K → w = v)
  | n, y, r, h => by
    unfold look at h
    split at h
    · rename_i b hb
      cases h
      obtain ⟨w, hw, hwt⟩ := hK y b hb
      exact ⟨w, _, hw, eval_boolE hL b, hwt.trans (boolV_sameTy b).symm,
        fun hg => Option.some.inj ((hg y b hb).symm.trans hw)⟩
    split at h <;> try cases h
    rename_i r0 hr0
    obtain ⟨v, w, hy, hw, hs, hx⟩ := cand_sem hL hC hI (Option.filter_eq_some_iff.1 hr0).1
    split at h
    · rename_i n z hz
      cases h
      have hzw : σ z = some w := (hL.var r0 z σ hC hz).symm.trans hw
      cases hl : look sc K n z with
      | none => exact ⟨v, w, hy, hw, hs, hx⟩
      | some r' =>
        obtain ⟨vz, wz, hz', hwz, hsz, hxz⟩ := look_sem hL hC hI hK n z r' hl
        obtain rfl : vz = w := Option.some.inj (hz'.symm.trans hzw)
        exact ⟨v, wz, hy, hwz, hs.trans hsz, fun hg => (hxz hg).trans (hx hg)⟩
    · exact Option.some.inj h ▸ ⟨v, w, hy, hw, hs, hx⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] in
/-- **Substitution by replacements.**  Substituting each free variable by an expression with a
    value of the type of the variable's value gives a sort-equivalent expression, and one with
    the input's value when each replacement has the variable's value (under `C`). -/
theorem substFn_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) {C : Prop}
    {lk : P.Ident → Option P.Expr}
    (hlk : ∀ k r, lk k = some r →
      ∃ v w, σ k = some v ∧ P.eval F σ r = some w ∧ SameTy F v w ∧ (C → w = v))
    (e : P.Expr) :
    SortEq F σ e (WPOps.substFn e lk) ∧
      (C → P.eval F σ (WPOps.substFn e lk) = P.eval F σ e) := by
  let sm := (HasFvars.getFvars e).filterMap fun y => (lk y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, lk x = Map.find? sm x :=
    fun x hx => (find?_filterMap lk _ x (.inl hx)).symm
  let σs : SemanticStore P := fun k => match lk k with
    | some r => P.eval F σ r
    | none => σ k
  have hσs {k} : lk k = none → σs k = σ k := fun h => by simp only [σs, h]
  have hσs' {k r} : lk k = some r → σs k = P.eval F σ r := fun h => by simp only [σs, h]
  have hCs : WellFormedStore σs F := fun k u hu => by
    cases hk : lk k with
    | none => exact hC k u (hσs hk ▸ hu)
    | some r =>
      obtain ⟨-, w, -, hw, ⟨ty, -, hty⟩, -⟩ := hlk k r hk
      rw [hσs' hk, hw] at hu
      cases hu
      exact LawfulHasVal.valueOfTy_isVal _ _ _ hty
  have hsub := hL.subst (σ := σs) (σ' := σ) hC hCs sm e
    (fun k hk r hr => by
      rw [← hfind k hk] at hr
      obtain ⟨-, w, -, hw, -⟩ := hlk k r hr
      rw [hσs' hr, hw]
      exact ⟨rfl, rfl⟩)
    (fun x hx hn => (hσs ((hfind x hx).trans hn)).symm)
  have hst : ∀ x ∈ HasFvars.getFvars e, SameTyO F (σ x) (σs x) := fun x _ => by
    cases hk : lk x with
    | none => exact .inl (hσs hk).symm
    | some r =>
      obtain ⟨v, w, hy, hw, hs, -⟩ := hlk x r hk
      exact .inr ⟨v, w, hy, (hσs' hk).trans hw, hs⟩
  unfold SortEq
  rw [WPLang.substFn_eq e lk sm hfind, hsub]
  refine ⟨⟨fun v he => hL.retype hC hCs hst he, fun v' he => ?_⟩, fun hc => ?_⟩
  · obtain ⟨v, hv, hs⟩ := hL.retype hCs hC (fun x hx => (hst x hx).elim (fun h => .inl h.symm)
      fun ⟨a, b, ha, hb, hab⟩ => .inr ⟨b, a, hb, ha, hab.symm⟩) he
    exact ⟨v, hv, hs.symm⟩
  · refine hL.congr e σs σ hCs hC fun x _ => ?_
    cases hx : lk x with
    | none => exact hσs hx
    | some r => exact (hlk x r hx).elim fun _ ⟨_, hy, hw, _, hx'⟩ => by rw [hσs' hx, hw, hy, hx' hc]

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] in
/-- **The conditional of rewritten parts.**  A conditional whose condition is rewritten to a
    sort-equivalent one, with the input's value under `C`, and whose arms are rewritten, wherever
    the rewritten condition has a Boolean value, to sort-equivalent arms with the input's values
    under `C` for the arm that value selects, is sort-equivalent to the input, with the input's
    value under `C`. -/
theorem ite_rel (hL : GuardFwdLaws F) {C : Prop} {c t f c' t' f' : P.Expr}
    (hc : SortEq F σ c c') (hce : C → P.eval F σ c' = P.eval F σ c)
    (harm : ∀ wc, P.eval F σ c' = some wc → SameTy F wc (HasBool.ttVal F) →
      SortEq F σ t t' ∧ SortEq F σ f f' ∧
        (C → wc = HasBool.ttVal F → P.eval F σ t' = P.eval F σ t) ∧
        (C → wc = HasBool.ffVal F → P.eval F σ f' = P.eval F σ f)) :
    SortEq F σ (WPOps.ite c t f) (WPOps.ite c' t' f') ∧
      (C → P.eval F σ (WPOps.ite c' t' f') = P.eval F σ (WPOps.ite c t f)) := by
  have fwd : ∀ v, P.eval F σ (WPOps.ite c t f) = some v → ∃ v',
      P.eval F σ (WPOps.ite c' t' f') = some v' ∧ SameTy F v v' ∧ (C → v' = v) := by
    intro v he
    obtain ⟨wc, wt, wf, hc0, ht, hf, hb, htf, h1, h2⟩ := hL.ite_parts he
    obtain ⟨wc', hc2, hsc⟩ := hc.1 wc hc0
    have hb' : SameTy F wc' (HasBool.ttVal F) := hsc.symm.trans hb
    obtain ⟨ht', hf', hxt, hxf⟩ := harm wc' hc2 hb'
    obtain ⟨wt', ht2, hst⟩ := ht'.1 wt ht
    obtain ⟨wf', hf2, hsf⟩ := hf'.1 wf hf
    obtain ⟨v', hv', h1', h2'⟩ := hL.ite_build hc2 ht2 hf2 hb' ((hst.symm.trans htf).trans hsf)
    refine ⟨v', hv', ((ite_sameTy hL hb htf ht h1 h2).trans hst).trans
      (ite_sameTy hL hb' ((hst.symm.trans htf).trans hsf) ht2 h1' h2').symm, fun hC0 => ?_⟩
    obtain rfl : wc' = wc := Option.some.inj (hc2.symm.trans ((hce hC0).trans hc0))
    rcases hL.bool_cases hb with h | h
    · rw [h1' h, h1 h]
      exact Option.some.inj (ht2.symm.trans ((hxt hC0 h).trans ht))
    · rw [h2' h, h2 h]
      exact Option.some.inj (hf2.symm.trans ((hxf hC0 h).trans hf))
  have bwd : ∀ v', P.eval F σ (WPOps.ite c' t' f') = some v' → ∃ v,
      P.eval F σ (WPOps.ite c t f) = some v ∧ SameTy F v v' := by
    intro v' he
    obtain ⟨wc', wt', wf', hc2, ht2, hf2, hb', htf', h1', h2'⟩ := hL.ite_parts he
    obtain ⟨ht', hf', -, -⟩ := harm wc' hc2 hb'
    obtain ⟨wc, hc0, hsc⟩ := hc.2 wc' hc2
    obtain ⟨wt, ht, hst⟩ := ht'.2 wt' ht2
    obtain ⟨wf, hf, hsf⟩ := hf'.2 wf' hf2
    have hb : SameTy F wc (HasBool.ttVal F) := hsc.trans hb'
    have htf : SameTy F wt wf := (hst.trans htf').trans hsf.symm
    obtain ⟨v, hv, h1, h2⟩ := hL.ite_build hc0 ht hf hb htf
    exact ⟨v, hv, ((ite_sameTy hL hb htf ht h1 h2).trans hst).trans
      (ite_sameTy hL hb' htf' ht2 h1' h2').symm⟩
  refine ⟨⟨fun v he => (fwd v he).imp fun _ h => ⟨h.1, h.2.1⟩, bwd⟩, fun hC0 => ?_⟩
  cases hs : P.eval F σ (WPOps.ite c t f) with
  | some v => exact (fwd v hs).elim fun _ ⟨hv', _, hx⟩ => hv'.trans (congrArg some (hx hC0))
  | none =>
    exact Option.eq_none_iff_forall_ne_some.2 fun v' ht => (bwd v' ht).elim fun _ ⟨hv, _⟩ =>
      nomatch hs.symm.trans hv

/-- **Contextual simplification keeps the value.**  In a well-formed store satisfying the scope
    invariant, with a guard map whose guards have Boolean values, the contextual simplification
    of an expression is sort-equivalent to it, and has its value when the guard map holds. -/
theorem rwG_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) (hI : ScopeInv F ini σ sc)
    (fuel : Nat) (K : Guards P) (e : P.Expr) : KBool F σ K →
    SortEq F σ e (rwG sc fuel K e) ∧
      (GCons F σ K → P.eval F σ (rwG sc fuel K e) = P.eval F σ e) := by
  fun_induction rwG sc fuel K e with
  | case1 K e c t f hv c' g hg ihc iht ihf =>
    intro hK
    rw [← rwG_goal_congr (WPLang.iteView?_eval hv)]
    obtain ⟨hc, hce⟩ := ihc hK
    refine ite_rel hL hc hce fun wc hc2 hb => ?_
    have hgw : σ g = some wc := (hL.var c' g σ hC hg).symm.trans hc2
    obtain ⟨ht, hxt⟩ := iht (hK.insert true hgw hb)
    obtain ⟨hf, hxf⟩ := ihf (hK.insert false hgw hb)
    exact ⟨ht, hf, fun hk hw => hxt (hk.insert (by simpa using hgw.trans (congrArg some hw))),
      fun hk hw => hxf (hk.insert (by simpa using hgw.trans (congrArg some hw)))⟩
  | case2 K e c t f hv c' hg ihc iht ihf =>
    intro hK
    rw [← rwG_goal_congr (WPLang.iteView?_eval hv)]
    obtain ⟨hc, hce⟩ := ihc hK
    obtain ⟨ht, hxt⟩ := iht hK
    obtain ⟨hf, hxf⟩ := ihf hK
    exact ite_rel hL hc hce fun _ _ _ => ⟨ht, hf, fun hk _ => hxt hk, fun hk _ => hxf hk⟩
  | case3 K e hv =>
    intro hK
    exact substFn_sem hL hC (look_sem hL hC hI hK fuel) e

/-! ## Facts -/

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- **A fact holds where its assumption does.**  When the condition `e` states a fact about the
    guard `g` and evaluates to `true` in a well-formed store, `g` has the value of the fact. -/
theorem factOf_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) {e : P.Expr} {g : P.Ident}
    {b : Bool} (hf : factOf e = some (g, b)) (he : P.eval F σ e = some (HasBool.ttVal F)) :
    σ g = some (boolV F b) := by
  unfold factOf at hf
  split at hf
  · rename_i g' hg
    cases hf
    exact (hL.var e g σ hC hg).symm.trans he
  split at hf <;> try cases hf
  rename_i c t f hv
  rw [WPLang.iteView?_eval hv] at he
  obtain ⟨wc, wt, wf, hc, ht, hf', hb, -, h1, h2⟩ := hL.ite_parts he
  have hcg {g : P.Ident} (hg : HasFvar.getFvar c = some g) : σ g = some wc :=
    (hL.var c g σ hC hg).symm.trans hc
  split at hf
  next g' hg htl hfl =>
    cases hf
    rw [WPLang.boolLit?_eval hfl] at hf'
    rcases hL.bool_cases hb with h | h
    · exact (hcg hg).trans (congrArg some h)
    · exact absurd ((h2 h).trans (Option.some.inj (hf'.symm.trans (hL.val.eval_ff σ))))
        (HasBool.ttVal_ne_ffVal F)
  next g' hg htl hfl =>
    cases hf
    rw [WPLang.boolLit?_eval htl] at ht
    rcases hL.bool_cases hb with h | h
    · exact absurd ((h1 h).trans (Option.some.inj (ht.symm.trans (hL.val.eval_ff σ))))
        (HasBool.ttVal_ne_ffVal F)
    · exact (hcg hg).trans (congrArg some h)
  next => cases hf

/-- The invariant of the walk state `st` in the store `σ`: the store is well formed and satisfies
    the scope invariant; every recorded type is the type of the variable's value; and every fact
    names a Boolean variable defined earlier on the path, stable in its scope. -/
structure WInv (F : P.Factory) (ini : Std.HashSet P.Ident) (σ : SemanticStore P)
    (st : PSt P) : Prop where
  wf : WellFormedStore σ F
  scope : ScopeInv F ini σ st.scope
  tys : ∀ g ty, st.tys[g]? = some ty → ∃ v, σ g = some v ∧ HasVal.valueOfTy F v ty
  facts : ∀ g b, st.facts[g]? = some b → boolVar ini st g = true

omit [GuardOps P] [LawfulBEq P.Ident] [LawfulHasVal P] in
/-- The facts of a state satisfying the walk invariant have Boolean values. -/
theorem WInv.kBool {st : PSt P} (hW : WInv F ini σ st) : KBool F σ st.facts := fun g b hg => by
  have hb := (Bool.and_eq_true_iff.1 (hW.facts g b hg)).2
  cases ht : st.tys[g]? with
  | none => simp [ht] at hb
  | some ty =>
    simp only [ht, Option.map_some, Option.getD_some] at hb
    obtain ⟨v, hv, hty⟩ := hW.tys g ty ht
    exact ⟨v, hv, _, WPLang.tyBEq_eq hb ▸ hty, (HasBool.boolIsValOfTy F).1⟩

/-- **The invariant and the facts after an `init`** of the undefined `x`, a name some `init` of
    the list defines, to a value of type `ty`: the walk invariant holds for the scope extended by
    `x` and the types extended by `x : ty`, and the facts that held still hold. -/
private theorem winv_push (hL : GuardFwdLaws F) {st : PSt P} (hW : WInv F ini σ st)
    {σ1 : SemanticStore P} {x : P.Ident} {ty : P.Ty} {v : P.Val} {val : Option P.Expr}
    (h0 : σ x = none) (h1 : σ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y)
    (hty : HasVal.valueOfTy F v ty) (hx : ini.contains x = true)
    (hval : ∀ d, val = some d → P.eval F σ d = some v ∧
      ∀ z ∈ HasFvars.getFvars d, st.scope.contains z = true ∨ ini.contains z = false) :
    WInv F ini σ1 { st with scope := st.scope.insert x val, tys := st.tys.insert x ty } ∧
      (GCons F σ st.facts → GCons F σ1 st.facts) := by
  obtain ⟨hC1, hI1⟩ :=
    hW.scope.push hL.congr hW.wf h0 h1 hfr (LawfulHasVal.valueOfTy_isVal _ _ _ hty) hx hval
  have hne : ∀ g b, st.facts[g]? = some b → x ≠ g := by
    rintro g b hg rfl
    have hs := hW.facts x b hg
    simp only [boolVar, stable, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
    rcases hs.1 with h | h
    · simpa [h0] using hW.scope.1 x h
    · simp [hx] at h
  refine ⟨⟨hC1, hI1, fun g t hg => ?_, fun g b hg => ?_⟩, fun hK g b hg => ?_⟩
  · rw [Std.HashMap.getElem?_insert] at hg
    split at hg
    · exact eq_of_beq ‹_› ▸ Option.some.inj hg ▸ ⟨v, h1, hty⟩
    · rename_i hxg
      exact (hfr g (by simpa using hxg)).symm ▸ hW.tys g t hg
  · have hxg : (x == g) = false := by simpa using hne g b hg
    simpa only [boolVar, stable, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Std.HashMap.contains_insert, Std.HashMap.getElem?_insert, hxg, Bool.false_eq_true,
      false_or, ↓reduceIte] using hW.facts g b hg
  · exact (hfr g (hne g b hg)).trans (hK g b hg)

/-! ## Runs of the rewritten list -/

/-- The rewrite of an expression at a position is sort-equivalent to it, and keeps its value
    where the facts hold. -/
private theorem rwAt_sem (hL : GuardFwdLaws F) {st : PSt P} (hW : WInv F ini σ st) (e : P.Expr) :
    SortEq F σ e (rwAt st e) ∧ (GCons F σ st.facts → P.eval F σ (rwAt st e) = P.eval F σ e) :=
  rwG_sem hL hW.wf hW.scope _ _ e hW.kBool

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- An event of a single statement corresponds to its rewrite. -/
private theorem keeps_single {mk : EventArg P → Event P} {l : String} {md : MetaData P}
    {e e' : P.Expr} (hmk : mk = .assume ∨ mk = .assert ∨ mk = .cover)
    (h : P.eval F σ e' = P.eval F σ e) :
    Trace.KeepsWhileAssumed [mk ⟨F, σ, l, e, md⟩] [mk ⟨F, σ, l, e', md⟩] := by
  have hh : Held (⟨F, σ, l, e', md⟩ : EventArg P) ↔ Held ⟨F, σ, l, e, md⟩ := by simp only [Held, h]
  rcases hmk with rfl | rfl | rfl
  · exact .assume rfl rfl hh fun _ => .nil
  · exact .assert rfl rfl hh .nil
  · exact .cover rfl rfl hh .nil

omit [DecidableEq P.Ident] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P] [BEq P.Ident]
  [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- A run of a list in passive form leaves the store of an `ite *` it is an arm of unchanged. -/
private theorem arm_store {ss : PStmts P} {σ σ1 : SemanticStore P} {evs : List (Event P)}
    (h : BRun F ss σ evs (.normal σ1)) (hp : Block.passiveForm ss = true) :
    projectStore σ σ1 = σ := by
  obtain ⟨_, ⟨⟩, hk⟩ := passive_run h hp
  exact projectStore_keep hk

/-- The store `τ` of the rewritten run *follows* the store `σ` of the input's run: it is well
    formed and holds, for every variable, the value of `σ` or a value of its type (and nothing
    where `σ` holds nothing). -/
structure Follows (F : P.Factory) (σ τ : SemanticStore P) : Prop where
  wf : WellFormedStore τ F
  same : ∀ x, SameTyO F (σ x) (τ x)

/-- The outcomes `o` of the input's run and `o'` of the rewritten run are both normal, with
    stores that follow. -/
@[expose] def OFollows (F : P.Factory) (o o' : Outcome P) : Prop :=
  ∃ σ τ, o = .normal σ ∧ o' = .normal τ ∧ Follows F σ τ

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P]
  [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- A well-formed store follows itself. -/
theorem Follows.refl (hC : WellFormedStore σ F) : Follows F σ σ := ⟨hC, fun _ => .inl rfl⟩

omit [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [GuardOps P] [BEq P.Ident]
  [LawfulBEq P.Ident] [Hashable P.Ident] in
/-- **An `init` replayed in a store that follows.**  The `init` of the undefined `x` to a value of
    type `ty` in `σ`, and a value `w` of the same type, give an `init` of `x` to `w` from a store
    `τ` that follows `σ`, to a store that follows the store after it. -/
private theorem init_follow {τ σ1 : SemanticStore P} (h : Follows F σ τ) {x : P.Ident}
    {ty : P.Ty} {v w : P.Val} (h0 : σ x = none) (h1 : σ1 x = some v)
    (hfr : ∀ y, x ≠ y → σ1 y = σ y) (hty : HasVal.valueOfTy F v ty) (hs : SameTy F v w) :
    ∃ τ1, InitState P τ x w τ1 ∧ HasVal.valueOfTy F w ty ∧ Follows F σ1 τ1 ∧
      (τ = σ → w = v → τ1 = σ1) := by
  obtain ⟨t, hv, hw⟩ := hs
  have hwty : HasVal.valueOfTy F w ty := LawfulHasVal.valueOfTy_congr F v w ty t hty hv hw
  have hτx : τ x = none := (h.same x).elim (fun h' => h0 ▸ h'.symm) fun ⟨_, _, ha, _⟩ => by
    cases h0.symm.trans ha
  refine ⟨fun y => if x = y then some w else τ y, .init hτx (by simp) fun y hy => by
    simp [hy], hwty, ⟨fun y u hu => ?_, fun y => ?_⟩, fun hτ hwv => funext fun y => ?_⟩
  · by_cases hxy : x = y
    · simp only [hxy, ↓reduceIte, Option.some.injEq] at hu
      exact hu ▸ LawfulHasVal.valueOfTy_isVal _ _ _ hwty
    · exact h.wf y u (by simpa only [hxy, ↓reduceIte] using hu)
  · rcases Classical.em (x = y) with rfl | hxy
    · exact .inr ⟨v, w, h1, by simp, t, hv, hw⟩
    · simpa only [hxy, ↓reduceIte, hfr y hxy] using h.same y
  · subst hτ hwv
    rcases Classical.em (x = y) with rfl | hxy
    · simp [h1]
    · simp [hxy, hfr y hxy]

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
mutual
/-- **A run of a list, replayed on its rewrite.**  A run of a list in passive form from a store
    satisfying the walk invariant has a run of the rewritten list from every store that follows
    it, with outcomes whose stores follow; when the two stores are equal and the facts hold, the
    events correspond, and, when the input's assumptions hold, the outcomes are equal. -/
private theorem gp_run [LawfulBEq P.Ident] [LawfulHasVal P] (hL : GuardFwdLaws F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRun F ss σ evs o → ∀ {st : PSt P} {τ : SemanticStore P}, Block.passiveForm ss = true →
    (∀ x ∈ Block.assignedVars ss, ini.contains x = true) → WInv F ini σ st → Follows F σ τ →
    ∃ evs' o', BRun F (walk ini st ss).1 τ evs' o' ∧ OFollows F o o' ∧
      (τ = σ → GCons F σ st.facts → Trace.KeepsWhileAssumed evs evs' ∧ (AllHeld evs → o' = o))
  | _, σ, _, _, .nil, _, τ, _, _, _, hD => ⟨[], _, .nil, ⟨σ, τ, rfl, rfl, hD⟩, fun h _ =>
      ⟨.nil, fun _ => h ▸ rfl⟩⟩
  | _, σ, _, _, .cons_normal (σ1 := σ1) (evs1 := evs1) (evs2 := evs2) h1 h2, st, τ, hp, hini, hW,
    hD => by
    obtain ⟨evs1', o1', h1', ⟨_, τ1, ⟨⟩, rfl, hD1⟩, hr1, hpost⟩ := gp_runS hL h1
      (passive_cons hp).1 (fun x hx => hini x (List.mem_append_left _ hx)) hW hD
    obtain ⟨hW1, hK1⟩ := hpost _ rfl
    obtain ⟨evs2', o', h2', ho', hr2⟩ := gp_run hL h2 (passive_cons hp).2
      (fun x hx => hini x (List.mem_append_right _ hx)) hW1 hD1
    have hc := fun hτ hK ha => hr2 (Outcome.normal.inj ((hr1 hτ hK).2 ha)) (hK1 hτ hK ha)
    refine ⟨evs1' ++ evs2', o', .cons_normal h1' h2', ho', fun hτ hK => ⟨(hr1 hτ hK).1.append
      fun ha => (hc hτ hK ha).1, fun ha => ?_⟩⟩
    exact (hc hτ hK fun a h => ha a (List.mem_append_left _ h)).2
      fun a h => ha a (List.mem_append_right _ h)
  | _, _, _, _, .cons_exit h1, st, τ, hp, _, _, _ => by
    obtain ⟨σ', ho, -⟩ := passive_run (.cons_exit (rest := []) h1) (passive_cons hp).1
    cases ho
/-- **A run of a statement, replayed on its rewrite**: `gp_run` for one statement; the store
    after it satisfies the walk invariant for the state after the walk over it, and the facts of
    that state hold there when the stores were equal, the facts before it held and the
    assumptions of the run hold. -/
private theorem gp_runS [LawfulBEq P.Ident] [LawfulHasVal P] (hL : GuardFwdLaws F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {st : PSt P} {τ : SemanticStore P}, Block.passiveForm [s] = true →
    (∀ x ∈ Stmt.assignedVars s, ini.contains x = true) → WInv F ini σ st → Follows F σ τ →
    ∃ evs' o', BRunS F (walkS ini st s).1 τ evs' o' ∧ OFollows F o o' ∧
      (τ = σ → GCons F σ st.facts → Trace.KeepsWhileAssumed evs evs' ∧ (AllHeld evs → o' = o)) ∧
      ∀ σ', o = .normal σ' → WInv F ini σ' (walkS ini st s).2 ∧
        (τ = σ → GCons F σ st.facts → AllHeld evs → GCons F σ' (walkS ini st s).2.facts)
  | _, σ, _, _, .cmd (c := .cmd (.init x ty (.det e) md)) h, st, τ, _, hini, hW, hD => by
    obtain ⟨v, hev, h0, h1, hfr, rfl, hty⟩ := EvalCmdE.init_det_inv h
    obtain ⟨w, hew, hs⟩ := hL.retype hW.wf hD.wf (fun z _ => hD.same z) hev
    obtain ⟨τ1, hin, hwty, hD1, heq⟩ := init_follow hD h0 h1 hfr hty hs
    refine ⟨[], _, .cmd (.eval_init hew hin hwty hL.var), ⟨_, τ1, rfl, rfl, hD1⟩,
      fun hτ hK => ⟨.nil, fun _ => by
        subst hτ; rw [heq rfl (Option.some.inj (hew.symm.trans hev))]⟩,
      fun σ' ho => ?_⟩
    cases ho
    obtain ⟨hW1, hK1⟩ := winv_push hL hW h0 h1 hfr hty (hini x (by simp [Stmt.assignedVars]))
      (val := if (HasFvars.getFvars e).all (stable ini st.scope) then some e else none)
      fun d hd => by
        split at hd <;> cases hd
        rename_i hrec
        exact ⟨hev, by simpa [stable] using hrec⟩
    exact ⟨hW1, fun _ hK _ => hK1 hK⟩
  | _, σ, _, _, .cmd (c := .cmd (.init x ty .nondet md)) h, st, τ, _, hini, hW, hD => by
    obtain ⟨v, hty, h0, h1, hfr, rfl⟩ := EvalCmdE.init_nondet_inv h
    obtain ⟨τ1, hin, hwty, hD1, heq⟩ := init_follow hD h0 h1 hfr hty ⟨_, hty, hty⟩
    refine ⟨[], _, .cmd (.eval_init_unconstrained hin hwty hL.var), ⟨_, τ1, rfl, rfl, hD1⟩,
      fun hτ _ => ⟨.nil, fun _ => by rw [heq hτ rfl]⟩, fun σ' ho => ?_⟩
    cases ho
    obtain ⟨hW1, hK1⟩ := winv_push hL hW h0 h1 hfr hty (hini x (by simp [Stmt.assignedVars]))
      (val := none) fun _ hd => by cases hd
    exact ⟨hW1, fun _ hK _ => hK1 hK⟩
  | _, _, _, _, .cmd (c := .cmd (.set _ _ _)) _, _, _, hp, _, _, _ => by
    simp [Block.passiveForm] at hp
  | _, σ, _, _, .cmd (c := .cmd (.assume l e md)) h, st, τ, _, _, hW, hD => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assume_inv h
    refine ⟨_, _, .cmd .eval_assume, ⟨_, τ, rfl, rfl, hD⟩, fun hτ hK => ?_, fun σ' ho => ?_⟩
    · subst hτ
      exact ⟨keeps_single (.inl rfl) ((rwAt_sem hL hW e).2 hK), fun _ => rfl⟩
    cases ho
    refine ⟨⟨hW.wf, hW.scope, hW.tys, fun g b hg => ?_⟩, fun hτ hK ha => ?_⟩
    · simp only [walkS, addFact] at hg ⊢
      (repeat' split at hg) <;> try exact hW.facts g b hg
      rw [Std.HashMap.getElem?_insert] at hg
      split at hg
      · exact eq_of_beq ‹_› ▸ ‹boolVar ini st _ = true›
      · exact hW.facts g b hg
    · have he : P.eval F _ (rwAt st e) = some (HasBool.ttVal F) :=
        ((rwAt_sem hL hW e).2 hK).trans (ha _ (List.mem_singleton_self _))
      simp only [walkS, addFact]
      (repeat' split) <;> first | exact hK | exact hK.insert (factOf_sem hL hW.wf ‹_› he)
  | _, σ, _, _, .cmd (c := .cmd (.assert l e md)) h, st, τ, _, _, hW, hD => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assert_inv h
    refine ⟨_, _, .cmd .eval_assert, ⟨_, τ, rfl, rfl, hD⟩, fun hτ hK => ?_,
      fun σ' ho => by cases ho; exact ⟨hW, fun _ hK _ => hK⟩⟩
    subst hτ
    exact ⟨keeps_single (.inr (.inl rfl)) ((rwAt_sem hL hW e).2 hK), fun _ => rfl⟩
  | _, σ, _, _, .cmd (c := .cmd (.cover l e md)) h, st, τ, _, _, hW, hD => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.cover_inv h
    refine ⟨_, _, .cmd .eval_cover, ⟨_, τ, rfl, rfl, hD⟩, fun hτ hK => ?_,
      fun σ' ho => by cases ho; exact ⟨hW, fun _ hK _ => hK⟩⟩
    subst hτ
    exact ⟨keeps_single (.inr (.inr rfl)) ((rwAt_sem hL hW e).2 hK), fun _ => rfl⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _, _, _, _, _, _ => h.elim
  | _, _, _, _, .ite_true _ _, _, _, hp, _, _, _ | _, _, _, _, .ite_false _ _, _, _, hp, _, _, _ =>
    by simp [Block.passiveForm] at hp
  | _, σ, _, _, .ite_nondet_true (tss := tss) h, st, τ, hp, hini, hW, hD => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', o', h', ⟨σ1, τ1, rfl, rfl, -⟩, hr⟩ := gp_run hL h hp.1.1
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hW hD
    refine ⟨evs', _, .ite_nondet_true h', ⟨σ, τ, ?_, ?_, hD⟩, fun hτ hK => ?_, fun σ' ho => ?_⟩
    · simp only [Outcome.proj, arm_store h hp.1.1]
    · simp only [Outcome.proj, arm_store h' (walk_shape ini tss hp.1.1 st).1]
    · exact ⟨(hr hτ hK).1, fun ha => by rw [(hr hτ hK).2 ha, hτ]⟩
    · simp only [Outcome.proj, arm_store h hp.1.1, Outcome.normal.injEq] at ho
      exact ho ▸ ⟨hW, fun _ hK _ => hK⟩
  | _, σ, _, _, .ite_nondet_false (ess := ess) h, st, τ, hp, hini, hW, hD => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', o', h', ⟨σ1, τ1, rfl, rfl, -⟩, hr⟩ := gp_run hL h hp.1.2
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hW hD
    refine ⟨evs', _, .ite_nondet_false h', ⟨σ, τ, ?_, ?_, hD⟩, fun hτ hK => ?_, fun σ' ho => ?_⟩
    · simp only [Outcome.proj, arm_store h hp.1.2]
    · simp only [Outcome.proj, arm_store h' (walk_shape ini ess hp.1.2 st).1]
    · exact ⟨(hr hτ hK).1, fun ha => by rw [(hr hτ hK).2 ha, hτ]⟩
    · simp only [Outcome.proj, arm_store h hp.1.2, Outcome.normal.injEq] at ho
      exact ho ▸ ⟨hW, fun _ hK _ => hK⟩
  | _, _, _, _, .block _, _, _, hp, _, _, _ | _, _, _, _, .exit, _, _, hp, _, _, _
  | _, _, _, _, .typeDecl, _, _, hp, _, _, _ | _, _, _, _, .loop_exit _, _, _, hp, _, _, _
  | _, _, _, _, .loop_iter _ _ _, _, _, hp, _, _, _
  | _, _, _, _, .loop_break _ _, _, _, hp, _, _, _ => by
    simp [Block.passiveForm] at hp
end

omit [LawfulBEq P.Ident] [LawfulHasVal P] in
mutual
/-- **A reach of a list, replayed on its rewrite.**  A reach of a list in passive form from a
    store satisfying the walk invariant has a reach of the rewritten list from every store that
    follows it, whose events correspond to the input's when the two stores are equal and the
    facts hold. -/
private theorem gp_reach [LawfulBEq P.Ident] [LawfulHasVal P] (hL : GuardFwdLaws F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)},
    BReach F ss σ evs → ∀ {st : PSt P} {τ : SemanticStore P}, Block.passiveForm ss = true →
    (∀ x ∈ Block.assignedVars ss, ini.contains x = true) → WInv F ini σ st → Follows F σ τ →
    ∃ evs', BReach F (walk ini st ss).1 τ evs' ∧
      (τ = σ → GCons F σ st.facts → Trace.KeepsWhileAssumed evs evs')
  | _, _, _, .here h, st, τ, hp, hini, hW, hD => by
    obtain ⟨evs', h', hr⟩ := gp_reachS hL h (passive_cons hp).1
      (fun x hx => hini x (List.mem_append_left _ hx)) hW hD
    exact ⟨evs', .here h', hr⟩
  | _, _, _, .later (σ1 := σ1) h1 h2, st, τ, hp, hini, hW, hD => by
    obtain ⟨evs1, o1', h1', ⟨_, τ1, ⟨⟩, rfl, hD1⟩, hr1, hpost⟩ := gp_runS hL h1
      (passive_cons hp).1 (fun x hx => hini x (List.mem_append_left _ hx)) hW hD
    obtain ⟨hW1, hK1⟩ := hpost _ rfl
    obtain ⟨evs2, h2', hr2⟩ := gp_reach hL h2 (passive_cons hp).2
      (fun x hx => hini x (List.mem_append_right _ hx)) hW1 hD1
    exact ⟨evs1 ++ evs2, .later h1' h2', fun hτ hK => (hr1 hτ hK).1.append fun ha =>
      hr2 (Outcome.normal.inj ((hr1 hτ hK).2 ha)) (hK1 hτ hK ha)⟩
/-- **A reach of a statement, replayed on its rewrite**: `gp_reach` for one statement. -/
private theorem gp_reachS [LawfulBEq P.Ident] [LawfulHasVal P] (hL : GuardFwdLaws F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {st : PSt P} {τ : SemanticStore P}, Block.passiveForm [s] = true →
    (∀ x ∈ Stmt.assignedVars s, ini.contains x = true) → WInv F ini σ st → Follows F σ τ →
    ∃ evs', BReachS F (walkS ini st s).1 τ evs' ∧
      (τ = σ → GCons F σ st.facts → Trace.KeepsWhileAssumed evs evs')
  | _, _, _, .cmd (c := c) h hne, st, τ, hp, hini, hW, hD => by
    obtain ⟨evs', o', h', -, hr, -⟩ := gp_runS hL (.cmd h) hp hini hW hD
    have hn : evs' ≠ [] := fun h0 => hne <| by
      subst h0
      rcases c with ((⟨x, ty, (e | _), md⟩ | ⟨x, e, md⟩ | _ | _ | _) | _)
      · exact (EvalCmdE.init_det_inv h).elim fun _ ⟨_, _, _, _, he, _⟩ => he
      · exact (EvalCmdE.init_nondet_inv h).elim fun _ ⟨_, _, _, _, he⟩ => he
      · simp [Block.passiveForm] at hp
      all_goals first | exact h.elim | (rcases h' with ⟨⟨⟩⟩)
    obtain ⟨c', hc'⟩ : ∃ c', (walkS ini st (.cmd c)).1 = .cmd c' := by
      rcases c with ((_ | _ | _ | _ | _) | _)
      all_goals first | exact ⟨_, rfl⟩ | (rename_i e _; cases e <;> exact ⟨_, rfl⟩)
    rw [hc'] at h' ⊢
    cases h' with
    | cmd h' => exact ⟨evs', .cmd h' hn, fun hτ hK => (hr hτ hK).1⟩
  | _, _, _, .ite_true _ _, _, _, hp, _, _, _ | _, _, _, .ite_false _ _, _, _, hp, _, _, _ => by
    simp [Block.passiveForm] at hp
  | _, _, _, .ite_nondet_true (tss := tss) h, st, τ, hp, hini, hW, hD => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := gp_reach hL h hp.1.1
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hW hD
    exact ⟨evs', .ite_nondet_true h', hr⟩
  | _, _, _, .ite_nondet_false (tss := tss) h, st, τ, hp, hini, hW, hD => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := gp_reach hL h hp.1.2
      (fun x hx => hini x (by simp [Stmt.assignedVars, hx])) hW hD
    exact ⟨evs', .ite_nondet_false h', hr⟩
  | _, _, _, .block _, _, _, hp, _, _, _ | _, _, _, .loop_here _ _, _, _, hp, _, _, _
  | _, _, _, .loop_later _ _ _, _, _, hp, _, _, _ => by simp [Block.passiveForm] at hp
end

omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [GuardOps P] [LawfulHasVal P] in
/-- The names some `init` of a list defines are in the set guard propagation computes. -/
private theorem guardProp_ini (ss : PStmts P) :
    ∀ x ∈ Block.assignedVars ss,
      (Std.HashSet.ofList (Block.assignedVarsH ss)).contains x = true := fun x hx => by
  simpa [Std.HashSet.contains_ofList, Block.assignedVarsH_eq] using hx

omit [GuardOps P] [LawfulHasVal P] in
/-- The walk invariant holds for the empty state in a well-formed store. -/
private theorem winv_empty (hC : WellFormedStore σ F) : WInv F ini σ {} :=
  ⟨hC, ⟨fun _ h => by simp at h, fun _ _ h => by simp at h⟩, fun _ _ h => by simp at h,
    fun _ _ h => by simp at h⟩

/-- **A run of a list, and of its guard propagation.**  A run of a list in passive form from a
    well-formed store has a run of `guardProp ss` from the same store, whose events correspond to
    it while its assumptions hold (`Trace.KeepsWhileAssumed`), ending normally like it in a store
    that holds, for every variable, the value of the input's final store or a value of its type
    (`OFollows`), for a factory satisfying `GuardFwdLaws`. -/
theorem guardProp_run_rel (hL : GuardFwdLaws F) {ss : PStmts P} (hp : Block.passiveForm ss = true)
    {evs : List (Event P)} {o : Outcome P} (hC : WellFormedStore σ F) (h : BRun F ss σ evs o) :
    ∃ evs' o', BRun F (guardProp ss) σ evs' o' ∧ Trace.KeepsWhileAssumed evs evs' ∧
      OFollows F o o' :=
  (gp_run hL h hp (guardProp_ini ss) (winv_empty hC) (.refl hC)).imp fun _ ⟨o', h1, h2, h3⟩ =>
    ⟨o', h1, (h3 rfl fun _ _ h => by simp at h).1, h2⟩

/-- **A reach of a list, and of its guard propagation.**  A reach of a list in passive form from
    a well-formed store has a reach of `guardProp ss` from the same store whose events correspond
    to it while its assumptions hold (`Trace.KeepsWhileAssumed`), for a factory satisfying
    `GuardFwdLaws`. -/
theorem guardProp_reach_rel (hL : GuardFwdLaws F) {ss : PStmts P}
    (hp : Block.passiveForm ss = true) {evs : List (Event P)} (hC : WellFormedStore σ F)
    (h : BReach F ss σ evs) :
    ∃ evs', BReach F (guardProp ss) σ evs' ∧ Trace.KeepsWhileAssumed evs evs' :=
  (gp_reach hL h hp (guardProp_ini ss) (winv_empty hC) (.refl hC)).imp fun _ ⟨h1, h2⟩ =>
    ⟨h1, h2 rfl fun _ _ h => by simp at h⟩

end -- public section

end GuardProp
end Imperative
