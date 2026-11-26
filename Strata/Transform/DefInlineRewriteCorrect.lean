/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInlineRewrite
public import Strata.Transform.NormLawTyped
public import Strata.Transform.DefInlineTyping
public import Strata.Transform.DefInlineCorrect
public import Strata.Transform.Passive.CoreTyped
public import Strata.DL.Lambda.LExprDenoteEvalCongr
import all Strata.Transform.DefInlineRewrite
import all Strata.Transform.Passive.CoreLang
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps
import Strata.Languages.Core.InstExprTyping

/-! # The rewrites of the rewrite loop keep values, syntax and types

Each rewrite at the root of `Core.DefInline.rwRoot` satisfies the *root laws* (`RootLaws`): on
an expression with ground operator, abstraction and quantifier annotations (`LExpr.AnnGround`),
it keeps the value in every well-formed store typing the expression's annotated free-variable
occurrences (`Imperative.StoreTypes`), under a factory whose functions are those of `fac` and
whose evaluator respects Boolean negation; it keeps the ground annotations; it adds no
free-variable occurrence and no operator; and it keeps the annotated type of an expression
whose free-variable occurrences carry ground annotations.  The root laws compose
(`RootLaws.comp`), so `rwRoot fac` satisfies them (`rwRoot_laws`).

The bottom-up rewrite `rwBelowWith root g` at a root rewrite `root` satisfying the root laws
keeps them too, between `e` with `g` substituted and its rewrite (`rwBelowWith_rel`, the laws at
one pair: `RelLaws`): a substituted expression is kept, and a node with parts replaced by
expressions with the same values keeps its value, also when a part has none
(`LExpr.denoteEval_app_congr`, `LExpr.denoteEval_eq_congr`, `LExpr.denoteEval_ite_congr`).
Hence `rwAllWith root`, and so the normalizations `rwAll fac` (at `rwRoot fac`) and `rwAllC fac`
(at `ctorRoot fac`, `ctorRoot_laws`), keep the values of substituted expressions in typed stores
(`rwAllWith_normLawT`), add no free-variable occurrence or operator to them (`rwAllWith_freeVars`,
`rwAllWith_ops`) and keep their types (`rwAllWith_typed`).

`annGround` decides `LExpr.AnnGround` (`annGround_ground`, `annGround_of_ground`); `annGroundWith`
with the ground checks of the substituted expressions is `annGround` of the substituted
expression (`annGroundWith_eq`); and the bottom-up rewrite of an expression whose substituted
form has ground annotations has ground annotations (`annGround_rwBelowWith`).

These are laws of a normalization, not a correctness theorem of their own: the trace
over-approximation of the inlining that uses them is stated with `OverapproximatesTracesUptoWhen`
(`defInline_overapproximatesTraces`, in `Strata.Transform.DefInlineCoreCorrect`, and
`Core.WPLoop.wpLoop_overapproximatesTraces`, in `Strata.Transform.WPLoopCorrect`).

Key definitions: `RootLaws`, `RelLaws`.

`testCtor fac` keeps values by the model's consistency with the body of the function it
applies (a tester's body applies the eliminator) and with the concrete evaluator of the function
that body applies (the eliminator's), whose result `(λ τ₁ … λ τₙ. k) a₁ … aₙ` denotes `k`.

Key theorems: `betaNG_laws`, `decEq_laws`, `foldOp_laws`, `liftIte_laws`, `iteSame_laws`,
`testCtor_laws`, `rwRoot_laws`, `ctorRoot_laws`, `rwBelowWith_rel`, `rwAllWith_normLawT`,
`rwAllWith_freeVars`, `rwAllWith_ops`, `rwAllWith_typed`, `annGround_ground`,
`annGround_of_ground`, `annGroundWith_eq`, `annGround_rwBelowWith`. -/

namespace Core
namespace DefInline

open Lambda Imperative Imperative.WP Imperative.DefInline Core.WP

public section

/-- The laws of a rewrite `r` at the root, for the factory of functions `fac`: on expressions
    with ground operator, abstraction and quantifier annotations, it keeps values in well-formed
    stores typing the annotated free-variable occurrences (under a factory whose functions are
    those of `fac` and whose evaluator respects Boolean negation), keeps the ground annotations,
    adds no free-variable occurrence and no operator, and keeps the annotated type of an
    expression whose free-variable occurrences carry ground annotations. -/
structure RootLaws (fac : Lambda.Factory CoreLParams) (r : Expression.Expr → Expression.Expr) :
    Prop where
  /-- The rewrite keeps the value. -/
  value : ∀ {F : Expression.Factory} {σ : SemanticStore Expression} {e : Expression.Expr},
    F.factory = fac → WellFormedSemanticEvalBool (P := Expression) F →
    WellFormedStore σ F → e.AnnGround → StoreTypes F σ e →
    Expression.eval F σ (r e) = Expression.eval F σ e
  /-- The rewrite keeps the ground annotations. -/
  ground : ∀ {e : Expression.Expr}, e.AnnGround → (r e).AnnGround
  /-- The rewrite adds no free-variable occurrence. -/
  fvars : ∀ {e : Expression.Expr} {p}, p ∈ (r e).freeVars → p ∈ e.freeVars
  /-- The rewrite adds no operator. -/
  ops : ∀ {e : Expression.Expr} {o}, o ∈ LExpr.getOps (r e) → o ∈ LExpr.getOps e
  /-- The rewrite keeps the annotated type. -/
  typed : ∀ {e : Expression.Expr} {τ : LMonoTy}, e.AnnGround →
    (∀ x τ?, (x, τ?) ∈ e.freeVars → ∃ τx, τ? = some τx ∧ τx.IsGround) →
    e.HasTypeA [] τ → (r e).HasTypeA [] τ

/-! ## Preliminaries -/

/-- The free-variable occurrences of a part are among those of the whole. -/
private theorem storeTypes_of_freeVars {F : Expression.Factory} {σ : SemanticStore Expression}
    {e e' : Expression.Expr} (h : StoreTypes F σ e)
    (hs : ∀ p, p ∈ e'.freeVars → p ∈ e.freeVars) : StoreTypes F σ e' :=
  h.mono fun _ hp => by
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap] at hp ⊢
    obtain ⟨q, hq, h⟩ := hp
    exact ⟨q, hs q hq, h⟩

/-- `tyGround` decides `LMonoTy.IsGround`. -/
private theorem tyGround_iff {τ : LMonoTy} : tyGround τ = true ↔ τ.IsGround := by
  simp [tyGround]

/-- `annGround` decides `LExpr.AnnGround`. -/
theorem annGround_ground : ∀ {e : Expression.Expr}, annGround e = true → e.AnnGround := by
  intro e h
  induction e <;> simp_all only [annGround, LExpr.AnnGround, Bool.and_eq_true, Option.all_eq_true,
    tyGround, decide_eq_true_eq, and_self, and_true, forall_const] <;>
    first | exact h | exact h.1 | exact h.1.1

/-- An expression with ground operator, abstraction and quantifier annotations passes
    `annGround`. -/
theorem annGround_of_ground : ∀ {e : Expression.Expr}, e.AnnGround → annGround e = true := by
  intro e h
  induction e <;> simp_all only [annGround, LExpr.AnnGround, Bool.and_eq_true, Option.all_eq_true,
    tyGround, decide_eq_true_eq, and_self, and_true, forall_const] <;>
    first | exact h | exact h.1

/-- **`annGroundWith` checks the substituted expression**: with `fl x` telling whether the
    expression `g` substitutes for `x`, if any, passes `annGround`, `annGroundWith fl e` is
    `annGround` of `e` with `g` substituted. -/
theorem annGroundWith_eq {fl : Expression.Ident → Bool}
    {g : Expression.Ident → Option Expression.Expr} (hfl : ∀ x, fl x = (g x).all annGround) :
    ∀ e : Expression.Expr, annGroundWith fl e = annGround (e.substFvarsBy g) := by
  intro e
  induction e with
  | fvar _ x _ =>
    rw [annGroundWith, hfl]
    cases hg : g x with
    | none => simp [LExpr.substFvarsBy, hg, annGround]
    | some v =>
      simp only [Option.all_some, LExpr.substFvarsBy, hg]
      cases v <;> rfl
  | _ => simp_all [annGroundWith, LExpr.substFvarsBy, annGround]

/-- A self-typed expression is typed at its ground type (`Core.Expression.Typed`). -/
private theorem selfTyped_typed {e : Expression.Expr} {τ : LMonoTy} (h : selfTyped e = some τ) :
    Expression.Typed e (.forAll [] τ) := by
  unfold selfTyped at h
  repeat' split at h
  all_goals try cases h
  rename_i hfv _ hτ hg
  refine ⟨_, rfl, tyGround_iff.1 hg, fun x τ? hx => ?_, LExpr.typeCheck_to_HasTypeA hτ⟩
  exact ((Option.any_eq_true _ _).1 (List.all_eq_true.1 hfv _ hx)).imp fun _ ⟨h1, h2⟩ =>
    ⟨h1, tyGround_iff.1 h2⟩

/-- **A self-typed expression evaluates** in a store typing its annotated free-variable
    occurrences, to a value of its type. -/
private theorem selfTyped_eval {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} {τ : LMonoTy} (h : selfTyped e = some τ) (hσ : StoreTypes F σ e) :
    ∃ v, e.denoteEval F σ = some v ∧ HasVal.valueOfTy F v (.forAll [] τ) :=
  eval_of_typed F σ (selfTyped_typed h) fun x τx hx =>
    hσ x _ (List.mem_filterMap.2 ⟨(x, some τx), hx, rfl⟩)

/-- Two distinct identifiers, for the congruence lemmas. -/
private theorem holes_ne : (⟨"a", ()⟩ : Identifier Unit) ≠ ⟨"b", ()⟩ := by
  simp

/-- **Congruence of applications** of Core expressions. -/
private theorem app_congr {F : Expression.Factory} {σ : SemanticStore Expression}
    {m : ExpressionMetadata}
    {f f' a a' : Expression.Expr} (hf : f.AnnGround) (hf' : f'.AnnGround)
    (hfe : f'.denoteEval F σ = f.denoteEval F σ) (hae : a'.denoteEval F σ = a.denoteEval F σ) :
    (LExpr.app m f' a').denoteEval F σ = (LExpr.app m f a).denoteEval F σ :=
  LExpr.denoteEval_app_congr _ _ holes_ne hf hf' hfe hae

/-- **Congruence of equalities** of Core expressions. -/
private theorem eq_congr {F : Expression.Factory} {σ : SemanticStore Expression}
    {m : ExpressionMetadata}
    {a a' b b' : Expression.Expr} (ha : a.AnnGround) (ha' : a'.AnnGround)
    (hae : a'.denoteEval F σ = a.denoteEval F σ) (hbe : b'.denoteEval F σ = b.denoteEval F σ) :
    (LExpr.eq m a' b').denoteEval F σ = (LExpr.eq m a b).denoteEval F σ :=
  LExpr.denoteEval_eq_congr _ _ holes_ne ha ha' hae hbe

/-- The root laws compose: `r₂ ∘ r₁` satisfies them when `r₁` and `r₂` do. -/
theorem RootLaws.comp {fac : Lambda.Factory CoreLParams} {r₁ r₂ : Expression.Expr → Expression.Expr}
    (h₁ : RootLaws fac r₁) (h₂ : RootLaws fac r₂) : RootLaws fac (fun e => r₂ (r₁ e)) where
  value hF hB hC hg hσ := (h₂.value hF hB hC (h₁.ground hg)
    (storeTypes_of_freeVars hσ fun _ => h₁.fvars)).trans (h₁.value hF hB hC hg hσ)
  ground hg := h₂.ground (h₁.ground hg)
  fvars hp := h₁.fvars (h₂.fvars hp)
  ops ho := h₁.ops (h₂.ops ho)
  typed hg hfv hT := h₂.typed (h₁.ground hg) (fun x τ? hx => hfv x τ? (h₁.fvars hx))
    (h₁.typed hg hfv hT)

/-- A typed expression with ground annotations has a ground type. -/
private theorem hasTypeA_ground {e : Expression.Expr} {τ : LMonoTy} (hg : e.AnnGround)
    (hfv : ∀ x τ?, (x, τ?) ∈ e.freeVars → ∃ τx, τ? = some τx ∧ τx.IsGround)
    (hT : e.HasTypeA [] τ) : τ.IsGround :=
  hT.isGround (by simp) hg fun x ty hx => (hfv x _ hx).elim fun _ ⟨h, hg⟩ => by cases h; exact hg

/-! ## Decided equality -/

/-- **Decided equality satisfies the root laws**: `a == a` has the value `true` wherever the
    self-typed `a` has a value, which is wherever its annotated variables hold values of their
    annotated types. -/
theorem decEq_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac decEq where
  value {F σ e} _ _ _ _ hσ := by
    unfold decEq
    (repeat' split) <;> try rfl
    rename_i m a b h
    obtain ⟨rfl, hs⟩ := h
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨v, hv, -⟩ := selfTyped_eval hτ (storeTypes_of_freeVars hσ fun p hp => by
      simp [LExpr.freeVars, hp])
    exact (LExpr.denoteEval_boolConst (T := CoreLParams)).trans
      (LExpr.denoteEval_eq_true (T := CoreLParams) hv hv).symm
  ground {e} hg := by
    unfold decEq
    (repeat' split) <;> first | exact hg | trivial
  fvars {e p} hp := by
    unfold decEq at hp
    (repeat' split at hp) <;>
      first | exact hp | simp [HasBool.tt, Core.true, LExpr.boolConst, LExpr.freeVars] at hp
  ops {e o} ho := by
    unfold decEq at ho
    (repeat' split at ho) <;>
      first | exact ho | simp [HasBool.tt, Core.true, LExpr.boolConst, LExpr.getOps] at ho
  typed {e τ} _ _ hT := by
    unfold decEq
    (repeat' split) <;> first | exact hT | (cases hT; exact .const rfl)

/-! ## Constant folding -/

/-- `foldOp fac` leaves the expression, or replaces it by a literal. -/
private theorem foldOp_cases (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    foldOp fac e = e ∨ ∃ c, foldOp fac e = .const valueLoc c := by
  unfold foldOp
  split
  · exact .inl rfl
  · cases h : WPOps.evalOp? (P := Expression) fac e with
    | none => exact .inl rfl
    | some r => exact .inr ((Option.map_eq_some_iff.1 h).elim fun c ⟨_, hr⟩ => ⟨c, hr ▸ rfl⟩)

/-- **Constant folding satisfies the root laws**: the evaluator agrees with operator evaluation
    `WPOps.evalOp?`, and a folded operator keeps its type. -/
theorem foldOp_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac (foldOp fac) where
  value {F σ e} hF hB hC _ _ := by
    unfold foldOp
    split
    · rfl
    · cases h : WPOps.evalOp? (P := Expression) fac e with
      | none => rfl
      | some r => exact coreEvaluator_WellFormedSemanticEvalOp F fac hF hB hC h
  ground {e} hg := (foldOp_cases fac e).elim (fun h => by rwa [h]) fun ⟨_, h⟩ => by rw [h]; trivial
  fvars {e p} hp := (foldOp_cases fac e).elim (fun h => by rwa [h] at hp) fun ⟨_, h⟩ => by
    simp [h, LExpr.freeVars] at hp
  ops {e o} ho := (foldOp_cases fac e).elim (fun h => by rwa [h] at ho) fun ⟨_, h⟩ => by
    simp [h, LExpr.getOps] at ho
  typed {e τ} hg hfv hT := by
    unfold foldOp
    split
    · exact hT
    · cases h : WPOps.evalOp? (P := Expression) fac e with
      | none => exact hT
      | some r =>
        obtain ⟨τ', hτ', -, -, hT'⟩ := (typedOpLaws fac).evalOp h
          (ty := .forAll [] τ) ⟨τ, rfl, hasTypeA_ground hg hfv hT, hfv, hT⟩
        cases hτ'
        exact hT'

/-! ## A conditional with equal arms -/

/-- **A conditional with equal arms satisfies the root laws**: its condition, self-typed at
    `bool`, has a Boolean value wherever its annotated variables hold values of their annotated
    types, so the conditional has the value of its arm. -/
theorem iteSame_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac iteSame where
  value {F σ e} _ _ _ _ hσ := by
    unfold iteSame
    (repeat' split) <;> try rfl
    rename_i m c t f h
    obtain ⟨rfl, hc⟩ := h
    obtain ⟨v, hv, hvt⟩ := selfTyped_eval hc (storeTypes_of_freeVars hσ fun p hp => by
      simp [LExpr.freeVars, hp])
    obtain ⟨b, rfl⟩ : ∃ b, v = SemValue.ofBool F.model.tcInterp b :=
      (valueOfTy_bool F v hvt).elim (fun h => ⟨true, h⟩) fun h => ⟨false, h⟩
    refine Option.ext fun w => ?_
    rw [show Expression.eval F σ _ = _ from rfl, LExpr.denoteEval_ite_iff (T := CoreLParams)]
    refine ⟨fun h => ⟨b, w, w, hv, h, h, rfl, by cases b <;> rfl⟩, ?_⟩
    rintro ⟨b', vt, ve, -, ht, hf, -, rfl⟩
    cases ht.symm.trans hf
    cases b' <;> simpa using ht
  ground {e} hg := by
    unfold iteSame
    (repeat' split) <;> first | exact hg | exact hg.2.1
  fvars {e p} hp := by
    unfold iteSame at hp
    (repeat' split at hp) <;> first | exact hp | simp [LExpr.freeVars, hp]
  ops {e o} ho := by
    unfold iteSame at ho
    (repeat' split at ho) <;> first | exact ho | simp [LExpr.getOps, ho]
  typed {e τ} _ _ hT := by
    unfold iteSame
    (repeat' split) <;> first | exact hT | exact (HasTypeA.ite_inv hT).2.1

/-! ## A conditional with a literal condition -/

/-- **A conditional with a literal condition satisfies the root laws**: its arms, self-typed at
    one type, both have a value, of one sort, wherever its annotated variables hold values of
    their annotated types, so the conditional has the value of the arm the literal selects. -/
theorem iteLit_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac iteLit where
  value {F σ e} hF hB hC hgnd hσ := by
    clear hF hB hC hgnd
    unfold iteLit
    split
    · rename_i mi mc bv t f
      split
      · rename_i h
        obtain ⟨heq, hsome⟩ := h
        obtain ⟨τ, ht⟩ := Option.isSome_iff_exists.1 hsome
        obtain ⟨vt, hvt, -, hvtt⟩ := selfTyped_eval ht
          (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp])
        obtain ⟨vf, hvf, -, hvft⟩ := selfTyped_eval (heq ▸ ht)
          (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp])
        have hs : vt.sort = vf.sort := Lambda.LSort.toMonoTy_injective (by simp_all)
        have hc : Expression.eval F σ (LExpr.const mc (.boolConst bv)) =
            some (SemValue.ofBool F.model.tcInterp bv) := by
          rw [show Expression.eval F σ _ = _ from LExpr.denoteEval_const (T := CoreLParams)]
          cases bv <;> rfl
        rw [show Expression.eval F σ (LExpr.ite mi (LExpr.const mc (.boolConst bv)) t f) = _ from
          (LExpr.denoteEval_ite_iff (T := CoreLParams)).2 ⟨bv, vt, vf, hc, hvt, hvf, hs, rfl⟩]
        cases bv <;> simp [hvt, hvf]
      · rfl
    · rfl
  ground {e} hg := by
    unfold iteLit
    (repeat' split) <;> first | exact hg | exact hg.2.1 | exact hg.2.2
  fvars {e p} hp := by
    unfold iteLit at hp
    (repeat' split at hp) <;> first | exact hp | simp_all [LExpr.freeVars]
  ops {e o} ho := by
    unfold iteLit at ho
    (repeat' split at ho) <;> first | exact ho | simp_all [LExpr.getOps]
  typed {e τ} hgnd hfv hT := by
    clear hgnd hfv
    unfold iteLit
    (repeat' split) <;> first | exact hT | exact (HasTypeA.ite_inv hT).2.1 |
      exact (HasTypeA.ite_inv hT).2.2

/-! ## An operator into a conditional -/

/-- The cases of `findIte`: the conditional itself, or one found in the function or the argument
    of an application, or in a side of an equality. -/
private theorem findIte_cases {e s : Expression.Expr} {C : Expression.Expr → Expression.Expr}
    (h : findIte e = some (s, C)) :
    (e = s ∧ C = id) ∨
    (∃ m f a C₀, e = .app m f a ∧ findIte f = some (s, C₀) ∧ C = fun x => .app m (C₀ x) a) ∨
    (∃ m f a C₀, e = .app m f a ∧ findIte f = none ∧ findIte a = some (s, C₀) ∧
      C = fun x => .app m f (C₀ x)) ∨
    (∃ m a b C₀, e = .eq m a b ∧ findIte a = some (s, C₀) ∧ C = fun x => .eq m (C₀ x) b) ∨
    (∃ m a b C₀, e = .eq m a b ∧ findIte a = none ∧ findIte b = some (s, C₀) ∧
      C = fun x => .eq m a (C₀ x)) := by
  cases e with
  | ite => cases h; exact .inl ⟨rfl, rfl⟩
  | app m f a =>
    simp only [findIte] at h
    split at h
    · rename_i s₀ C₀ hf
      cases h
      exact .inr (.inl ⟨m, f, a, C₀, rfl, hf, rfl⟩)
    · rename_i hf
      split at h
      · obtain ⟨⟨s₀, C₀⟩, ha, ⟨⟩⟩ := Option.map_eq_some_iff.1 h
        exact .inr (.inr (.inl ⟨m, f, a, C₀, rfl, hf, ha, rfl⟩))
      · split at h
        · cases h
          exact .inr (.inr (.inl ⟨m, f, _, id, rfl, hf, rfl, rfl⟩))
        · cases h
  | eq m a b =>
    simp only [findIte] at h
    split at h
    · rename_i s₀ C₀ ha
      cases h
      exact .inr (.inr (.inr (.inl ⟨m, a, b, C₀, rfl, ha, rfl⟩)))
    · rename_i ha
      obtain ⟨⟨s₀, C₀⟩, hb, ⟨⟩⟩ := Option.map_eq_some_iff.1 h
      exact .inr (.inr (.inr (.inr ⟨m, a, b, C₀, rfl, ha, hb, rfl⟩)))
  | _ => simp [findIte] at h

/-- The facts about the conditional `s` that `findIte` finds in `e`, and about `e` with `s`
    replaced (`C s'`): `C s` is `e`; `s` has no free-variable occurrence, operator or
    non-ground annotation `e` does not have; `C s'` has none `e` and `s'` do not have; `C s'`
    keeps the value of `e` when `s'` has the value of `s`; `e` evaluates only when `s` does;
    `s` has a type at which every `s'` of that type gives `C s'` the type of `e`. -/
private theorem findIte_spec : ∀ {e s : Expression.Expr} {C : Expression.Expr → Expression.Expr},
    findIte e = some (s, C) →
    C s = e ∧ (∀ p, p ∈ s.freeVars → p ∈ e.freeVars) ∧
    (∀ o, o ∈ LExpr.getOps s → o ∈ LExpr.getOps e) ∧ (e.AnnGround → s.AnnGround) ∧
    (∀ s', e.AnnGround → s'.AnnGround → (C s').AnnGround) ∧
    (∀ s' p, p ∈ (C s').freeVars → p ∈ e.freeVars ∨ p ∈ s'.freeVars) ∧
    (∀ s' o, o ∈ LExpr.getOps (C s') → o ∈ LExpr.getOps e ∨ o ∈ LExpr.getOps s') ∧
    (∀ (F : Expression.Factory) (σ : SemanticStore Expression) s', e.AnnGround →
      s'.AnnGround → Expression.eval F σ s' = Expression.eval F σ s →
      Expression.eval F σ (C s') = Expression.eval F σ e) ∧
    (∀ (F : Expression.Factory) (σ : SemanticStore Expression) w, e.AnnGround →
      Expression.eval F σ e = some w → ∃ v, Expression.eval F σ s = some v) ∧
    (∀ τ, e.HasTypeA [] τ → ∃ τs, s.HasTypeA [] τs ∧
      ∀ s', s'.HasTypeA [] τs → (C s').HasTypeA [] τ)
  | e, s, C, h => by
    rcases findIte_cases h with ⟨rfl, rfl⟩ | ⟨m, f, a, C₀, rfl, hf, rfl⟩ |
      ⟨m, f, a, C₀, rfl, -, ha, rfl⟩ | ⟨m, a, b, C₀, rfl, ha, rfl⟩ | ⟨m, a, b, C₀, rfl, -, hb, rfl⟩
    · exact ⟨rfl, fun _ h => h, fun _ h => h, id, fun _ _ h => h, fun _ _ h => .inr h,
        fun _ _ h => .inr h, fun _ _ _ _ _ h => h, fun _ _ _ _ h => ⟨_, h⟩,
        fun τ h => ⟨τ, h, fun _ h => h⟩⟩
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := findIte_spec hf
      refine ⟨by simp [e1], fun p hp => by simp [LExpr.freeVars, e2 p hp],
        fun o ho => by simp [LExpr.getOps, e3 o ho], fun hg => e4 hg.1,
        fun s' hg hs' => ⟨e5 s' hg.1 hs', hg.2⟩, fun s' p hp => ?_, fun s' o ho => ?_,
        fun F σ s' hg hs' hv => app_congr hg.1 (e5 s' hg.1 hs') (e8 F σ s' hg.1 hs' hv) rfl,
        fun F σ w hg hw => (LExpr.denoteEval_app_parts hg.1 hw).1.elim fun w h =>
          e9 F σ w hg.1 h, fun τ hT => ?_⟩
      · simp only [LExpr.freeVars, List.mem_append] at hp ⊢
        exact hp.elim (fun h => (e6 s' p h).imp_left .inl) (fun h => .inl (.inr h))
      · simp only [LExpr.getOps, List.mem_append] at ho ⊢
        exact ho.elim (fun h => (e7 s' o h).imp_left .inl) (fun h => .inl (.inr h))
      · obtain ⟨_, hfT, haT⟩ := HasTypeA.app_inv hT
        obtain ⟨τs, hs, hC⟩ := e10 _ hfT
        exact ⟨τs, hs, fun s' h => .app (hC s' h) haT⟩
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := findIte_spec ha
      refine ⟨by simp [e1], fun p hp => by simp [LExpr.freeVars, e2 p hp],
        fun o ho => by simp [LExpr.getOps, e3 o ho], fun hg => e4 hg.2,
        fun s' hg hs' => ⟨hg.1, e5 s' hg.2 hs'⟩, fun s' p hp => ?_, fun s' o ho => ?_,
        fun F σ s' hg hs' hv => app_congr hg.1 hg.1 rfl (e8 F σ s' hg.2 hs' hv),
        fun F σ w hg hw => (LExpr.denoteEval_app_parts hg.1 hw).2.elim fun w h =>
          e9 F σ w hg.2 h, fun τ hT => ?_⟩
      · simp only [LExpr.freeVars, List.mem_append] at hp ⊢
        exact hp.elim (fun h => .inl (.inl h)) (fun h => (e6 s' p h).imp_left .inr)
      · simp only [LExpr.getOps, List.mem_append] at ho ⊢
        exact ho.elim (fun h => .inl (.inl h)) (fun h => (e7 s' o h).imp_left .inr)
      · obtain ⟨_, hfT, haT⟩ := HasTypeA.app_inv hT
        obtain ⟨τs, hs, hC⟩ := e10 _ haT
        exact ⟨τs, hs, fun s' h => .app hfT (hC s' h)⟩
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := findIte_spec ha
      refine ⟨by simp [e1], fun p hp => by simp [LExpr.freeVars, e2 p hp],
        fun o ho => by simp [LExpr.getOps, e3 o ho], fun hg => e4 hg.1,
        fun s' hg hs' => ⟨e5 s' hg.1 hs', hg.2⟩, fun s' p hp => ?_, fun s' o ho => ?_,
        fun F σ s' hg hs' hv => eq_congr hg.1 (e5 s' hg.1 hs') (e8 F σ s' hg.1 hs' hv) rfl,
        fun F σ w hg hw => (LExpr.denoteEval_eq_parts hg.1 hw).1.elim fun w h =>
          e9 F σ w hg.1 h, fun τ hT => ?_⟩
      · simp only [LExpr.freeVars, List.mem_append] at hp ⊢
        exact hp.elim (fun h => (e6 s' p h).imp_left .inl) (fun h => .inl (.inr h))
      · simp only [LExpr.getOps, List.mem_append] at ho ⊢
        exact ho.elim (fun h => (e7 s' o h).imp_left .inl) (fun h => .inl (.inr h))
      · cases hT with
        | eq haT hbT =>
          obtain ⟨τs, hs, hC⟩ := e10 _ haT
          exact ⟨τs, hs, fun s' h => .eq (hC s' h) hbT⟩
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := findIte_spec hb
      refine ⟨by simp [e1], fun p hp => by simp [LExpr.freeVars, e2 p hp],
        fun o ho => by simp [LExpr.getOps, e3 o ho], fun hg => e4 hg.2,
        fun s' hg hs' => ⟨hg.1, e5 s' hg.2 hs'⟩, fun s' p hp => ?_, fun s' o ho => ?_,
        fun F σ s' hg hs' hv => eq_congr hg.1 hg.1 rfl (e8 F σ s' hg.2 hs' hv),
        fun F σ w hg hw => (LExpr.denoteEval_eq_parts hg.1 hw).2.elim fun w h =>
          e9 F σ w hg.2 h, fun τ hT => ?_⟩
      · simp only [LExpr.freeVars, List.mem_append] at hp ⊢
        exact hp.elim (fun h => .inl (.inl h)) (fun h => (e6 s' p h).imp_left .inr)
      · simp only [LExpr.getOps, List.mem_append] at ho ⊢
        exact ho.elim (fun h => .inl (.inl h)) (fun h => (e7 s' o h).imp_left .inr)
      · cases hT with
        | eq haT hbT =>
          obtain ⟨τs, hs, hC⟩ := e10 _ hbT
          exact ⟨τs, hs, fun s' h => .eq haT (hC s' h)⟩

/-- `liftIte` leaves the expression, or replaces it by the conditional of the folded
    instances. -/
private theorem liftIte_cases (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    liftIte fac e = e ∨ ∃ m c m₁ k₁ m₂ k₂ C r₁ r₂,
      findIte e = some (.ite m c (.const m₁ k₁) (.const m₂ k₂), C) ∧ k₁.ty = k₂.ty ∧
      r₁.ty = r₂.ty ∧ opFold fac (C (.const m₁ k₁)) = some r₁ ∧
      opFold fac (C (.const m₂ k₂)) = some r₂ ∧
      liftIte fac e = .ite m c (.const m₁ r₁) (.const m₂ r₂) := by
  unfold liftIte
  split
  · rename_i m c m₁ k₁ m₂ k₂ C hf
    split
    · rename_i r₁ r₂ h₁ h₂
      split
      · rename_i hk
        exact .inr ⟨m, c, m₁, k₁, m₂, k₂, C, r₁, r₂, hf, hk.1, hk.2, h₁, h₂, rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- A folded expression has the value of its fold. -/
private theorem opFold_eval {fac : Lambda.Factory CoreLParams} {F : Expression.Factory}
    {σ : SemanticStore Expression} (hF : F.factory = fac)
    (hB : WellFormedSemanticEvalBool (P := Expression) F) (hC : WellFormedStore σ F)
    {X : Expression.Expr} {r : LConst} (h : opFold fac X = some r) (m : ExpressionMetadata) :
    Expression.eval F σ (.const m r) = Expression.eval F σ X :=
  (LExpr.denoteEval_const (T := CoreLParams) (opFold_wt h)).trans
    ((LExpr.denoteEval_const (T := CoreLParams) (opFold_wt h)).symm.trans
      (coreEvaluator_WellFormedSemanticEvalOp F fac hF hB hC
        (r := .const valueLoc r) (by simp [WPOps.evalOp?, h])))

/-- A literal in the hole of a context that `findIte` returns, where the filled context is typed,
    is well typed: typing inverts through the applications and equalities down to the hole. -/
private theorem wt_of_findIte_typed {e : Expression.Expr} :
    ∀ {s : Expression.Expr} {C : Expression.Expr → Expression.Expr}, findIte e = some (s, C) →
      ∀ {mk : ExpressionMetadata} {k : LConst} {Δ : List LMonoTy} {τ : LMonoTy},
        (C (.const mk k)).HasTypeA Δ τ → k.wt = true := by
  have hc : ∀ {mk k Δ τ}, (LExpr.const mk k : Expression.Expr).HasTypeA Δ τ → k.wt = true :=
    fun h => by cases h; assumption
  induction e with
  | app m f a ihf iha =>
    intro s C hf mk k Δ τ hT
    rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, C₀, he, hf', rfl⟩ |
      ⟨_, _, _, C₀, he, -, ha', rfl⟩ | ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ <;> try cases he
    · exact hc hT
    · exact ihf hf' (HasTypeA.app_inv hT).2.1
    · exact iha ha' (HasTypeA.app_inv hT).2.2
  | eq m a b iha ihb =>
    intro s C hf mk k Δ τ hT
    rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ |
      ⟨_, _, _, C₀, he, ha', rfl⟩ | ⟨_, _, _, C₀, he, -, hb', rfl⟩ <;> try cases he
    · exact hc hT
    · cases hT with | eq h1 _ => exact iha ha' h1
    · cases hT with | eq _ h2 => exact ihb hb' h2
  | _ =>
    intro s C hf mk k Δ τ hT
    rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ |
      ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ <;> try cases he
    exact hc hT

/-- The context that `findIte` returns, filled with a literal, is not an operator: it is the
    literal itself or an application or equality. -/
private theorem findIte_ctx_ne_op {f s : Expression.Expr} {C : Expression.Expr → Expression.Expr}
    (hf : findIte f = some (s, C)) (mk : ExpressionMetadata) (k : LConst) :
    C (.const mk k) ≠ (Lambda.boolNotFunc (T := CoreLParams)).opExpr := by
  rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, rfl⟩ | ⟨_, _, _, _, -, -, rfl⟩ | ⟨_, _, _, _, -, -, -, rfl⟩ <;>
    exact fun h => by cases h

/-- A literal in the hole of a context that `findIte` returns, where `constFold` folds the filled
    context, is well typed: `constFold` reaches the hole through equalities and `Bool.Not`, which
    fold their arguments, and folds a literal only when it is well typed. -/
private theorem wt_of_findIte_constFold {e : Expression.Expr} :
    ∀ {s : Expression.Expr} {C : Expression.Expr → Expression.Expr}, findIte e = some (s, C) →
      ∀ {mk : ExpressionMetadata} {k r : LConst}, constFold (C (.const mk k)) = some r →
        k.wt = true := by
  have hlit : ∀ {mk : ExpressionMetadata} {k r : LConst},
      constFold (.const mk k) = some r → k.wt = true := fun h => by
    simp only [constFold] at h
    split at h
    · assumption
    · cases h
  induction e with
  | app m f a ihf iha =>
    intro s C hf mk k r h
    rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, C₀, he, hf', rfl⟩ |
      ⟨_, _, _, C₀, he, -, ha', rfl⟩ | ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ <;> try cases he
    · exact hlit h
    · simp only [constFold, constFoldApp] at h
      split at h <;> first | exact absurd ‹_› (findIte_ctx_ne_op hf' mk k) | cases h
    · simp only [constFold, constFoldApp] at h
      (repeat' split at h) <;> first | exact iha ha' ‹_› | cases h
  | eq m a b iha ihb =>
    intro s C hf mk k r h
    rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ |
      ⟨_, _, _, C₀, he, ha', rfl⟩ | ⟨_, _, _, C₀, he, -, hb', rfl⟩ <;> try cases he
    · exact hlit h
    · simp only [constFold, constFoldEq] at h
      split at h <;> first | exact iha ha' ‹_› | cases h
    · simp only [constFold, constFoldEq] at h
      split at h <;> first | exact ihb hb' ‹_› | cases h
  | _ =>
    intro s C hf mk k r h
    rcases findIte_cases hf with ⟨-, rfl⟩ | ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ |
      ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, he, _⟩ <;> try cases he
    exact hlit h

/-- **A literal in the hole of a context that `findIte` returns, where the filled context folds,
    is well typed.** `concreteFold` type checks the whole filled context, and `constFold` reaches
    the hole (`wt_of_findIte_typed`, `wt_of_findIte_constFold`). -/
private theorem wt_of_findIte_fold {fac : Lambda.Factory CoreLParams} {e s : Expression.Expr}
    {C : Expression.Expr → Expression.Expr} (hf : findIte e = some (s, C))
    {mk : ExpressionMetadata} {k r : LConst} (h : opFold fac (C (.const mk k)) = some r) :
    k.wt = true := by
  simp only [opFold] at h
  split at h
  · exact wt_of_findIte_constFold hf ‹_›
  · exact wt_of_findIte_typed hf (LExpr.typeCheck_to_HasTypeA (concreteFold_typeCheck h))

/-- A conditional of literals of one type has the value of the literal its condition selects,
    and none when its condition has no Boolean value. -/
private theorem eval_ite_consts {F : Expression.Factory} {σ : SemanticStore Expression}
    {m m₁ m₂ : ExpressionMetadata} {c : Expression.Expr} {k₁ k₂ : LConst} (hk : k₁.ty = k₂.ty)
    (hw₁ : k₁.wt = true) (hw₂ : k₂.wt = true) :
    (∀ b, Expression.eval F σ c = some (SemValue.ofBool F.model.tcInterp b) →
      Expression.eval F σ (.ite m c (.const m₁ k₁) (.const m₂ k₂)) =
        if b then Expression.eval F σ (.const m₁ k₁) else Expression.eval F σ (.const m₂ k₂)) ∧
    ((∀ b, Expression.eval F σ c ≠ some (SemValue.ofBool F.model.tcInterp b)) →
      Expression.eval F σ (.ite m c (.const m₁ k₁) (.const m₂ k₂)) = none) := by
  have h₁ := LExpr.denoteEval_const (T := CoreLParams) (M := F) (σ := σ) (m := m₁) (c := k₁) hw₁
  have h₂ := LExpr.denoteEval_const (T := CoreLParams) (M := F) (σ := σ) (m := m₂) (c := k₂) hw₂
  have hs : (SemValue.ofConst F.model.tcInterp k₁).sort =
      (SemValue.ofConst F.model.tcInterp k₂).sort := by
    simp [SemValue.ofConst, hk]
  refine ⟨fun b hb => ?_, fun hn => Option.eq_none_iff_forall_ne_some.2 fun v hv => ?_⟩
  · show LExpr.denoteEval F σ _ = if b then LExpr.denoteEval F σ _ else LExpr.denoteEval F σ _
    rw [h₁, h₂, LExpr.denoteEval_ite_iff (T := CoreLParams).2 ⟨b, _, _, hb, h₁, h₂, hs, rfl⟩]
    cases b <;> rfl
  · obtain ⟨b, -, -, hb, -⟩ := (LExpr.denoteEval_ite_iff (T := CoreLParams)).1 hv
    exact hn b hb

/-- **An operator into a conditional satisfies the root laws**: the conditional among the parts
    selects the literal its condition gives, the expression with that literal in place has the
    value of its fold, and an expression whose conditional has no value has none. -/
theorem liftIte_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac (liftIte fac) where
  value {F σ e} hF hB hC hg _ := by
    rcases liftIte_cases fac e with h | ⟨m, c, m₁, k₁, m₂, k₂, C, r₁, r₂, hf, hk, hr, h₁, h₂, h⟩ <;>
      rw [h]
    obtain ⟨e1, -, -, -, -, -, -, e8, e9, -⟩ := findIte_spec hf
    have hl₁ := opFold_eval hF hB hC h₁ m₁
    have hl₂ := opFold_eval hF hB hC h₂ m₂
    have hc₁ := e8 F σ (.const m₁ k₁) hg trivial
    have hc₂ := e8 F σ (.const m₂ k₂) hg trivial
    rcases Classical.em (∃ b, Expression.eval F σ c = some (SemValue.ofBool F.model.tcInterp b))
      with ⟨b, hb⟩ | hc
    · rw [(eval_ite_consts hr (opFold_wt h₁) (opFold_wt h₂)).1 b hb]
      have hs := (eval_ite_consts (m := m) (m₁ := m₁) (m₂ := m₂) hk
        (wt_of_findIte_fold hf h₁) (wt_of_findIte_fold hf h₂)).1 b hb
      cases b
      · exact hl₂.trans (hc₂ hs.symm)
      · exact hl₁.trans (hc₁ hs.symm)
    · have hn := fun b h => hc ⟨b, h⟩
      rw [(eval_ite_consts hr (opFold_wt h₁) (opFold_wt h₂)).2 hn]
      refine (Option.eq_none_iff_forall_ne_some.2 fun w hw => ?_).symm
      obtain ⟨v, hv⟩ := e9 F σ w hg hw
      rw [(eval_ite_consts hk (wt_of_findIte_fold hf h₁) (wt_of_findIte_fold hf h₂)).2 hn] at hv
      cases hv
  ground {e} hg := by
    rcases liftIte_cases fac e with h | ⟨m, c, m₁, k₁, m₂, k₂, C, r₁, r₂, hf, -, -, -, -, h⟩
    · rwa [h]
    rw [h]
    exact ⟨((findIte_spec hf).2.2.2.1 hg).1, trivial, trivial⟩
  fvars {e p} hp := by
    rcases liftIte_cases fac e with h | ⟨m, c, m₁, k₁, m₂, k₂, C, r₁, r₂, hf, -, -, -, -, h⟩
    · exact h ▸ hp
    rw [h] at hp
    exact (findIte_spec hf).2.1 p (by simpa [LExpr.freeVars] using hp)
  ops {e o} ho := by
    rcases liftIte_cases fac e with h | ⟨m, c, m₁, k₁, m₂, k₂, C, r₁, r₂, hf, -, -, -, -, h⟩
    · exact h ▸ ho
    rw [h] at ho
    exact (findIte_spec hf).2.2.1 o (by simpa [LExpr.getOps] using ho)
  typed {e τ} hg hfv hT := by
    rcases liftIte_cases fac e with h | ⟨m, c, m₁, k₁, m₂, k₂, C, r₁, r₂, hf, -, -, h₁, h₂, h⟩
    · rwa [h]
    rw [h]
    obtain ⟨-, -, -, -, -, e6, -, -, -, e10⟩ := findIte_spec hf
    obtain ⟨τs, hs, hCt⟩ := e10 τ hT
    obtain ⟨hcT, hk₁, hk₂⟩ := HasTypeA.ite_inv hs
    have hfold {mi : ExpressionMetadata} {k r : LConst}
        (hk : (LExpr.const mi k : Expression.Expr).HasTypeA [] τs)
        (hr : opFold fac (C (.const mi k)) = some r) :
        (LExpr.const mi r : Expression.Expr).HasTypeA [] τ := by
      have hfv' : ∀ x τ?, (x, τ?) ∈ (C (.const mi k)).freeVars →
          ∃ τx, τ? = some τx ∧ τx.IsGround := fun x τ? hx =>
        (e6 _ _ hx).elim (hfv x τ?) fun h => by simp [LExpr.freeVars] at h
      obtain ⟨τ', hτ', -, -, hT'⟩ := (typedOpLaws fac).evalOp (r := .const valueLoc r)
        (by simp [WPOps.evalOp?, hr]) (ty := .forAll [] τ)
        ⟨τ, rfl, hasTypeA_ground hg hfv hT, hfv', hCt _ hk⟩
      cases hτ'
      cases hT'
      exact .const (opFold_wt hr)
    exact .ite hcT (hfold hk₁ h₁) (hfold hk₂ h₂)

/-! ## Contraction of a redex -/

/-- **The contraction of a redex that does not grow the term satisfies the root laws**: its
    argument, self-typed at the type of the bound variable, has a value of that type wherever
    its annotated variables hold values of their annotated types, so the contraction and the
    redex have the same value (`LExpr.denoteEval_subst_beta`). -/
theorem betaNG_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac betaNG where
  value {F σ e} _ _ _ _ hσ := by
    unfold betaNG
    (repeat' split) <;> try rfl
    rename_i m ma n aty b a h
    obtain ⟨-, hs, -⟩ := h
    obtain ⟨w, hw, -, hwt⟩ := selfTyped_eval hs (storeTypes_of_freeVars hσ fun p hp => by
      simp [LExpr.freeVars, hp])
    exact LExpr.denoteEval_subst_beta (T := CoreLParams) hw (Option.some.inj (hwt.symm.trans rfl))
  ground {e} hg := by
    unfold betaNG
    (repeat' split) <;> first | exact hg | exact LExpr.AnnGround.substK hg.2 hg.1.2
  fvars {e p} hp := by
    unfold betaNG at hp
    (repeat' split at hp) <;>
      first | exact hp | simpa [LExpr.freeVars] using LExpr.mem_freeVars_substK hp
  ops {e o} ho := by
    unfold betaNG at ho
    (repeat' split at ho) <;>
      first | exact ho | simpa [LExpr.getOps] using LExpr.mem_getOps_substK ho
  typed {e τ} _ _ hT := by
    unfold betaNG
    (repeat' split) <;> try exact hT
    cases hT with
    | app hf ha =>
      cases hf with
      | abs hb =>
        exact LExpr.typeCheck_to_HasTypeA ((LExpr.typeCheck_substK (HasTypeA_nil_lcAt ha)
          (LExpr.HasTypeA_to_typeCheck ha) _ []).trans (LExpr.HasTypeA_to_typeCheck hb))

/-! ## A tester applied to a constructor -/

/-- A value of `n` arguments that is the denotation of the literal `k` whatever the arguments:
    for `n = 0` the denotation of `k`, for `n + 1` a function from the first argument's sort to
    such a value of `n` arguments. -/
private def ConstVal (tc : TyConstrInterp) (vt : TyVarVal) (k : LConst) :
    (n : Nat) → (τ : LMonoTy) → TyDenote tc vt τ → Prop
  | 0, _, v => HEq v (denoteConst tc vt k)
  | n + 1, .tcons "arrow" [_, b], v => ∀ x, ConstVal tc vt k n b (v x)
  | _ + 1, _, _ => False

/-- An expression that `constRedex` reads as `k` with `n` binders left denotes a value of `n`
    arguments that is the denotation of `k` whatever the arguments. -/
private theorem constRedex_denote {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal CoreLParams tc} {vt : TyVarVal} :
    ∀ {e : Expression.Expr} {n : Nat} {k : LConst}, constRedex e = some (n, k) →
    ∀ {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) {τ : LMonoTy} (h : e.HasTypeA Δ τ),
      ConstVal tc vt k n τ (LExpr.denote tc op fv vt bv e τ h)
  | .const m c, n, k, hr, Δ, bv, τ, h => by
    cases hr
    cases h
    exact HEq.rfl
  | .abs m nm (some aty) b, n, k, hr, Δ, bv, τ, h => by
    obtain ⟨⟨n', k'⟩, hb, ⟨⟩⟩ := Option.map_eq_some_iff.1 hr
    cases h with
    | abs hB =>
      rw [denote_abs bv hB]
      exact fun x => constRedex_denote hb (.cons x bv) hB
  | .app m f a, n, k, hr, Δ, bv, τ, h => by
    simp only [constRedex] at hr
    split at hr <;> try cases hr
    rename_i hf
    cases h with
    | app hF hA =>
      rw [denote_app bv hF hA]
      exact constRedex_denote hf bv hF _

/-- A literal that `constRedex` finds in an expression that type checks is well typed: the
    literal is a typed part of the expression. -/
private theorem constRedex_wt {r : Expression.Expr} :
    ∀ {n : Nat} {k : LConst} {Δ : List LMonoTy} {τ : LMonoTy},
      constRedex r = some (n, k) → LExpr.typeCheck Δ r = some τ → k.wt = true := by
  induction r with
  | const m k' =>
    intro n k Δ τ h ht
    cases h
    cases LExpr.typeCheck_to_HasTypeA ht with
    | const hw => exact hw
  | abs m nm ty b ih =>
    intro n k Δ τ h ht
    cases ty with
    | none => cases h
    | some ty =>
      obtain ⟨⟨n', k'⟩, hb, ⟨⟩⟩ := Option.map_eq_some_iff.1 h
      cases LExpr.typeCheck_to_HasTypeA ht with
      | abs hb' => exact ih hb (LExpr.HasTypeA_to_typeCheck hb')
  | app m f a ihf _ =>
    intro n k Δ τ h ht
    simp only [constRedex] at h
    split at h <;> try cases h
    rename_i hf
    exact ihf hf
      (LExpr.HasTypeA_to_typeCheck (HasTypeA.app_inv (LExpr.typeCheck_to_HasTypeA ht)).2.1)
  | _ => nofun

/-- An application that `bodyFold fac` folds to `k` type checks at the type of `k`, annotates
    every free-variable occurrence, and denotes, under every model of `fac`, the denotation of
    `k`. -/
private theorem bodyFold_spec {fac : Lambda.Factory CoreLParams} {e : Expression.Expr}
    {k : LConst} (h : bodyFold fac e = some k) :
    LExpr.typeCheck [] e = some k.ty ∧ (e.freeVars.all fun p => p.2.isSome) = true ∧
      (∀ (model : Lambda.Interp fac) (fv : FreeVarVal CoreLParams model.tcInterp)
        (vt : TyVarVal) {τ : LMonoTy} (hT : e.HasTypeA [] τ),
        HEq (LExpr.denote model.tcInterp model.opInterp fv vt .nil e τ hT)
          (denoteConst model.tcInterp vt k)) ∧ k.wt = true := by
  unfold bodyFold at h
  repeat' split at h
  all_goals try cases h
  rename_i _ m mo t τt a _ tf htf _ _ x xty body hin hb hc _ mel el τel args ef hcall hc2 _ r hce _
    hk hc3
  obtain ⟨hname, rfl, hann, hbT, hbx⟩ := hc
  obtain ⟨hname2, hS⟩ := hc2
  obtain ⟨heT, hrT⟩ := hc3
  refine ⟨heT, hann, fun model fv vt τ hT => ?_, constRedex_wt hk hrT⟩
  have hmem := Lambda.Factory.getElem?_some_implies_mem htf
  have hget := Lambda.Factory.getElem?_some_getElem htf
  have hIC := model.interpConsistent.1 t.name hmem body (by rw [hget]; exact hb)
  rw [hget] at hIC
  unfold LFunc.InterpConsistentBody at hIC
  generalize hI : tf.inputs = ins at hIC
  obtain rfl : ins = [(x, xty)] := hI ▸ hin
  rw [hname] at hIC
  obtain ⟨aty, hop, ha⟩ := HasTypeA.app_inv hT
  have hτ := HasTypeA.op_inv hop
  simp only [LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq, and_true, true_and] at hτ
  obtain ⟨rfl, rfl⟩ := hτ
  have hbody := LExpr.typeCheck_to_HasTypeA hbT
  have h1 := hIC vt fv hbody
    (.cons (LExpr.denote model.tcInterp model.opInterp fv vt .nil a aty ha) .nil)
  rw [denote_app .nil hop ha, denote_op]
  refine HEq.trans (heq_of_eq h1) ?_
  have hlc := HasTypeA_nil_lcAt ha
  have hxa : ∀ {y tyo}, (y, tyo) ∈ body.freeVars → y = x → tyo = some aty := fun hy hyx => by
    simpa [hyx] using List.all_eq_true.1 hbx _ hy
  have htc : ∀ y tyo r, (y, tyo) ∈ body.freeVars →
      (fun y => if y = x then some a else none) y = some r → ∀ Δ', LExpr.typeCheck Δ' r = tyo := by
    intro y tyo r hy hl Δ'
    dsimp only at hl
    split at hl <;> cases hl
    rw [typeCheck_of_lcAt hlc, LExpr.HasTypeA_to_typeCheck ha, hxa hy ‹_›]
  have hB' := LExpr.HasTypeA_substFvarsBy htc hbody
  have h2 := denote_substFvarsBy (op := model.opInterp) (vt := vt) (fv' := fv)
    (fv := IdentInterp.withArgs fv [(x, aty.substTyVars vt)]
      (.cons (LExpr.denote model.tcInterp model.opInterp fv vt .nil a aty ha) .nil))
    (fun y => if y = x then some a else none) .nil htc
    (fun y ty r hy hl Δ' bv' hr => by
      dsimp only at hl
      split at hl <;> cases hl
      rename_i hyx
      cases Option.some.inj (hxa hy hyx)
      subst hyx
      unfold IdentInterp.withArgs
      simp only [↓reduceIte, ↓reduceDIte]
      exact denote_irrel_of_lcAt _ _ _ _ hlc hr ha bv' .nil)
    (fun y ty hy hl => by
      dsimp only at hl
      split at hl <;> try cases hl
      unfold IdentInterp.withArgs
      simp only [‹¬y = x›, ↓reduceIte]
      rfl) hbody hB'
  refine HEq.trans (heq_of_eq h2.symm) ?_
  have hkt : tf.output = k.ty := Option.some.inj ((LExpr.HasTypeA_to_typeCheck hT).symm.trans heT)
  obtain ⟨argTys, ty_op, m', name, h_args, hty_op, hcallee, hden⟩ :=
    callOfLFunc_denote model.tcInterp model.opInterp fv vt hcall hB'
  cases hcallee
  obtain ⟨m0, nm, ty0, hcl0, hlook⟩ := Factory.callOfLFunc_getElem? hcall
  cases hcl0
  obtain ⟨S, hS'⟩ := Option.isSome_iff_exists.1 hS
  have hty := (subst_mkArrow' S _ _).symm.trans (tyInst?_subst hS')
  have hlen : argTys.length = ef.inputs.length :=
    h_args.length_eq.symm.trans (Factory.callOfLFunc_arity hcall)
  obtain ⟨hout, hins⟩ := LMonoTy.mkArrow'_injective
    (hlen.trans ((List.length_map _).trans (List.length_map _)).symm) (hty_op.symm.trans hty.symm)
  subst hins
  have hres : r.HasTypeA [] (ef.output.subst S) :=
    hout ▸ hkt ▸ LExpr.typeCheck_to_HasTypeA hrT
  have hci := opInterp_of_concreteEval_subst model hlook hname2 S (by rw [hty]; exact hce) vt fv
    h_args hres
  have hop : ∀ {s1 s2 : LSort} (_ : s1 = s2),
      HEq (model.opInterp el.name s1) (model.opInterp el.name s2) := fun h => h ▸ .rfl
  have happ : ∀ {L L' : List LSort} {r r' : LSort} (_ : L = L') (_ : r = r')
      {f : SortDenote model.tcInterp (LSort.mkArrow r L)}
      {f' : SortDenote model.tcInterp (LSort.mkArrow r' L')} (_ : HEq f f')
      {xs : HList (SortDenote model.tcInterp) L} {xs' : HList (SortDenote model.tcInterp) L'}
      (_ : HEq xs xs'),
      HEq (SortDenote.applyArgs model.tcInterp f xs)
        (SortDenote.applyArgs model.tcInterp f' xs') := by
    rintro L _ r _ rfl rfl f _ ⟨⟩ xs _ ⟨⟩
    rfl
  refine (heq_of_eq hden).trans ((happ rfl ?_ ((eqRec_heq _ _).trans (hop ?_)) HEq.rfl).trans
    ((heq_of_eq hci).symm.trans ?_))
  · exact congrArg _ hout
  · rw [hty_op, substTyVars_mkArrow', hout]
  · exact constRedex_denote hk .nil hres

/-- **A tester applied to a constructor satisfies the root laws**: the application that
    `bodyFold fac` folds has, in a store holding values of its annotated types, the value of its
    denotation, which every model of `fac` makes the denotation of the literal it folds to. -/
theorem testCtor_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac (testCtor fac) where
  value {F σ e} hF _ _ _ hσ := by
    unfold testCtor
    split
    · rename_i k hk
      subst hF
      obtain ⟨heT, hann, hD, hkw⟩ := bodyFold_spec hk
      have hT := LExpr.typeCheck_to_HasTypeA heT
      have hσ' : ∀ x τ, (x, some τ) ∈ e.freeVars →
          ∃ v, σ x = some v ∧ HasVal.valueOfTy F v (.forAll [] τ) := fun x τ hx =>
        hσ x _ (List.mem_filterMap.2 ⟨(x, some τ), hx, rfl⟩)
      have hself : e.annotateFvars (ValStore.ann (T := CoreLParams) σ) = e :=
        LExpr.annotateFvars_eq_self e fun x τ? hx => by
          obtain ⟨τx, rfl⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hann _ hx)
          obtain ⟨v, hv, -, hs⟩ := hσ' x τx hx
          exact ⟨τx, rfl, by simpa [ValStore.ann, hv, LTy.toMonoType?] using hs.symm⟩
      have hd : ValStore.Defines (T := CoreLParams) σ F.model.tcInterp e := fun x hx => by
        obtain ⟨⟨x', τ?⟩, hx', rfl⟩ := List.mem_map.1 (getVars_eq_freeVars_idents (e := e) ▸ hx)
        obtain ⟨τx, rfl⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hann _ hx')
        exact (hσ' x' τx hx').imp fun _ ⟨hv, htc, _⟩ => ⟨hv, htc⟩
      have hg : k.ty.IsGround := LConst.ty_isGround k
      show LExpr.denoteEval F σ (.const valueLoc k) = LExpr.denoteEval F σ e
      rw [LExpr.denoteEval_const (T := CoreLParams) hkw,
        LExpr.denoteEval_of_hasTypeA hd (hself.symm ▸ hT) hg]
      unfold LExpr.denoteEvalResult
      letI := F.model.allInhabited
      have hkey : ∀ e' (he : e' = e) (h' : e'.HasTypeA [] k.ty),
          HEq (LExpr.denote F.model.tcInterp F.model.opInterp
            (ValStore.fvarVal F.model.tcInterp σ) F.tyVarVal .nil e' k.ty h')
            (denoteConst F.model.tcInterp F.tyVarVal k) := by
        rintro _ rfl h'
        exact hD F.model _ F.tyVarVal h'
      refine congrArg some (SemValue.mk_eq_mk (hg.substTyVars_eq _ _) ?_)
      refine HEq.trans ?_ (hkey _ hself _).symm
      rw [denoteConst_cast_vt F.model.tcInterp refTyVarVal F.tyVarVal k
        (congrArg (SortDenote F.model.tcInterp) (hg.substTyVars_eq _ _))]
      exact cast_heq _ _
    · rfl
  ground {e} hg := by
    unfold testCtor
    split <;> first | exact hg | trivial
  fvars {e p} hp := by
    unfold testCtor at hp
    split at hp <;> first | exact hp | simp [LExpr.freeVars] at hp
  ops {e o} ho := by
    unfold testCtor at ho
    split at ho <;> first | exact ho | simp [LExpr.getOps] at ho
  typed {e τ} _ _ hT := by
    unfold testCtor
    split
    · rename_i k hk
      cases Option.some.inj ((LExpr.HasTypeA_to_typeCheck hT).symm.trans (bodyFold_spec hk).1)
      exact .const (bodyFold_spec hk).2.2.2
    · exact hT

/-- **The rewrites at the root satisfy the root laws**: `rwRoot fac` is a composition of root
    rewrites, each of which keeps values, ground annotations, free variables, operators and
    types, so the composition keeps them too. -/
theorem rwRoot_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac (rwRoot fac) :=
  (((((betaNG_laws fac).comp (decEq_laws fac)).comp (foldOp_laws fac)).comp
    (liftIte_laws fac)).comp (iteSame_laws fac)).comp (testCtor_laws fac)

/-! ## The bottom-up rewrite -/

/-- The laws of a rewrite of `x` into `y`, for the factory of functions `fac`: the root laws
    (`RootLaws`) at the one expression `x`. -/
structure RelLaws (fac : Lambda.Factory CoreLParams) (x y : Expression.Expr) : Prop where
  /-- The rewrite keeps the value. -/
  value : ∀ {F : Expression.Factory} {σ : SemanticStore Expression}, F.factory = fac →
    WellFormedSemanticEvalBool (P := Expression) F → WellFormedStore σ F → x.AnnGround →
    StoreTypes F σ x → Expression.eval F σ y = Expression.eval F σ x
  /-- The rewrite keeps the ground annotations. -/
  ground : x.AnnGround → y.AnnGround
  /-- The rewrite adds no free-variable occurrence. -/
  fvars : ∀ {p}, p ∈ y.freeVars → p ∈ x.freeVars
  /-- The rewrite adds no operator. -/
  ops : ∀ {o}, o ∈ LExpr.getOps y → o ∈ LExpr.getOps x
  /-- The rewrite keeps the annotated type. -/
  typed : ∀ {τ : LMonoTy}, x.AnnGround →
    (∀ z τ?, (z, τ?) ∈ x.freeVars → ∃ τz, τ? = some τz ∧ τz.IsGround) →
    x.HasTypeA [] τ → y.HasTypeA [] τ

/-- A rewrite satisfying the root laws satisfies them at each expression. -/
theorem RootLaws.rel {fac : Lambda.Factory CoreLParams} {r : Expression.Expr → Expression.Expr}
    (h : RootLaws fac r) (x : Expression.Expr) : RelLaws fac x (r x) :=
  ⟨h.value, h.ground, h.fvars, h.ops, h.typed⟩

/-- An expression left as it is. -/
theorem RelLaws.refl {fac : Lambda.Factory CoreLParams} {x : Expression.Expr} : RelLaws fac x x :=
  ⟨fun _ _ _ _ _ => rfl, id, id, id, fun _ _ => id⟩

/-- **Moving an expression to a new root location satisfies the laws**: the value, the ground
    annotations, the free-variable occurrences, the operators and the typing of an expression do
    not depend on the location at its root. Substitution places each substituted expression at
    the location of the occurrence it replaces. -/
theorem RelLaws.replaceMetadata1 {fac : Lambda.Factory CoreLParams} (m : ExpressionMetadata)
    (v : Expression.Expr) : RelLaws fac (LExpr.replaceMetadata1 m v) v where
  value _ _ _ _ _ := (LExpr.denoteEval_replaceMetadata1 _ _ m v).symm
  ground hg := by cases v <;> exact hg
  fvars hp := by cases v <;> exact hp
  ops ho := by cases v <;> exact ho
  typed _ _ hT := by cases v <;> cases hT <;> constructor <;> assumption

/-- Two rewrites in turn. -/
theorem RelLaws.trans {fac : Lambda.Factory CoreLParams} {x y z : Expression.Expr}
    (h₁ : RelLaws fac x y) (h₂ : RelLaws fac y z) : RelLaws fac x z where
  value hF hB hC hg hσ := (h₂.value hF hB hC (h₁.ground hg)
    (storeTypes_of_freeVars hσ fun _ => h₁.fvars)).trans (h₁.value hF hB hC hg hσ)
  ground hg := h₂.ground (h₁.ground hg)
  fvars hp := h₁.fvars (h₂.fvars hp)
  ops ho := h₁.ops (h₂.ops ho)
  typed hg hfv hT := h₂.typed (h₁.ground hg) (fun z τ? hz => hfv z τ? (h₁.fvars hz))
    (h₁.typed hg hfv hT)

/-- The parts of an application rewritten. -/
theorem RelLaws.app {fac : Lambda.Factory CoreLParams} {m : ExpressionMetadata}
    {f f' a a' : Expression.Expr}
    (hf : RelLaws fac f f') (ha : RelLaws fac a a') :
    RelLaws fac (.app m f a) (.app m f' a') where
  value hF hB hC hg hσ := app_congr hg.1 (hf.ground hg.1)
    (hf.value hF hB hC hg.1 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
    (ha.value hF hB hC hg.2 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
  ground hg := ⟨hf.ground hg.1, ha.ground hg.2⟩
  fvars hp := by
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    exact hp.imp hf.fvars ha.fvars
  ops ho := by
    simp only [LExpr.getOps, List.mem_append] at ho ⊢
    exact ho.imp hf.ops ha.ops
  typed hg hfv hT := by
    cases hT with
    | app hfT haT =>
      exact .app (hf.typed hg.1 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) hfT)
        (ha.typed hg.2 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) haT)

/-- The parts of a conditional rewritten. -/
theorem RelLaws.ite {fac : Lambda.Factory CoreLParams} {m : ExpressionMetadata}
    {c c' t t' e e' : Expression.Expr} (hc : RelLaws fac c c') (ht : RelLaws fac t t')
    (he : RelLaws fac e e') : RelLaws fac (.ite m c t e) (.ite m c' t' e') where
  value hF hB hC hg hσ := LExpr.denoteEval_ite_congr
    (hc.value hF hB hC hg.1 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
    (ht.value hF hB hC hg.2.1 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
    (he.value hF hB hC hg.2.2 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
  ground hg := ⟨hc.ground hg.1, ht.ground hg.2.1, he.ground hg.2.2⟩
  fvars hp := by
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    exact hp.imp (·.imp hc.fvars ht.fvars) he.fvars
  ops ho := by
    simp only [LExpr.getOps, List.mem_append] at ho ⊢
    exact ho.imp (·.imp hc.ops ht.ops) he.ops
  typed hg hfv hT := by
    obtain ⟨hcT, htT, heT⟩ := HasTypeA.ite_inv hT
    exact .ite (hc.typed hg.1 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) hcT)
      (ht.typed hg.2.1 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) htT)
      (he.typed hg.2.2 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) heT)

/-- The sides of an equality rewritten. -/
theorem RelLaws.eq {fac : Lambda.Factory CoreLParams} {m : ExpressionMetadata}
    {a a' b b' : Expression.Expr}
    (ha : RelLaws fac a a') (hb : RelLaws fac b b') :
    RelLaws fac (.eq m a b) (.eq m a' b') where
  value hF hB hC hg hσ := eq_congr hg.1 (ha.ground hg.1)
    (ha.value hF hB hC hg.1 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
    (hb.value hF hB hC hg.2 (storeTypes_of_freeVars hσ fun p hp => by simp [LExpr.freeVars, hp]))
  ground hg := ⟨ha.ground hg.1, hb.ground hg.2⟩
  fvars hp := by
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    exact hp.imp ha.fvars hb.fvars
  ops ho := by
    simp only [LExpr.getOps, List.mem_append] at ho ⊢
    exact ho.imp ha.ops hb.ops
  typed hg hfv hT := by
    cases hT with
    | eq haT hbT =>
      exact .eq (ha.typed hg.1 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) haT)
        (hb.typed hg.2 (fun z τ? hz => hfv z τ? (by simp [LExpr.freeVars, hz])) hbT)

/-- **The bottom-up rewrite at a root rewrite satisfying the root laws satisfies them** at `e`
    with `g` substituted: the leaves `g` substitutes are left as they are, every other node is
    rewritten by `root` after its parts. -/
theorem rwBelowWith_rel {fac : Lambda.Factory CoreLParams}
    {root : Expression.Expr → Expression.Expr} (hr : RootLaws fac root)
    (g : Expression.Ident → Option Expression.Expr) :
    ∀ e : Expression.Expr, RelLaws fac (e.substFvarsBy g) (rwBelowWith root g e)
  | .app _ f a => ((rwBelowWith_rel hr g f).app (rwBelowWith_rel hr g a)).trans (hr.rel _)
  | .ite _ c t e =>
    ((rwBelowWith_rel hr g c).ite (rwBelowWith_rel hr g t) (rwBelowWith_rel hr g e)).trans
      (hr.rel _)
  | .eq _ a b => ((rwBelowWith_rel hr g a).eq (rwBelowWith_rel hr g b)).trans (hr.rel _)
  | .fvar m x ty => by
    show RelLaws fac _ (leafRwWith root g (.fvar m x ty))
    cases hx : g x <;> simp only [leafRwWith, LExpr.substFvarsBy, hx, Option.getD]
    · exact hr.rel _
    · exact RelLaws.replaceMetadata1 m _
  | .const .. | .op .. | .bvar .. | .abs .. | .quant .. => hr.rel _

/-! ## The normalizations

`rwAll fac` is the bottom-up rewrite at `rwRoot fac`, and `rwAllC fac`, the normalization of the
constructor fold, the bottom-up rewrite at `ctorRoot fac`, which is `rwRoot fac` followed by
`iteLit` and so satisfies the root laws by `RootLaws.comp` (`ctorRoot_laws`).  The laws below
hold for the bottom-up rewrite at any root rewrite satisfying the root laws. -/

/-- **The root rewrite of the constructor fold satisfies the root laws**: those of `rwRoot fac`
    and of `iteLit`, in turn. -/
theorem ctorRoot_laws (fac : Lambda.Factory CoreLParams) : RootLaws fac (ctorRoot fac) :=
  (rwRoot_laws fac).comp (iteLit_laws fac)

/-- The bottom-up rewrite, at a root rewrite satisfying the root laws, of an expression whose
    substituted form passes `annGround` passes `annGround`. -/
theorem annGround_rwBelowWith {fac : Lambda.Factory CoreLParams}
    {root : Expression.Expr → Expression.Expr} (hr : RootLaws fac root)
    {g : Expression.Ident → Option Expression.Expr} {e : Expression.Expr}
    (h : annGround (e.substFvarsBy g) = true) : annGround (rwBelowWith root g e) = true :=
  annGround_of_ground ((rwBelowWith_rel hr g e).ground (annGround_ground h))

/-- The bottom-up rewrite at a root rewrite satisfying the root laws adds no free-variable
    occurrence to the substituted expression. -/
theorem rwAllWith_freeVars {fac : Lambda.Factory CoreLParams}
    {root : Expression.Expr → Expression.Expr} (hr : RootLaws fac root)
    {g : Expression.Ident → Option Expression.Expr} {e : Expression.Expr} {p}
    (hp : p ∈ (rwAllWith root g e).freeVars) : p ∈ (e.substFvarsBy g).freeVars := by
  unfold rwAllWith at hp
  split at hp <;> first | exact (rwBelowWith_rel hr g e).fvars hp | exact hp

/-- The bottom-up rewrite at a root rewrite satisfying the root laws adds no operator to the
    substituted expression. -/
theorem rwAllWith_ops {fac : Lambda.Factory CoreLParams}
    {root : Expression.Expr → Expression.Expr} (hr : RootLaws fac root)
    {g : Expression.Ident → Option Expression.Expr} {e : Expression.Expr} {o}
    (ho : o ∈ LExpr.getOps (rwAllWith root g e)) : o ∈ LExpr.getOps (e.substFvarsBy g) := by
  unfold rwAllWith at ho
  split at ho <;> first | exact (rwBelowWith_rel hr g e).ops ho | exact ho

/-- **The bottom-up rewrite at a root rewrite satisfying the root laws keeps the values of
    substituted expressions in typed stores**, under a factory whose functions are those of `fac`
    and whose evaluator respects Boolean negation. -/
theorem rwAllWith_normLawT {fac : Lambda.Factory CoreLParams}
    {root : Expression.Expr → Expression.Expr} (hr : RootLaws fac root) {F : Expression.Factory}
    (hF : F.factory = fac) (hB : WellFormedSemanticEvalBool (P := Expression) F) :
    SubstNormLawT F (rwAllWith root) := by
  intro σ g e hC hσ
  unfold rwAllWith
  split <;> first | exact (rwBelowWith_rel hr g e).value hF hB hC (annGround_ground ‹_›) hσ | rfl

/-- **The bottom-up rewrite at a root rewrite satisfying the root laws keeps types**: it rewrites
    a substituted expression typed at `ty` (`Core.Expression.Typed`) into one typed at `ty`. -/
theorem rwAllWith_typed {fac : Lambda.Factory CoreLParams}
    {root : Expression.Expr → Expression.Expr} (hr : RootLaws fac root) :
    SubstNormTyped Expression.Typed (rwAllWith root) := by
  intro g e ty ⟨τ, hτ, hg, hfv, hT⟩
  refine ⟨τ, hτ, hg, fun x τ? hx => hfv x τ? (rwAllWith_freeVars hr hx), ?_⟩
  unfold rwAllWith
  split <;> first | exact (rwBelowWith_rel hr g e).typed (annGround_ground ‹_›) hfv hT | exact hT

end -- public section

end DefInline
end Core
