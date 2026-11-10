/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.WellTyped
public import Strata.Transform.Passive.CoreLang
public import Strata.Transform.Passive.LangProps
import all Strata.Transform.Passive.CoreLang
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
public import Strata.Languages.Core.InstExprTyping

/-! # Typed Core expressions

A Core expression is *typed* at a type scheme `ty` (`Core.Expression.Typed`) when `ty` is a
ground monomorphic type `τ`, every free-variable occurrence of the expression carries a ground
type annotation, and the expression, with its own annotations, has type `τ`.  The judgment reads
nothing but the expression, so the phases that rewrite right-hand sides keep it through local
laws (`Core.typedLaws`, the `Imperative.WP.TypedLaws` of Core expressions).
A typed expression evaluates, in a store holding at each annotated free-variable
occurrence a value of the annotated type, to a value of its type (`Core.eval_of_typed`).

Key definitions: `Core.Expression.Typed`.

Key theorems: `Core.typedLaws`, `Core.eval_of_typed`. -/

namespace Core

open Imperative Imperative.WP Lambda Core.WP

public section

/-- **Typed Core expressions.**  `e` has the ground monomorphic type of the scheme `ty`, with
    every free-variable occurrence annotated with a ground type, under its own annotations. -/
@[expose] def Expression.Typed (e : Expression.Expr) (ty : Expression.Ty) : Prop :=
  ∃ τ, ty.toMonoType? = some τ ∧ τ.IsGround ∧
    (∀ x τ?, (x, τ?) ∈ LExpr.freeVars e → ∃ τx, τ? = some τx ∧ τx.IsGround) ∧ e.HasTypeA [] τ

/-- An annotated free-variable occurrence of a Core expression is one of its annotated
    occurrences as a monomorphic type scheme. -/
private theorem mem_typedFvars {e : Expression.Expr} {x : Expression.Ident} {τ : LMonoTy}
    (h : (x, some τ) ∈ LExpr.freeVars e) :
    (x, LTy.forAll [] τ) ∈ HasFvars.getTypedFvars (P := Expression) e :=
  List.mem_filterMap.2 ⟨(x, some τ), h, rfl⟩

/-- **The typing laws of Core expressions**: the `TypedLaws` of `Core.Expression.Typed`. -/
theorem typedLaws :
    TypedLaws (P := Expression) Expression.Typed where
  ite {c t f ty} := by
    change Expression.Typed (.ite () c t f) ty ↔ _
    constructor
    · rintro ⟨τ, hτ, hg, ha, hT⟩
      obtain ⟨hc, ht, hf⟩ := HasTypeA.ite_inv hT
      simp only [LExpr.freeVars, List.mem_append] at ha
      exact ⟨⟨.bool, rfl, rfl, fun x τ? hx => ha x τ? (.inl (.inl hx)), hc⟩,
        ⟨τ, hτ, hg, fun x τ? hx => ha x τ? (.inl (.inr hx)), ht⟩,
        ⟨τ, hτ, hg, fun x τ? hx => ha x τ? (.inr hx), hf⟩⟩
    · rintro ⟨⟨τc, hτc, -, hac, hc⟩, ⟨τ, hτ, hg, hat, ht⟩, ⟨τ', hτ', -, haf, hf⟩⟩
      cases hτc
      cases Option.some.inj (hτ'.symm.trans hτ)
      refine ⟨τ, hτ, hg, fun x τ? hx => ?_, .ite hc ht hf⟩
      simp only [LExpr.freeVars, List.mem_append] at hx
      exact hx.elim (·.elim (hac x τ?) (hat x τ?)) (haf x τ?)
  substFn {e ty} g he hg := by
    obtain ⟨τ, hτ, hgr, ha, hT⟩ := he
    have himg : ∀ x τx r, (x, some τx) ∈ LExpr.freeVars e → g x = some r →
        Expression.Typed r (.forAll [] τx) := fun x τx r hx hr =>
      hg (x, .forAll [] τx) (mem_typedFvars hx) r hr
    refine ⟨τ, hτ, hgr, fun x τ? hx => ?_,
      LExpr.HasTypeA_substFvarsBy (fun x tyo r hx hr Δ' => ?_) hT⟩
    · rcases LExpr.mem_freeVars_substFvarsBy hx with ⟨hx, -⟩ | ⟨y, tyy, r, hy, hgy, hr⟩
      · exact ha x τ? hx
      · obtain ⟨τy, rfl, -⟩ := ha y tyy hy
        obtain ⟨-, -, -, har, -⟩ := himg y τy r hy hgy
        exact har x τ? hr
    · obtain ⟨τx, rfl, -⟩ := ha x tyo hx
      obtain ⟨τr, hτr, -, -, hTr⟩ := himg x τx r hx hr
      cases hτr
      exact LExpr.HasTypeA_to_typeCheck (HasTypeA_append_right hTr Δ')
  typedFvars_ite {c t f p} h := by
    change p ∈ Expression.typedFvars (.ite () c t f)
    change p ∈ Expression.typedFvars c ∨ p ∈ Expression.typedFvars t ∨
      p ∈ Expression.typedFvars f at h
    simpa [Expression.typedFvars, LExpr.freeVars, List.filterMap_append, or_assoc] using h
  getFvar {e ty y} hy he := by
    obtain ⟨τ, hτ, -, ha, hT⟩ := he
    cases e <;> simp only [HasFvar.getFvar, reduceCtorEq, Option.some.injEq] at hy
    subst hy
    rename_i m ann
    obtain ⟨τx, rfl, -⟩ := ha m ann (by simp [LExpr.freeVars])
    cases hT
    cases ty with
    | forAll vs t =>
      cases vs with
      | nil =>
        cases hτ
        exact List.mem_filterMap.2 ⟨(_, some _), by simp [LExpr.freeVars], rfl⟩
      | cons => simp [LTy.toMonoType?] at hτ
  var {e ty p} y he hp := by
    obtain ⟨⟨x, τ?⟩, hx, hp⟩ := List.mem_filterMap.1 hp
    obtain ⟨-, -, -, ha, -⟩ := he
    obtain ⟨τx, rfl, hg⟩ := ha x τ? hx
    cases hp
    refine ⟨τx, rfl, hg, fun z τz hz => ?_, .fvar⟩
    simp only [HasFvar.mkVar, HasFvar.mkTypedFvar, LTy.toMonoType?, LExpr.freeVars,
      List.mem_singleton, Prod.mk.injEq] at hz
    exact ⟨τx, hz.2, hg⟩

/-- **A typed expression evaluates.**  A Core expression typed at `ty` evaluates, in a store
    binding the variable of each annotated free-variable occurrence to a value of the annotated
    type, to a value of type `ty`. -/
theorem eval_of_typed (f : Expression.Factory) (σ : SemanticStore Expression) {e : Expression.Expr}
    {ty : Expression.Ty} (he : Expression.Typed e ty)
    (hσ : ∀ x τ, (x, some τ) ∈ LExpr.freeVars e →
      ∃ v, σ x = some v ∧ HasVal.valueOfTy f v (.forAll [] τ)) :
    ∃ v, Expression.eval f σ e = some v ∧ HasVal.valueOfTy f v ty := by
  obtain ⟨τ, hτ, hg, ha, hT⟩ := he
  have hself : e.annotateFvars (ValStore.ann (T := CoreLParams) σ) = e :=
    LExpr.annotateFvars_eq_self e fun x τ? hx => by
      obtain ⟨τx, rfl, -⟩ := ha x τ? hx
      obtain ⟨v, hv, -, hs⟩ := hσ x τx hx
      exact ⟨τx, rfl, by simpa [ValStore.ann, hv, LTy.toMonoType?] using hs.symm⟩
  have hd : ValStore.Defines (T := CoreLParams) σ f.model.tcInterp e := fun x hx => by
    obtain ⟨⟨x', τ?⟩, hx', rfl⟩ := List.mem_map.1 (getVars_eq_freeVars_idents (e := e) ▸ hx)
    obtain ⟨τx, rfl, -⟩ := ha x' τ? hx'
    obtain ⟨v, hv, htc, -⟩ := hσ x' τx hx'
    exact ⟨v, hv, htc⟩
  refine ⟨_, LExpr.denoteEval_of_hasTypeA hd (hself.symm ▸ hT :) hg, rfl, ?_⟩
  show ty.toMonoType? = some (τ.substTyVars f.tyVarVal).toMonoTy
  rw [hg.substTyVars_eq f.tyVarVal refTyVarVal, hg, hτ]

/-- Core's conditionals are strict: a conditional evaluates when both of its branches do, to
    values of one type (`LExpr.denoteEval_ite_iff`). -/
instance : WPIteLang Expression where
  ev_ite_true {_ _ _ _ _ v w _} hc ht he hv hw :=
    (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr ⟨true, v, w, hc, ht, he,
      LSort.toMonoTy_injective (Option.some.inj (hv.2.symm.trans hw.2)), rfl⟩
  ev_ite_false {_ _ _ _ _ v w _} hc ht he hv hw :=
    (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr ⟨false, w, v, hc, ht, he,
      LSort.toMonoTy_injective (Option.some.inj (hw.2.symm.trans hv.2)), rfl⟩

/-- Core's typed expressions evaluate (`Core.eval_of_typed`). -/
@[expose] def typedEval : TypedEval Expression where
  Typ := Expression.Typed
  eval_of_typed he hσ := eval_of_typed _ _ he
    fun x τ hx => hσ _ (List.mem_filterMap.2 ⟨(x, some τ), hx, rfl⟩)
  valueOfTy_bool h := Core.valueOfTy_bool _ _ h

/-- **A well-typed Core statement list**, under the typing `Γ` of the names in scope at its
    entry: `Imperative.Block.WellTyped` for the typed Core expressions (`Expression.Typed`) and
    the ground monomorphic types.  Every expression of `ss` has its type under its own
    annotations, every annotation agrees with `Γ` and the declarations of `ss`, and the
    nondeterministic assignments write variables of ground types.  No theorem derives it from
    `Core.typeCheck`; `Core.WP.TypeCheckWPWellTyped` states that type checking establishes it
    for the contract-wrapped body of a procedure under the types of its parameters. -/
@[expose] def Statements.WellTyped (Γ : VarTyping Expression) (ss : Statements) : Prop :=
  Block.WellTyped Expression.Typed (fun ty => ∃ τ, ty.toMonoType? = some τ ∧ τ.IsGround) Γ ss

end -- public section

end Core
