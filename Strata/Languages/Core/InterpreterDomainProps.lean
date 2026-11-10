/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.LExprEvalFuelProps
import all Strata.DL.Lambda.LExprDenoteEval

/-! # The evaluation domain of Core's bounded evaluator

Core's bounded evaluator `evalBounded` evaluates only expressions in the domain of the reference
evaluator `Lambda.LExpr.denoteEval`, checked on the runtime store by `evalTypedDomain`. This
module relates the check to that domain.

Key theorems:
* `denotes_iff`: a runtime value denotes a semantic value exactly when it passes `isValue`,
  type checks against the factory (`typeCheckWith`), and `denoteEval` evaluates it to that value;
* `denotes_literal`: a literal denotes its value;
* `denotes_boolConst`: when no constructor of the factory produces a Boolean, a runtime value
  denoting a Boolean is a Boolean literal;
* `denotes_typeCheck`: a runtime value type checks to the type of the sort it denotes;
* `runtimeAnn_eq_ann`: on a runtime store denoting `σ`, the annotation the runtime store gives
  a variable is the one `σ` gives it;
* `evalTypedDomain_congr`, `evalTypedDomain_frame`: the check depends only on the bindings of
  the free variables, and survives store extension;
* `evalTypedDomain_iff`: on a runtime store denoting `σ`, an expression passes `evalTypedDomain`
  exactly when `denoteEval` evaluates it on `σ`;
* `denote_of_isValue_typeCheckWith`: a value that type checks at a ground type denotes a value
  of that type;
* `evalBounded_eq_some_iff`: `evalBounded` returns `v` exactly when the expression passes
  `evalTypedDomain` and `evalOpsChecked`, `Lambda.LExpr.eval` reduces it to the value `v`, and
  `v` type checks against the factory. -/

namespace Core
open Imperative Lambda

public section

/-- Annotating no free variable leaves an expression unchanged. -/
private theorem annotateFvars_none' (e : Expression.Expr) :
    e.annotateFvars (fun _ => none) = e := by
  induction e <;> simp_all only [LExpr.annotateFvars]

/-- A runtime value `r` denotes `v` (`InterpLang.Denotes`) exactly when `r` passes `isValue`,
    type checks against the factory (`typeCheckWith`), and evaluates to `v` (`denoteEval`) on
    the empty store. -/
theorem denotes_iff {F : Expression.Factory} {r : Expression.Expr} {v : Expression.Val} :
    InterpLang.Denotes F r v ↔
      LExpr.isValue F.factory r = true ∧ (r.typeCheckWith F.factory []).isSome = true ∧
        r.denoteEval F (fun _ => none) = some v := by
  change (if LExpr.isValue F.factory r && (r.typeCheckWith F.factory []).isSome then _
    else none) = _ ↔ _
  split <;> simp_all only [Bool.and_eq_true, true_and, not_and, Bool.not_eq_true,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, reduceCtorEq, false_iff,
      Option.isSome_none, Bool.false_eq_true, false_and, not_false_eq_true, implies_true]

/-- A literal type checks against every factory (`typeCheckWith`). -/
theorem typeCheckWith_const (F : Lambda.Factory CoreLParams) (m : ExpressionMetadata)
    (c : LConst) : ((LExpr.const m c : Expression.Expr).typeCheckWith F []).isSome = true :=
  rfl

/-- A literal denotes the value `denoteEval` gives it on the empty store. -/
theorem denotes_literal {F : Expression.Factory} {m : ExpressionMetadata} {c : LConst}
    {v : Expression.Val} (h : (LExpr.const m c : Expression.Expr).denoteEval F (fun _ => none) =
      some v) : InterpLang.Denotes F (.const m c) v :=
  denotes_iff.2 ⟨isValue_const_true .., typeCheckWith_const .., h⟩

/-- A runtime value that denotes `v` (`InterpLang.Denotes`) type checks, with no bound type
    variables, to the type of `v`'s sort. -/
theorem denotes_typeCheck {F : Expression.Factory} {r : Expression.Expr} {v : Expression.Val}
    (h : InterpLang.Denotes F r v) : r.typeCheck [] = some v.sort.toMonoTy := by
  obtain ⟨-, τ, hτ, hg, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp
    (denotes_iff.1 h).2.2
  have hT : r.typeCheck [] = some τ :=
    annotateFvars_none' r ▸ LExpr.HasTypeA_to_typeCheck hτ
  rw [hT]
  exact congrArg some (by
    change τ = (τ.substTyVars F.tyVarVal).toMonoTy
    rw [hg.substTyVars_eq F.tyVarVal refTyVarVal, hg])

/-- On a runtime store `σr` denoting `σ`, the annotation `σr` gives each variable (the type its
    runtime value type checks to) is the one `σ` gives it (the type of its value's sort). -/
theorem runtimeAnn_eq_ann {F : Expression.Factory} {σr : RStore Expression}
    {σ : SemanticStore Expression} (hS : StoreDenotes F σr σ) :
    runtimeAnn σr = ValStore.ann (T := CoreLParams) σ := by
  funext x
  cases hx : σ x with
  | none => simp [runtimeAnn, ValStore.ann, hx, (hS.1 x).1 hx]
  | some v =>
    obtain ⟨r, hr⟩ : ∃ r, σr x = some r :=
      Option.ne_none_iff_exists'.1 fun h => by simp [(hS.1 x).2 h] at hx
    simp [runtimeAnn, ValStore.ann, hx, hr, denotes_typeCheck (hS.2 x r v hr hx)]

/-- `isGroundTy` decides `Lambda.LMonoTy.IsGround`. -/
theorem isGroundTy_iff {τ : LMonoTy} : isGroundTy τ = true ↔ τ.IsGround := by
  simp [isGroundTy, LMonoTy.IsGround]

/-- A literal is in the evaluation domain on every runtime store. -/
theorem evalTypedDomain_const (σr : RStore Expression) (m : Unit) (c : LConst) :
    evalTypedDomain σr (.const m c) = true := by
  unfold evalTypedDomain
  exact isGroundTy_iff.2 (by cases c <;> rfl)

/-- A variable bound in the runtime store to a value that type checks at a ground type is in
    the evaluation domain. -/
theorem evalTypedDomain_fvar {σr : RStore Expression} {m : Unit} {x : CoreIdent}
    {ty : Option LMonoTy} {r : Expression.Expr} (hx : σr x = some r)
    (hr : (r.typeCheck []).any isGroundTy = true) : evalTypedDomain σr (.fvar m x ty) = true := by
  obtain ⟨τ, hτ, hg⟩ := (Option.any_eq_true _ _).1 hr
  simp [evalTypedDomain, LExpr.LExpr.getVars, LExpr.annotateFvars, runtimeAnn, hx, hτ, hg,
    LExpr.typeCheck]

/-- Whether an expression is in the evaluation domain depends only on the runtime store's
    bindings of its free variables. -/
theorem evalTypedDomain_congr {σr σr' : RStore Expression} {e : Expression.Expr}
    (h : ∀ x ∈ LExpr.LExpr.getVars e, σr x = σr' x) :
    evalTypedDomain σr e = evalTypedDomain σr' e := by
  have hann : e.annotateFvars (runtimeAnn σr) = e.annotateFvars (runtimeAnn σr') :=
    LExpr.annotateFvars_congr e fun x _ hx => by
      simp only [runtimeAnn, h x (LExpr.mem_getVars_of_mem_freeVars hx)]
  have hall : (LExpr.LExpr.getVars e).all (fun x => (σr x).isSome) =
      (LExpr.LExpr.getVars e).all (fun x => (σr' x).isSome) :=
    Bool.eq_iff_iff.2 (by
      simp only [List.all_eq_true]
      exact forall₂_congr fun x hx => by rw [h x hx])
  simp only [evalTypedDomain, hann, hall]

/-- An expression in the evaluation domain of a runtime store stays in it on every store that
    extends it. -/
theorem evalTypedDomain_frame {σr σr' : RStore Expression} {e : Expression.Expr}
    (hext : ∀ x w, σr x = some w → σr' x = some w) (h : evalTypedDomain σr e = true) :
    evalTypedDomain σr' e = true := by
  have hb : ∀ x ∈ LExpr.LExpr.getVars e, (σr x).isSome = true := by
    simp only [evalTypedDomain, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1
  rwa [← evalTypedDomain_congr fun x hx => ?_]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hb x hx)
  rw [hw, hext x w hw]

/-- Whether an expression passes `evalOpsChecked` depends only on the runtime store's bindings of
    its free variables. -/
theorem evalOpsChecked_congr {F : Lambda.Factory CoreLParams} {σr σr' : RStore Expression}
    {e : Expression.Expr} (h : ∀ x ∈ LExpr.LExpr.getVars e, σr x = σr' x) :
    evalOpsChecked F σr e = evalOpsChecked F σr' e := by
  have hall : (LExpr.LExpr.getVars e).all (fun x => (σr x).all (opsInstantiated F)) =
      (LExpr.LExpr.getVars e).all (fun x => (σr' x).all (opsInstantiated F)) :=
    Bool.eq_iff_iff.2 (by
      simp only [List.all_eq_true]
      exact forall₂_congr fun x hx => by rw [h x hx])
  simp only [evalOpsChecked, hall]

/-- A variable passes `evalOpsChecked` when its runtime value passes `opsInstantiated`. -/
theorem evalOpsChecked_fvar {F : Lambda.Factory CoreLParams} {σr : RStore Expression}
    {m : ExpressionMetadata} {x : CoreIdent} {ty : Option LMonoTy} {r : Expression.Expr}
    (hx : σr x = some r) (hr : opsInstantiated F r = true) :
    evalOpsChecked F σr (.fvar m x ty) = true := by
  simp [evalOpsChecked, opsInstantiated, LExpr.LExpr.getVars, hx, hr]

/-- An expression in the evaluation domain of a runtime store that passes `evalOpsChecked` on it
    passes it on every store that extends it. -/
theorem evalOpsChecked_frame {F : Lambda.Factory CoreLParams} {σr σr' : RStore Expression}
    {e : Expression.Expr} (hext : ∀ x w, σr x = some w → σr' x = some w)
    (hd : evalTypedDomain σr e = true) (h : evalOpsChecked F σr e = true) :
    evalOpsChecked F σr' e = true := by
  have hb : ∀ x ∈ LExpr.LExpr.getVars e, (σr x).isSome = true := by
    simp only [evalTypedDomain, Bool.and_eq_true, List.all_eq_true] at hd
    exact hd.1
  rwa [← evalOpsChecked_congr fun x hx => ?_]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hb x hx)
  rw [hw, hext x w hw]

/-- **The evaluation domain.** On a runtime store `σr` denoting the semantic store `σ` under `F`,
    `e` passes `evalTypedDomain` exactly when the reference evaluator `denoteEval` gives `e` a
    value on `σ`. -/
theorem evalTypedDomain_iff {F : Expression.Factory} {σr : RStore Expression}
    {σ : SemanticStore Expression} (hS : StoreDenotes F σr σ) (e : Expression.Expr) :
    evalTypedDomain σr e = true ↔ ∃ v, e.denoteEval F σ = some v := by
  have hdef : (LExpr.LExpr.getVars e).all (fun x => (σr x).isSome) = true ↔
      ValStore.Defines (T := CoreLParams) σ F.model.tcInterp e := by
    simp only [List.all_eq_true, Option.isSome_iff_ne_none, ValStore.Defines]
    refine forall₂_congr fun x _ => ⟨fun h => ?_, fun ⟨v, hv, _⟩ h => by simp [(hS.1 x).2 h] at hv⟩
    obtain ⟨v, hv⟩ : ∃ v, σ x = some v := Option.ne_none_iff_exists'.1 fun h' => h ((hS.1 x).1 h')
    obtain ⟨r, hr⟩ : ∃ r, σr x = some r := Option.ne_none_iff_exists'.1 h
    exact ⟨v, hv, LExpr.denoteEval_tc (denotes_iff.1 (hS.2 x r v hr hv)).2.2⟩
  simp only [evalTypedDomain, Bool.and_eq_true, hdef, runtimeAnn_eq_ann hS, Option.any_eq_true,
    isGroundTy_iff]
  constructor
  · rintro ⟨hd, τ, hτ, hg⟩
    exact ⟨_, LExpr.denoteEval_of_hasTypeA hd (LExpr.typeCheck_to_HasTypeA hτ) hg⟩
  · rintro ⟨v, hv⟩
    obtain ⟨hd, τ, hτ, hg, -⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp hv
    exact ⟨hd, τ, LExpr.HasTypeA_to_typeCheck hτ, hg⟩

/-- A value that passes Core's `isValue` and type checks (`typeCheckWith`) to a ground type `τ`
    denotes a value of the factory's interpretation whose sort has type `τ`. -/
theorem denote_of_isValue_typeCheckWith {F : Expression.Factory} {r : Expression.Expr}
    {τ : LMonoTy} (hv : LExpr.isValue F.factory r = true)
    (ht : r.typeCheckWith F.factory [] = some τ) (hg : τ.IsGround) :
    ∃ v, InterpLang.Denotes F r v ∧ v.tc = F.model.tcInterp ∧ v.sort.toMonoTy = τ := by
  have ht' : r.typeCheck [] = some τ := by
    unfold LExpr.typeCheckWith at ht
    split at ht <;> simp_all only [Bool.not_eq_true, reduceCtorEq]
  obtain ⟨sv, htc, hs, hall⟩ :=
    LExpr.denoteEval_of_isValue (M := F) hv (LExpr.typeCheck_to_HasTypeA ht') hg
  exact ⟨sv, denotes_iff.2 ⟨hv, by simp [ht], hall _⟩, htc, hs⟩

/-- When no constructor of the factory produces a Boolean (`ConstrsNotBool`), a runtime value
    that denotes a value of sort `bool` is a Boolean literal. -/
theorem denotes_boolConst {F : Expression.Factory} {r : Expression.Expr} {v : Expression.Val}
    (hF : F.factory.ConstrsNotBool) (h : InterpLang.Denotes F r v)
    (hs : v.sort.toMonoTy = .bool) : ∃ m b, r = .boolConst m b := by
  obtain ⟨hv, hw, -⟩ := denotes_iff.1 h
  have ht := denotes_typeCheck h
  refine LExpr.isValue_bool_eq_boolConst hF hv ?_
  unfold LExpr.typeCheckWith at hw ⊢
  split at hw <;> simp_all only [Option.isSome_some, ↓reduceIte, Bool.not_eq_true,
      Option.isSome_none, Bool.false_eq_true]

/-- `evalBounded` returns `v` exactly when `e` passes `evalTypedDomain`, `Lambda.LExpr.eval`
    reduces `e` at the fuel to the fully-decided value `v`, `v` type checks against the
    factory (`typeCheckWith`), and `e` passes `evalOpsChecked`. -/
theorem evalBounded_eq_some_iff {n : Nat} {F : Lambda.Factory CoreLParams}
    {σr : RStore Expression} {e v : Expression.Expr} :
    evalBounded n F σr e = some v ↔
      evalTypedDomain σr e = true ∧ LExpr.eval n F σr e = (v, .value true) ∧
        (v.typeCheckWith F []).isSome = true ∧ evalOpsChecked F σr e = true := by
  unfold evalBounded
  split
  · split
    · split <;> grind
    · simp_all only [Bool.and_eq_true, imp_false, reduceCtorEq, and_true, false_and, and_false]
  · simp_all only [Bool.and_eq_true, not_and, Bool.not_eq_true, reduceCtorEq, false_iff,
      Bool.false_eq_true, and_false, not_false_eq_true, implies_true]

end

end Core
