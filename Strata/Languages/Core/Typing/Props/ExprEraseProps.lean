/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.CmdType
public import Strata.Languages.Core.WrittenTyVarScope
public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.DL.Lambda.LExprTEraseProps
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.CmdType
import all Strata.Languages.Core.WrittenTyVarScope
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import all Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprTEraseProps
import Strata.Util.Tactics

/-! # Type erasure of checker-produced expressions

The type checker re-annotates every source expression it stores: resolution elaborates it,
and the stored form is read back from the elaborated one. Each step changes only type
annotations, so the stored expression and the source expression have the same erasure
(`LExpr.eraseTypes`). The free-variable check that makes resolution erasure-preserving is the
annotation linking of `SourceExpr.resolve`, which rejects a binder that captures a free
variable.

Key theorems: `SourceExpr.resolve_unresolved_eraseTypes`,
`SourceExpr.resolveWithType_unresolved_eraseTypes` and `eraseTypes_finishDeskolemized`.
-/

namespace Core

open Lambda

public section

namespace SourceExpr

/-- Resolving a source expression only adds type annotations: the elaborated expression, with
    its annotations erased, is the erased source. The generated variable that resolution opens a
    binder with could capture a free variable of the source that has the same name; annotation
    linking rejects that, because the capturing binder changes the shape of the expression. -/
theorem resolve_unresolved_eraseTypes (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (e : Core.Expression.Expr)
    (typed : LExprT CoreLParams.mono) (Env' : Core.Expression.TyEnv)
    (h : resolve C Env e = .ok (typed, Env')) :
    (LExpr.unresolved typed).eraseTypes = e.eraseTypes := by
  simp only [resolve, bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · elim_err h with r hr
    obtain ⟨typedR, EnvR⟩ := r
    elim_err h with r2 hlink
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_typed, _⟩ := h
    subst h_typed
    have hsc : ∀ id ∈ LExpr.LExpr.getVars e, id ∈ TContext.knownVars Env.context := by
      intro id hid
      exact LExpr.Proofs.resolve_getVars_mem_knownVars C Env EnvR e typedR hr id
        (linkFVarAnnotations_getVars C e typedR EnvR r2 hlink id hid)
    exact LExpr.resolve_unresolved_eraseTypes C Env EnvR e typedR hr hsc

/-- Resolving source expressions from left to right only adds type annotations to each. -/
theorem resolves_unresolved_eraseTypes (C : Core.Expression.TyContext) :
    ∀ (es : List Core.Expression.Expr) (Env : Core.Expression.TyEnv)
      (ts : List (LExprT CoreLParams.mono)) (Env' : Core.Expression.TyEnv),
      resolves C Env es = .ok (ts, Env') →
      ts.map (fun t => (LExpr.unresolved t).eraseTypes) = es.map LExpr.eraseTypes := by
  intro es
  induction es with
  | nil =>
    intro Env ts Env' h
    simp only [resolves, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ts, _⟩ := h
    subst h_ts
    rfl
  | cons e rest ih =>
    intro Env ts Env' h
    simp only [resolves, bind, Except.bind] at h
    elim_err h with r1 h1
    obtain ⟨typed, Env1⟩ := r1
    elim_err h with r2 h2
    obtain ⟨typedRest, Env2⟩ := r2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ts, _⟩ := h
    subst h_ts
    simp only [List.map_cons, resolve_unresolved_eraseTypes C Env e typed Env1 h1,
      ih Env1 typedRest Env2 h2]

/-- Resolving a source expression against an expected type only adds type annotations. -/
theorem resolveWithType_unresolved_eraseTypes (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (e : Core.Expression.Expr) (expected : LMonoTy)
    (et : LExprT CoreLParams.mono) (Env' : Core.Expression.TyEnv)
    (h : resolveWithType C Env e expected = .ok (et, Env')) :
    (LExpr.unresolved et).eraseTypes = e.eraseTypes := by
  simp only [resolveWithType, bind, Except.bind] at h
  elim_err h with r1 h1
  obtain ⟨et1, Env1⟩ := r1
  elim_err h with S hS
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h_et, _⟩ := h
  subst h_et
  simp only [Except.mapError] at h1
  split at h1
  · simp at h1
  · rename_i r hr
    simp only [Except.ok.injEq] at h1
    subst h1
    exact resolve_unresolved_eraseTypes C Env e et1 Env1 hr

end SourceExpr

/-- Skolemizing the annotations of an expression leaves its erasure unchanged. -/
theorem eraseTypes_skolemizeBody (selfName : Option String) (σ : RigidNames)
    (e : Core.Expression.Expr) : (skolemizeBody selfName σ e).eraseTypes = e.eraseTypes := by
  simp only [skolemizeBody]
  exact LExpr.eraseTypes_replaceUserProvidedType _ e _

/-- Substituting and deskolemizing an elaborated expression, then erasing its annotations, is
    erasing the `unresolved` form of the elaborated expression. -/
theorem eraseTypes_finishDeskolemized (σ : RigidNames) (S : Subst)
    (et : LExprT CoreLParams.mono) :
    (finishDeskolemized σ S et).eraseTypes = (LExpr.unresolved et).eraseTypes := by
  simp only [finishDeskolemized]
  rw [LExpr.eraseTypes_replaceUserProvidedType, LExpr.eraseTypes_unresolved_applySubstT]

namespace WrittenTyVarScope

/-- Renaming the annotations of an expression into a scope leaves its erasure unchanged. -/
theorem eraseTypes_renameExpr (m : ScopeMap) (e : Core.Expression.Expr) :
    (renameExpr m e).eraseTypes = e.eraseTypes := by
  simp only [renameExpr]
  exact LExpr.eraseTypes_replaceUserProvidedType _ e _

end WrittenTyVarScope

end

end Core
