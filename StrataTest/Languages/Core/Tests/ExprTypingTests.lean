/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.InstExprTyping
import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Lambda.Denote.LExprAnnotated

/-! # Tests for Core's expression typing

A well-typed comparison `x == 1`, with `x : int`, evaluates to a Boolean in
every store conforming to the typing.
-/

namespace Core.ExprTypingTests

open Imperative

/-- The variable `x`. -/
abbrev x : CoreIdent := ⟨"x", ()⟩

/-- `x` has type `int`; no other variable is typed. -/
abbrev Γ : VarTyping Expression := fun y => if y = x then some (.forAll [] .int) else none

/-- The condition `x == 1`. -/
abbrev cond : Expression.Expr := .eq () (.fvar () x none) (.intConst () 1)

/-- Annotating `cond` by `Γ` marks `x` as an integer. -/
theorem cond_annotated :
    cond.annotateFvars (fun y => (Γ y).bind Lambda.LTy.toMonoType?) =
      .eq () (.fvar () x (some .int)) (.intConst () 1) := by
  simp [Γ, Lambda.LExpr.annotateFvars, Lambda.LTy.toMonoType?]
  rfl

/-- Under `Γ`, the condition `x == 1` has the Boolean type. -/
theorem cond_hasType : HasTyping.HasType (P := Expression) f Γ cond HasBool.boolTy := by
  refine ⟨.bool, boolTy_toMonoType, rfl, ?_, ?_⟩
  · intro y hy
    simp only [Lambda.LExpr.LExpr.getVars] at hy
    obtain rfl : y = x := by simpa using hy
    simp [Γ]
  · rw [cond_annotated]
    exact Lambda.LExpr.typeCheck_to_HasTypeA (by rfl)

/-- In any store binding `x` to an integer of the model, `x == 1` evaluates to
    `true` or `false`. -/
example (f : Expression.Factory) (σ : CoreStore) (i : Int)
    (hx : σ x = some (Lambda.SemValue.ofInt f.model.tcInterp i)) :
    Expression.eval f σ cond = some (HasBool.ttVal f) ∨
      Expression.eval f σ cond = some (HasBool.ffVal f) := by
  refine eval_bool_of_hasType cond_hasType ?_
  intro y ty hy
  by_cases hyx : y = x
  · subst hyx
    simp only [Γ, ↓reduceIte, Option.some.injEq] at hy
    subst hy
    exact ⟨_, hx, rfl, rfl⟩
  · simp [Γ, hyx] at hy

end Core.ExprTypingTests
