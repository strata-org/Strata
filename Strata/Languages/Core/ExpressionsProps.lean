/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.Factory
import all Strata.Languages.Core.Expressions
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.IntBoolFactory

/-! # Properties of Core expressions

The negation `HasBoolOps.not` of a Core expression reads no variable the expression does not
read (`Core.not_getFvars`), has no annotated free-variable occurrence the expression does not
have (`Core.not_getTypedFvars`), and refers only to the operators of the expression and the
built-in `Bool.Not` (`Core.not_getOps`); a comparison `a < b` of expressions reads, annotates and
refers only to theirs and the built-in `Int.Lt` (`Core.lt_getFvars`, `Core.lt_getTypedFvars`,
`Core.lt_getOps`). -/

namespace Core

public section

open Imperative

/-- The negation of an expression reads only the variables the expression reads. -/
theorem not_getFvars (g : Expression.Expr) :
    ∀ x ∈ HasFvars.getFvars (HasBoolOps.not g), x ∈ HasFvars.getFvars g := by
  intro x hx
  simp only [HasBoolOps.not] at hx
  split at hx
  · simp [HasFvars.getFvars, Lambda.LExpr.LExpr.getVars] at hx
  · simp [HasFvars.getFvars, Lambda.LExpr.LExpr.getVars] at hx
  · simpa [HasFvars.getFvars, Lambda.LExpr.LExpr.getVars, Lambda.WFLFunc.opExpr,
      Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr] using hx

/-- The negation of an expression has only the annotated free-variable occurrences of the
    expression. -/
theorem not_getTypedFvars (g : Expression.Expr) :
    ∀ p ∈ HasFvars.getTypedFvars (HasBoolOps.not g), p ∈ HasFvars.getTypedFvars g := by
  intro p hp
  simp only [HasBoolOps.not] at hp
  split at hp
  · simp [HasFvars.getTypedFvars, Expression.typedFvars, Lambda.LExpr.freeVars] at hp
  · simp [HasFvars.getTypedFvars, Expression.typedFvars, Lambda.LExpr.freeVars] at hp
  · simpa [HasFvars.getTypedFvars, Expression.typedFvars, Lambda.LExpr.freeVars,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr] using hp

/-- The negation of an expression refers only to the operators of the expression and to the
    built-in `Bool.Not`. -/
theorem not_getOps (g : Expression.Expr) :
    ∀ o ∈ HasOps.getOps (HasBoolOps.not g), o ∈ HasOps.getOps g ∨ o = ⟨"Bool.Not", ()⟩ := by
  intro o ho
  simp only [HasBoolOps.not] at ho
  split at ho
  · simp [HasOps.getOps, Lambda.LExpr.getOps] at ho
  · simp [HasOps.getOps, Lambda.LExpr.getOps] at ho
  · simp only [HasOps.getOps, Lambda.LExpr.getOps, List.mem_append] at ho
    rcases ho with ho | ho
    · right
      simpa [Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
        Lambda.LExpr.getOps, Lambda.boolNotFunc, Lambda.unaryOp] using ho
    · exact .inl ho

/-- The comparison `a < b` of expressions reads only the variables they read. -/
theorem lt_getFvars (a b : Expression.Expr) :
    ∀ x ∈ HasFvars.getFvars (HasIntOps.lt a b),
      x ∈ HasFvars.getFvars a ∨ x ∈ HasFvars.getFvars b := by
  intro x hx
  simpa [HasIntOps.lt, HasFvars.getFvars, Lambda.LExpr.LExpr.getVars, Lambda.WFLFunc.opExpr,
    Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr] using hx

/-- The comparison `a < b` of expressions has only their annotated free-variable
    occurrences. -/
theorem lt_getTypedFvars (a b : Expression.Expr) :
    ∀ p ∈ HasFvars.getTypedFvars (HasIntOps.lt a b),
      p ∈ HasFvars.getTypedFvars a ∨ p ∈ HasFvars.getTypedFvars b := by
  intro p hp
  simpa [HasIntOps.lt, HasFvars.getTypedFvars, Expression.typedFvars, Lambda.LExpr.freeVars,
    Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr] using hp

/-- The comparison `a < b` of expressions refers only to their operators and to the built-in
    `Int.Lt`. -/
theorem lt_getOps (a b : Expression.Expr) :
    ∀ o ∈ HasOps.getOps (HasIntOps.lt a b),
      o ∈ HasOps.getOps a ∨ o ∈ HasOps.getOps b ∨ o = ⟨"Int.Lt", ()⟩ := by
  intro o ho
  simp only [HasIntOps.lt, HasOps.getOps, Lambda.LExpr.getOps, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · right; right
    simpa [Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.LExpr.getOps, Lambda.intLtFunc, Lambda.binaryOp] using ho
  · exact .inl ho
  · exact .inr (.inl ho)

end -- public section

end Core
