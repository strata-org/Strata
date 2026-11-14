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
`Core.lt_getOps`).  `EqModuloMeta.beq` on Core expressions, on `Option`s of them and on
products is `true` exactly when the metadata-erased operands are equal — it ignores metadata,
not values (`eqModuloMeta_beq_iff`, `eqModuloMeta_beq_option_iff`, `eqModuloMeta_beq_prod_iff`). -/

namespace Core

public section

open Imperative

/-- The negation of an expression reads only the variables the expression reads. -/
theorem not_getFvars (g : Expression.Expr) :
    ∀ x ∈ HasFvars.getFvars (HasBoolOps.not g), x ∈ HasFvars.getFvars g := by
  intro x hx
  simp only [HasBoolOps.not] at hx
  split at hx
  -- The located `not` folds both bool-literal arms into one, so `split` yields two cases.
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

/-- `EqModuloMeta.beq` on Core expressions is `true` exactly when the metadata-erased
expressions are equal: it ignores metadata, not values. -/
theorem eqModuloMeta_beq_iff (a b : Lambda.LExpr CoreLParams.mono) :
    Lambda.LExpr.EqModuloMeta.beq a b = true ↔ a.eraseMetadata = b.eraseMetadata :=
  Lambda.LExpr.beq_eq a.eraseMetadata b.eraseMetadata

/-- `EqModuloMeta.beq` on `Option` of Core expressions ignores metadata, not values. -/
theorem eqModuloMeta_beq_option_iff (a b : Option (Lambda.LExpr CoreLParams.mono)) :
    Lambda.LExpr.EqModuloMeta.beq a b = true ↔
      a.map Lambda.LExpr.eraseMetadata = b.map Lambda.LExpr.eraseMetadata := by
  cases a with
  | none => cases b <;> simp [Lambda.LExpr.EqModuloMeta.beq]
  | some x => cases b with
    | none => simp [Lambda.LExpr.EqModuloMeta.beq]
    | some y =>
      simp only [Option.map_some, Option.some.injEq]
      exact eqModuloMeta_beq_iff x y

/-- `EqModuloMeta.beq` on a product is the conjunction of the component comparisons, so by the
component iffs it too ignores metadata, not values. -/
theorem eqModuloMeta_beq_prod_iff {α β : Type _}
    [Lambda.LExpr.EqModuloMeta α] [Lambda.LExpr.EqModuloMeta β] (p q : α × β) :
    Lambda.LExpr.EqModuloMeta.beq p q = true ↔
      Lambda.LExpr.EqModuloMeta.beq p.1 q.1 = true ∧ Lambda.LExpr.EqModuloMeta.beq p.2 q.2 = true := by
  simp only [Lambda.LExpr.EqModuloMeta.beq, Bool.and_eq_true]

end -- public section

end Core
