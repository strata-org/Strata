/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.Util.ListUtils

/-! # Sound concrete evaluators

`LFunc.EvalSound fn`: the concrete evaluator of `fn` returns, on arguments typed at the
function's input types, a literal or one of its arguments, typed at the function's output
type. The evaluator also receives the operator's type annotation (`ConcreteEval`); typing is
required at the function's type instantiated by the call's type substitution. It bounds what a concrete evaluation can produce, so a proof can reason about
evaluation results without knowing the evaluator itself.
-/

namespace Lambda

public section

variable {T : LExprParams}

/-- The concrete evaluator of `fn`, if any, returns, on arguments typed at the function's
    input types under a type substitution and at the function's type instantiated by that
    substitution as the operator's annotation, a result typed at its output type under that
    substitution; and, at every annotation, that result is a literal or one of the
    arguments. -/
structure LFunc.EvalSound (fn : LFunc T) : Prop where
  wt : ∀ ceval, fn.concreteEval = some ceval →
    ∀ (md : T.Metadata) (args : List (LExpr T.mono)) (result : LExpr T.mono) (S : Subst),
      ceval md (some (LMonoTy.mkArrow' (LMonoTy.subst S fn.output)
        (fn.inputs.map Prod.snd |>.map (LMonoTy.subst S)))) args = some result →
      List.Rel₂ (LExpr.HasTypeA []) args (fn.inputs.map Prod.snd |>.map (LMonoTy.subst S)) →
      LExpr.HasTypeA [] result (LMonoTy.subst S fn.output)
  shape : ∀ ceval, fn.concreteEval = some ceval →
    ∀ (md : T.Metadata) (opTy : Option LMonoTy) (args : List (LExpr T.mono))
      (result : LExpr T.mono),
      ceval md opTy args = some result → (∃ m c, result = .const m c) ∨ result ∈ args

end -- public section

end Lambda
