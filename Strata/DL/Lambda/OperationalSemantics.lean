/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.LExprWFProps

import all Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprProps
import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.LExprType
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.Scopes
public import Strata.Util.RelationsProps

/-!
# Operational semantics for Lambda expressions

This module defines the small-step relation `Step` and its reflexive-transitive
closure `StepStar`. Proofs about these relations live in
`OperationalSemanticsProps`; evaluator soundness lives in `LExprEvalSound`.
-/

namespace Lambda

open Std (ToFormat Format format)

public section

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]

open Lambda

/--
A small-step semantics for `LExpr`.

Currently only defined for expressions paremeterized by `LMonoTy`, but it will
be expanded to an arbitrary type in the future.

The order of constructors matter because the `constructor` tactic will rely on
it.

This small-step definitions faithfully follows the behavior of `LExpr.eval`,
except that:
1. This inductive definition may get stuck early when there is no
   assignment to a free variable available.

2. This semantics does not describe how metadata must change, because
   metadata must not affect evaluation semantics. Different concrete evaluators
   like `LExpr.eval` can have different strategy for updating metadata.
-/
inductive Step (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop where
/-- A free variable. Stuck if `rf` does not assign an expression to `x`. -/
| expand_fvar:
  ∀ (x:Tbase.Identifier) (e:LExpr Tbase.mono),
    rf x = .some e →
    Step F rf (.fvar m x ty) e

/-- Beta reduction. The argument `e2` need not be a value;
this relaxation (compared to strict call-by-value) is necessary because `LExpr.eval`
evaluates both sub-expressions before performing substitution and we want the
semantics to be flexible enough to handle partial evaluation. -/
| beta:
  ∀ (e1 e2 eres:LExpr Tbase.mono),
    eres = LExpr.subst (fun _ => e2) e1 →
    Step F rf (.app m1 (.abs m2 name ty e1) e2) eres

/-- Argument evaluation: reduce the argument of an application.
Note: this rule does NOT require the function part to be a value.
Unlike the call-by-value strategy, this allows stepping any
argument of an application, which is needed for factory calls where `LExpr.eval`
evaluates all arguments independently (not left-to-right) with possibly limited
fuels. -/
| reduce_2:
  ∀ (e1 e2 e2':LExpr Tbase.mono),
    Step F rf e2 e2' →
    Step F rf (.app m e1 e2) (.app m' e1 e2')

/-- Function application. -/
| reduce_1:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.app m e1 e2) (.app m' e1' e2)

/-- Evaluation of `ite`: condition is true, select "then" branch. -/
| ite_reduce_then:
  ∀ (ethen eelse:LExpr Tbase.mono),
    Step F rf (.ite m (.const mc (.boolConst true)) ethen eelse) ethen

/-- Evaluation of `ite`: condition is false, select "else" branch. -/
| ite_reduce_else:
  ∀ (ethen eelse:LExpr Tbase.mono),
    Step F rf (.ite m (.const mc (.boolConst false)) ethen eelse) eelse

/-- Evaluation of `ite` condition. -/
| ite_reduce_cond:
  ∀ (econd econd' ethen eelse:LExpr Tbase.mono),
    Step F rf econd econd' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd' ethen eelse)

/-- Evaluation of `ite` "then" branch (when condition is not yet resolved). -/
| ite_reduce_then_branch:
  ∀ (econd ethen ethen' eelse:LExpr Tbase.mono),
    Step F rf ethen ethen' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd ethen' eelse)

/-- Evaluation of `ite` "else" branch (when condition is not yet resolved). -/
| ite_reduce_else_branch:
  ∀ (econd ethen eelse eelse':LExpr Tbase.mono),
    Step F rf eelse eelse' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd ethen eelse')

/-- Evaluation of equality to true. Always allowed. -/
| eq_reduce_true:
  ∀ (e1 e2:LExpr Tbase.mono),
    LExpr.eql F e1 e2 = some true →
    Step F rf (.eq m e1 e2) (.const mc (.boolConst true))

/-- Evaluation of equality to false. Only when neither side contains a binder,
    because syntactic inequality under binders does not imply semantic inequality
    (e.g., `λx. x+1` vs `λx. 1+x`). -/
| eq_reduce_false:
  ∀ (e1 e2:LExpr Tbase.mono),
    LExpr.eql F e1 e2 = some false →
    Step F rf (.eq m e1 e2) (.const mc (.boolConst false))

/-- Evaluation of the left-hand side of an equality. -/
| eq_reduce_lhs:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.eq m e1 e2) (.eq m' e1' e2)

/-- Evaluation of the right-hand side of an equality.
Note: this rule does NOT require the LHS to be a value. -/
| eq_reduce_rhs:
  ∀ (e1 e2 e2':LExpr Tbase.mono),
    Step F rf e2 e2' →
    Step F rf (.eq m e1 e2) (.eq m' e1 e2')

/-- Evaluate a built-in function when a body expression is available in the
`Factory` argument `F`. This is consistent with what `LExpr.eval` does (modulo
the `inline` flag). Note that it might also be possible to evaluate with
`eval_fn`. A key correctness property is that doing so will yield the same
result. Note that this rule does not enforce an evaluation order. -/
| expand_fn:
  ∀ (e callee fnbody new_body:LExpr Tbase.mono) args fn tySubst,
    F.callOfLFunc e = .some (callee,args,fn) →
    fn.body = .some fnbody →
    LFunc.computeTypeSubst fn callee args = .some tySubst →
    new_body = LExpr.substFvarsLifting (fnbody.applyTypeSubst tySubst) (fn.inputs.keys.zip args) →
    Step F rf e new_body

/-- Evaluate a built-in function when a concrete evaluation function is
available in the `Factory` argument `F`.  Note that it might also be possible to
evaluate with `expand_fn`. A key correctness property is that doing so will
yield the same result. Note that this rule does not enforce an evaluation
order. -/
| eval_fn:
  ∀ (e callee e':LExpr Tbase.mono) args fn denotefn,
    F.callOfLFunc e = .some (callee,args,fn) →
    fn.concreteEval = .some denotefn →
    .some e' = denotefn m args →
    Step F rf e e'

/-- Substitute free variables under an abstraction binder using the full state.
This is analogous to the closure rule in lambda calculi with explicit
substitutions: it substitutes all occurrences of a free variable in the body of
an abstraction, even though the substitution is not represented as an explicit
syntactic term.

The `x ∈ freeVars body` witness ensures the step only fires when the body
actually has free variables. This preserves `value_not_step`:
`isValue` returns `true` for an abs only when it is *closed*
(`freeVars e = []`), so an abstraction that is a value has no free variables for this rule
to fire on.
-/
| abs_subst_fvars:
  ∀ (body : LExpr Tbase.mono) (x : Tbase.Identifier),
    x ∈ (LExpr.freeVars body).map Prod.fst →
    Step F rf (.abs m name ty body) (.abs m' name ty (LExpr.substFvarsFromEnv rf body))

/-- Substitute free variables under a quantifier binder (body). Same motivation
as `abs_subst_fvars`. -/
| quant_subst_fvars_body:
  ∀ (tr body : LExpr Tbase.mono) (x : Tbase.Identifier),
    x ∈ (LExpr.freeVars body).map Prod.fst →
    Step F rf (.quant m qk name ty tr body) (.quant m' qk name ty tr (LExpr.substFvarsFromEnv rf body))

/-- Substitute free variables in the trigger of a quantifier. Same motivation
as `abs_subst_fvars`. -/
| quant_subst_fvars_trigger:
  ∀ (tr body : LExpr Tbase.mono) (x : Tbase.Identifier),
    x ∈ (LExpr.freeVars tr).map Prod.fst →
    Step F rf (.quant m qk name ty tr body) (.quant m' qk name ty (LExpr.substFvarsFromEnv rf tr) body)

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
@[expose] def StepStar (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop :=
  ReflTrans (Step F rf)


end -- public section
end Lambda
