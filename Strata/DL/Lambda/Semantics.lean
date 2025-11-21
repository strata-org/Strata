/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LState

---------------------------------------------------------------------

namespace Lambda

variable {T : LExprParamsT} [DecidableEq T.base.Metadata]
    [DecidableEq T.base.Identifier] [DecidableEq T.base.IDMeta]
    [Traceable LExpr.EvalProvenance T.base.Metadata]

open Lambda

/--
A free variable -> expression mapping.
-/
abbrev Env (T:LExprParamsT) := T.base.Identifier → Option (LExpr T)

def Scopes.toFreeVarMap (s:Scopes T.base) : Env T.base.mono :=
  fun t => (s.find? t).map (·.snd)

/--
A small-step semantics of LExpr.
Currently only defined for LMonoTy, but it will be expanded to an arbitrary
type in the future.
The order of constructors matter because the `constructor` tactic will rely on
it.
This small-step definitions faithfully follows the behavior of LExpr.eval,
except that
(1) This inductive definition may stuck early when there is no
assignment to a free variable available.
(2) This semantics does not describe how the metadata must change, because
metadata must not affect evaluation semantics. Different concrete evaluators
like LExpr.eval can use different strategy for updating metadata.
-/
inductive Step (F:@Factory T.base.mono.base) (rf:Env T.base.mono)
  : LExpr T.base.mono → LExpr T.base.mono → Prop where
-- A free variable. Stuck if fvar does not exist in FreeVarMap.
| expand_fvar:
  ∀ (x:T.base.mono.base.Identifier) (e:LExpr T.base.mono),
    rf x = .some e →
    Step F rf (.fvar _ x ty) e

-- Beta reduction for lambda; Call-by-value semantics.
| beta:
  ∀ (e1 v2 eres:LExpr T.base.mono),
    LExpr.isCanonicalValue F v2 →
    eres = LExpr.subst (fun _ => v2) e1 →
    Step F rf (.app m1 (.abs m2 ty e1) v2) eres

-- Call-by-value semantics.
| reduce_2:
  ∀ (v1 e2 e2':LExpr T.base.mono),
    LExpr.isCanonicalValue F v1 →
    Step F rf e2 e2' →
    Step F rf (.app m v1 e2) (.app m' v1 e2')

| reduce_1:
  ∀ (e1 e1' e2:LExpr T.base.mono),
    Step F rf e1 e1' →
    Step F rf (.app m e1 e2) (.app m' e1' e2)

-- For ite x e1 e2, do not eagerly evaluate e1 and e2.
-- For the reduction order, ite x e1 e2 is interpreted as
-- 'ite x (λ.e1) (λ.e2)'.
| ite_reduce_then:
  ∀ (ethen eelse:LExpr T.base.mono),
    Step F rf (.ite m (.const mc (.boolConst true)) ethen eelse) ethen

| ite_reduce_else:
  ∀ (ethen eelse:LExpr T.base.mono),
    Step F rf (.ite m (.const mc (.boolConst false)) ethen eelse) eelse

| ite_reduce_cond:
  ∀ (econd econd' ethen eelse:LExpr T.base.mono),
    Step F rf econd econd' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd' ethen eelse)

-- Equality. Reduce after both operands evaluate to values.
| eq_reduce:
  ∀ (e1 e2 eres:LExpr T.base.mono)
    (H1:LExpr.isCanonicalValue F e1)
    (H2:LExpr.isCanonicalValue F e2),
    eres = .const mc (.boolConst (LExpr.eql F e1 e2 H1 H2)) →
    Step F rf (.eq m e1 e2) eres

| eq_reduce_lhs:
  ∀ (e1 e1' e2:LExpr T.base.mono),
    Step F rf e1 e1' →
    Step F rf (.eq m e1 e2) (.eq m' e1' e2)

| eq_reduce_rhs:
  ∀ (v1 e2 e2':LExpr T.base.mono),
    LExpr.isCanonicalValue F v1 →
    Step F rf e2 e2' →
    Step F rf (.eq m v1 e2) (.eq m' v1 e2')

-- Expand functions and free variables when they are evaluated.
-- If the function body is unknown, concreteEval can be instead used. Look at
-- the eval_fn constructor below.
-- This is consistent with what LExpr.eval does (modulo the "inline" flag).
| expand_fn:
  ∀ (e callee fnbody new_body:LExpr T.base.mono) args fn,
    F.callOfLFunc e = .some (callee,args,fn) →
    args.all (LExpr.isCanonicalValue F) →
    fn.body = .some fnbody →
    new_body = LExpr.substFvars fnbody (fn.inputs.keys.zip args) →
    Step F rf e new_body

-- The second way of evaluating a function call.
-- If LFunc has a concrete evaluator, this can be used to 'jump' to the final
-- result of the function.
| eval_fn:
  ∀ (e callee:LExpr T.base.mono) args fn denotefn,
    F.callOfLFunc e = .some (callee,args,fn) →
    args.all (LExpr.isCanonicalValue F) →
    fn.concreteEval = .some denotefn →
    Step F rf e (denotefn (LExpr.mkApp m callee args) args)


omit [DecidableEq T.base.Metadata] [DecidableEq T.base.Identifier]
     [Traceable LExpr.EvalProvenance T.base.Metadata] in
theorem step_const_stuck:
  ∀ (F:@Factory T.base) r x e,
  ¬ Step F r (.const m x) e := by
  intros
  intro H
  contradiction

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
inductive StepStar (F:@Factory T.base) (rf:Env T.base.mono)
  : LExpr T.base.mono → LExpr T.base.mono → Prop where
| refl : StepStar F rf e e
| step : ∀ e e' e'', Step F rf e e' → StepStar F rf e' e''
        → StepStar F rf e e''

end Lambda
