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

variable {IDMeta:Type} [DecidableEq IDMeta]

open Lambda

/--
A small-step semantics of LExpr.
Currently only defined for LMonoTy, but it will be expanded to an arbitrary
type.
The order of constructors matter because the `constructor` tactic will rely on
it.
This small-step definitions faithfully follows the behavior of LExpr.eval,
except that this inductive definition may stuck early when there is no
assignment to a free variable available in LState.
-/
inductive Step (F:@Factory IDMeta) (state:Scopes IDMeta)
  : LExpr LMonoTy IDMeta → LExpr LMonoTy IDMeta → Prop where
-- A free variable. Stuck if fvar does not exist in LState.
| expand_fvar:
  ∀ (x:Identifier IDMeta) (e:LExpr LMonoTy IDMeta),
    state.find? x = .some (ty,e) →
    Step F state (.fvar x ty') e

-- Beta reduction for lambda; Call-by-value semantics.
| beta:
  ∀ (e1 v2:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue F v2 →
    Step F state (.app (.abs ty e1) v2) (LExpr.subst v2 e1)

-- Call-by-value semantics.
| reduce_2:
  ∀ (v1 e2 e2':LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue F v1 →
    Step F state e2 e2' →
    Step F state (.app v1 e2) (.app v1 e2')

| reduce_1:
  ∀ (e1 e1' e2:LExpr LMonoTy IDMeta),
    Step F state  e1 e1' →
    Step F state  (.app e1 e2) (.app e1' e2)

-- For ite x e1 e2, do not eagerly evaluate e1 and e2.
-- For the reduction order, ite x e1 e2 is interpreted as
-- 'ite x (λ.e1) (λ.e2)'.
| ite_beta_then:
  ∀ (ethen eelse:LExpr LMonoTy IDMeta),
    Step F state  (.ite (.const (.boolConst true)) ethen eelse) ethen

| ite_beta_else:
  ∀ (ethen eelse:LExpr LMonoTy IDMeta),
    Step F state  (.ite (.const (.boolConst false)) ethen eelse) eelse

| ite_reduce_cond:
  ∀ (econd econd' ethen eelse:LExpr LMonoTy IDMeta),
    Step F state  econd econd' →
    Step F state  (.ite econd ethen eelse) (.ite econd' ethen eelse)

-- Equality. Reduce after both operands evaluate to values.
| beta_eq:
  ∀ (e1 e2 eres:LExpr LMonoTy IDMeta)
    (H1:LExpr.isCanonicalValue F e1)
    (H2:LExpr.isCanonicalValue F e2),
    eres = .const (.boolConst (LExpr.eql F e1 e2 H1 H2)) →
    Step F state  (.eq e1 e2) eres

| reduce_eq_lhs:
  ∀ (e1 e1' e2:LExpr LMonoTy IDMeta),
    Step F state  e1 e1' →
    Step F state  (.eq e1 e2) (.eq e1' e2)

| reduce_eq_rhs:
  ∀ (v1 e2 e2':LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue F v1 →
    Step F state  e2 e2' →
    Step F state  (.eq v1 e2) (.eq v1 e2')

-- Evaluation keeps the metadata.
| mdata:
  ∀ (e e':LExpr LMonoTy IDMeta) (m:Info),
    Step F state  e e' →
    Step F state  (.mdata m e) (.mdata m e')

-- Expand functions and free variables when they are evaluated.
-- If the function body is unknown, concreteEval can be instead used. Look at
-- the eval_fn constructor below.
-- This is consistent with what LExpr.eval does (modulo the "inline" flag).
| expand_fn:
  ∀ (e callee fnbody new_body:LExpr LMonoTy IDMeta) args fn,
    F.callOfLFunc e = .some (callee,args,fn) →
    args.all (LExpr.isCanonicalValue F) →
    fn.body = .some fnbody →
    new_body = LExpr.substFvars fnbody (fn.inputs.keys.zip args) →
    Step F state  e new_body

-- The second way of evaluating a function call.
-- If LFunc has a concrete evaluator, this can be used to 'jump' to the final
-- result of the function.
| eval_fn:
  ∀ (e callee:LExpr LMonoTy IDMeta) args fn denotefn,
    F.callOfLFunc e = .some (callee,args,fn) →
    args.all (LExpr.isCanonicalValue F) →
    fn.concreteEval = .some denotefn →
    Step F state  e (denotefn (LExpr.mkApp callee args) args)


theorem step_const_stuck:
  ∀ (F:@Factory IDMeta) (state:Scopes IDMeta) x e,
  ¬ Step F state  (.const x) e := by
  intros
  intro H
  contradiction

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
inductive StepStar (F:@Factory IDMeta) (state:Scopes IDMeta)
  : LExpr LMonoTy IDMeta → LExpr LMonoTy IDMeta → Prop where
| refl : StepStar F state e e
| step : ∀ e e' e'', Step F state e e' → StepStar F state e' e''
        → StepStar F state e e''

end Lambda
