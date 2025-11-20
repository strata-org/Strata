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
inductive Step
  : LState IDMeta → LExpr LMonoTy IDMeta → LExpr LMonoTy IDMeta → Prop where
-- A free variable. Stuck if fvar does not exist in LState.
| expand_fvar:
  ∀ (σ:LState IDMeta) (x:Identifier IDMeta) (e:LExpr LMonoTy IDMeta),
    σ.state.find? x = .some (ty,e) →
    Step σ (.fvar x ty') e

-- Beta reduction for lambda; Call-by-value semantics.
| beta:
  ∀ (σ:LState IDMeta) (e1 v2:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ v2 →
    Step σ (.app (.abs ty e1) v2) (LExpr.subst v2 e1)

-- Universal quantification.
| beta_univ:
  ∀ (σ:LState IDMeta) (e1 v2 trig:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ v2 →
    Step σ (.app (.quant .all ty trig e1) v2) (LExpr.subst v2 e1)

-- Call-by-value semantics.
| reduce_2:
  ∀ (σ:LState IDMeta) (v1 e2 e2':LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ v1 →
    Step σ e2 e2' →
    Step σ (.app v1 e2) (.app v1 e2')

| reduce_1:
  ∀ (σ:LState IDMeta) (e1 e1' e2:LExpr LMonoTy IDMeta),
    Step σ e1 e1' →
    Step σ (.app e1 e2) (.app e1' e2)

-- For ite x e1 e2, do not eagerly evaluate e1 and e2.
-- For the reduction order, ite x e1 e2 is interpreted as
-- 'ite x (λ.e1) (λ.e2)'.
| ite_beta_then:
  ∀ (σ:LState IDMeta) (ethen eelse:LExpr LMonoTy IDMeta),
    Step σ (.ite (.const (.boolConst true)) ethen eelse) ethen

| ite_beta_else:
  ∀ (σ:LState IDMeta) (ethen eelse:LExpr LMonoTy IDMeta),
    Step σ (.ite (.const (.boolConst false)) ethen eelse) eelse

| ite_reduce_cond:
  ∀ (σ:LState IDMeta) (econd econd' ethen eelse:LExpr LMonoTy IDMeta),
    Step σ econd econd' →
    Step σ (.ite econd ethen eelse) (.ite econd' ethen eelse)

-- Equality. Reduce after both operands evaluate to values.
| beta_eq:
  ∀ (σ:LState IDMeta) (e1 e2:LExpr LMonoTy IDMeta)
    (H1:LExpr.isCanonicalValue σ e1)
    (H2:LExpr.isCanonicalValue σ e2),
    Step σ (.eq e1 e2) (.const (.boolConst (LExpr.eql σ e1 e2 H1 H2)))

| reduce_eq_lhs:
  ∀ (σ:LState IDMeta) (e1 e1' e2:LExpr LMonoTy IDMeta),
    Step σ e1 e1' →
    Step σ (.eq e1 e2) (.eq e1' e2)

| reduce_eq_rhs:
  ∀ (σ:LState IDMeta) (v1 e2 e2':LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ v1 → Step σ e2 e2' →
    Step σ (.eq v1 e2) (.eq v1 e2')

-- Evaluation keeps the metadata.
| mdata:
  ∀ (σ:LState IDMeta) (e e':LExpr LMonoTy IDMeta) (m:Info),
    Step σ e e' →
    Step σ (.mdata m e) (.mdata m e')

-- Expand functions and free variables when they are evaluated.
-- If the function body is unknown, concreteEval can be instead used. Look at
-- the eval_fn constructor below.
-- This is consistent with what LExpr.eval does (modulo the "inline" flag).
| expand_fn:
  ∀ (σ:LState IDMeta) (e callee fnbody new_body:LExpr LMonoTy IDMeta) args fn,
    σ.config.factory.callOfLFunc e = .some (callee,args,fn) →
    args.all (LExpr.isCanonicalValue σ) →
    fn.body = .some fnbody →
    new_body = LExpr.substFvars fnbody (fn.inputs.keys.zip args) →
    Step σ e new_body

-- The second way of evaluating a function call.
-- If LFunc has a concrete evaluator, this can be used to 'jump' to the final
-- result of the function.
| eval_fn:
  ∀ (σ:LState IDMeta) (e callee:LExpr LMonoTy IDMeta) args fn denotefn,
    σ.config.factory.callOfLFunc e = .some (callee,args,fn) →
    args.all (LExpr.isCanonicalValue σ) →
    fn.concreteEval = .some denotefn →
    Step σ e (denotefn (LExpr.mkApp callee args) args)


theorem step_const_stuck:
  ∀ (σ:LState IDMeta) x e, ¬ Step σ (.const x) e := by
  intros σ x e H
  contradiction

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
inductive StepStar
  : LState IDMeta → LExpr LMonoTy IDMeta → LExpr LMonoTy IDMeta → Prop where
| refl : ∀ σ e, StepStar σ e e
| step : ∀ σ e e' e'', Step σ e e' → StepStar σ e' e'' → StepStar σ e e''

end Lambda
