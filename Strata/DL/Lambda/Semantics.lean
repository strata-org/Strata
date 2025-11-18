/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LState

---------------------------------------------------------------------

namespace Lamda

variable {IDMeta:Type} [DecidableEq IDMeta]

open Lambda

/--
A small-step semantics of LExpr.
Currently only defined for LMonoTy, but it will be expanded to an arbitrary
type.
-/
inductive Step
  : LState IDMeta → LExpr LMonoTy IDMeta → LExpr LMonoTy IDMeta → Prop where
-- A small-step reduction expands functions and free variables when they are
-- evaluated. Stucks if the function body is unknown or fvar does not exist
-- in LState.
| expand_fn:
  ∀ (σ:LState IDMeta) (func_id:Identifier IDMeta) (fn:LFunc IDMeta)
    (fnbody:LExpr LMonoTy IDMeta),
    σ.config.factory.getFactoryLFunc func_id.name = .some fn →
    fn.body = .some fnbody →
    Step σ (.op func_id _) fnbody

| expand_fvar:
  ∀ (σ:LState IDMeta) (x:Identifier IDMeta) (e:LExpr LMonoTy IDMeta),
    σ.state.find? x = .some (_,e) →
    Step σ (.fvar x _) e

-- Beta reduction for lambda; Call-by-value semantics.
| beta:
  ∀ (σ:LState IDMeta) (e1 v2:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ v2 →
    Step σ (.app (.abs _ e1) v2) (LExpr.subst e1 v2)

| cbv:
  ∀ (σ:LState IDMeta) (e1 e2 e2':LExpr LMonoTy IDMeta),
    Step σ e2 e2' →
    Step σ (.app e1 e2) (.app e1 e2')

-- Universal quantification.
| beta_univ:
  ∀ (σ:LState IDMeta) (e1 v2:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ v2 →
    Step σ (.app (.quant .all _ _ e1) v2) (LExpr.subst e1 v2)

-- For ite x e1 e2, do not eagerly evaluate e1 and e2.
-- It is interpreted as 'ite x (λ.e1) (λ.e2)'.
| beta_ite_then:
  ∀ (σ:LState IDMeta) (econd ethen eelse:LExpr LMonoTy IDMeta),
    econd = .const (.boolConst true) →
    Step σ (.ite econd ethen eelse) ethen

| beta_ite_else:
  ∀ (σ:LState IDMeta) (econd ethen eelse:LExpr LMonoTy IDMeta),
    econd = .const (.boolConst false) →
    Step σ (.ite econd ethen eelse) eelse

| cbv_ite_cond:
  ∀ (σ:LState IDMeta) (econd econd' ethen eelse:LExpr LMonoTy IDMeta),
    Step σ econd econd' →
    Step σ (.ite econd ethen eelse) (.ite econd' ethen eelse)

-- Equality. Reduce after both operands evaluate to values.
| beta_eq_true:
  ∀ (σ:LState IDMeta) (e1 e2:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ e1 → LExpr.isCanonicalValue σ e2 →
    e1 = e2 →
    Step σ (.eq e1 e2) (.const (.boolConst true))

| beta_eq_false:
  ∀ (σ:LState IDMeta) (e1 e2:LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ e1 → LExpr.isCanonicalValue σ e2 →
    ¬ (e1 = e2) →
    Step σ (.eq e1 e2) (.const (.boolConst false))

| cbv_eq_lhs:
  ∀ (σ:LState IDMeta) (e1 e1' e2:LExpr LMonoTy IDMeta),
    Step σ e1 e1' →
    Step σ (.eq e1 e2) (.eq e1' e2)

| cbv_eq_rhs:
  ∀ (σ:LState IDMeta) (e1 e2 e2':LExpr LMonoTy IDMeta),
    LExpr.isCanonicalValue σ e1 → Step σ e2 e2' →
    Step σ (.eq e1 e2) (.eq e1 e2')

-- Evaluation keeps the metadata.
| mdata:
  ∀ (σ:LState IDMeta) (e e':LExpr LMonoTy IDMeta) (m:Info),
    Step σ e e' →
    Step σ (.mdata m e) (.mdata m e')

end Lamda
