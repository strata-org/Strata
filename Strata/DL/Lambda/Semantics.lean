/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LState
import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Lambda

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]

open Lambda

/--
A free variable -> expression mapping.
-/
abbrev Env (Tbase:LExprParams) := Tbase.Identifier → Option (LExpr Tbase.mono)

def Scopes.toEnv (s:Scopes Tbase) : Env Tbase :=
  fun t => (s.find? t).map (·.snd)

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
/-- A free variable. Stuck if `fvar` does not exist in `FreeVarMap`. -/
| expand_fvar:
  ∀ (x:Tbase.Identifier) (e:LExpr Tbase.mono),
    rf x = .some e →
    Step F rf (.fvar m x ty) e

/-- Call-by-value semantics: beta reduction. -/
| beta:
  ∀ (e1 v2 eres:LExpr Tbase.mono),
    LExpr.isCanonicalValue F v2 →
    eres = LExpr.subst (fun _ => v2) e1 →
    Step F rf (.app m1 (.abs m2 ty e1) v2) eres

/-- Call-by-value semantics: argument evaluation. -/
| reduce_2:
  ∀ (v1 e2 e2':LExpr Tbase.mono),
    LExpr.isCanonicalValue F v1 →
    Step F rf e2 e2' →
    Step F rf (.app m v1 e2) (.app m' v1 e2')

/-- Call-by-value semantics: function evaluation. -/
| reduce_1:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.app m e1 e2) (.app m' e1' e2)

/-- Lazy evaluation of `ite`: condition is true. To evaluate `ite x e1 e2`, do
not first evaluate `e1` and `e2`. In other words, `ite x e1 e2` is interpreted
as `ite x (λ.e1) (λ.e2)`.  -/
| ite_reduce_then:
  ∀ (ethen eelse:LExpr Tbase.mono),
    Step F rf (.ite m (.const mc (.boolConst true)) ethen eelse) ethen

/-- Lazy evaluation of `ite`: condition is false. To evaluate `ite x e1 e2`, do
not first evaluate `e1` and `e2`. In other words, `ite x e1 e2` is interpreted
as `ite x (λ.e1) (λ.e2)`.  -/
| ite_reduce_else:
  ∀ (ethen eelse:LExpr Tbase.mono),
    Step F rf (.ite m (.const mc (.boolConst false)) ethen eelse) eelse

/-- Evaluation of `ite` condition. -/
| ite_reduce_cond:
  ∀ (econd econd' ethen eelse:LExpr Tbase.mono),
    Step F rf econd econd' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd' ethen eelse)

/-- Evaluation of equality. Reduce after both operands evaluate to values. -/
| eq_reduce:
  ∀ (e1 e2 eres:LExpr Tbase.mono)
    (H1:LExpr.isCanonicalValue F e1)
    (H2:LExpr.isCanonicalValue F e2),
    eres = .const mc (.boolConst (LExpr.eql F e1 e2 H1 H2)) →
    Step F rf (.eq m e1 e2) eres

/-- Evaluation of the left-hand side of an equality. -/
| eq_reduce_lhs:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.eq m e1 e2) (.eq m' e1' e2)

/-- Evaluation of the right-hand side of an equality. -/
| eq_reduce_rhs:
  ∀ (v1 e2 e2':LExpr Tbase.mono),
    LExpr.isCanonicalValue F v1 →
    Step F rf e2 e2' →
    Step F rf (.eq m v1 e2) (.eq m' v1 e2')

/-- Evaluate a built-in function when a body expression is available in the
`Factory` argument `F`. This is consistent with what `LExpr.eval` does (modulo
the `inline` flag). Note that it might also be possible to evaluate with
`eval_fn`. A key correctness property is that doing so will yield the same
result. Note that this rule does not enforce an evaluation order. -/
| expand_fn:
  ∀ (e callee fnbody new_body:LExpr Tbase.mono) args fn,
    F.callOfLFunc e = .some (callee,args,fn) →
    fn.body = .some fnbody →
    new_body = LExpr.substFvars fnbody (fn.inputs.keys.zip args) →
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


omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem step_const_stuck:
  ∀ (F:@Factory Tbase) r x e,
  ¬ Step F r (.const m x) e := by
  intros
  intro H
  contradiction

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
def StepStar (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop :=
  ReflTrans (Step F rf)

end Lambda
