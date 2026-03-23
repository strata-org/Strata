/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF
public import Strata.DL.Lambda.LState
import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.Scopes
public import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

public section

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
    Step F rf (.app m1 (.abs m2 name ty e1) v2) eres

/-- Argument evaluation: reduce the argument of an application.
Note: this rule does NOT require the function part to be a canonical value.
This relaxes the strict call-by-value discipline to allow stepping any
argument of an application, which is needed for factory calls where `eval`
evaluates all arguments independently (not left-to-right). -/
| reduce_2:
  ∀ (e1 e2 e2':LExpr Tbase.mono),
    Step F rf e2 e2' →
    Step F rf (.app m e1 e2) (.app m' e1 e2')

/-- Call-by-value semantics: function evaluation. -/
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
  ∀ (e1 e2:LExpr Tbase.mono)
    (H1:LExpr.isCanonicalValue F e1)
    (H2:LExpr.isCanonicalValue F e2),
    LExpr.eql F e1 e2 H1 H2 = true →
    Step F rf (.eq m e1 e2) (.const mc (.boolConst true))

/-- Evaluation of equality to false. Only when neither side contains a binder,
    because syntactic inequality under binders does not imply semantic inequality
    (e.g., `λx. x+1` vs `λx. 1+x`). -/
| eq_reduce_false:
  ∀ (e1 e2:LExpr Tbase.mono)
    (H1:LExpr.isCanonicalValue F e1)
    (H2:LExpr.isCanonicalValue F e2),
    LExpr.eql F e1 e2 H1 H2 = false →
    e1.containsBinder = false →
    e2.containsBinder = false →
    Step F rf (.eq m e1 e2) (.const mc (.boolConst false))

/-- Evaluation of the left-hand side of an equality. -/
| eq_reduce_lhs:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.eq m e1 e2) (.eq m' e1' e2)

/-- Evaluation of the right-hand side of an equality.
Note: this rule does NOT require the LHS to be a canonical value.
This relaxes the strict call-by-value discipline, analogous to how
`reduce_2` was relaxed for application arguments. -/
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

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem step_abs_stuck:
  ∀ (F:@Factory Tbase) r n t body e,
  ¬ Step F r (.abs m n t body) e := by
  intros; intro H; cases H with
  | expand_fn _ _ _ _ _ _ h => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h
  | eval_fn _ _ _ _ _ _ h => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem step_quant_stuck:
  ∀ (F:@Factory Tbase) r qk n ty tr body e,
  ¬ Step F r (.quant m qk n ty tr body) e := by
  intros; intro H; cases H with
  | expand_fn _ _ _ _ _ _ h => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h
  | eval_fn _ _ _ _ _ _ h => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h

-- If e is stuck for Step, then ReflTrans (Step) e e' implies e = e'.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem ReflTrans_stuck {e e' : LExpr Tbase.mono}
    (h : ReflTrans (Step F rf) e e')
    (h_stuck : ∀ e'', ¬ Step F rf e e'') :
    e = e' := by
  cases h with
  | refl => rfl
  | step _ b _ hab _ => exact absurd hab (h_stuck b)

-- canonical_value_not_step is proved after the helper lemmas below (see ~line 965).

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
@[expose] def StepStar (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop :=
  ReflTrans (Step F rf)

/--
Confluence properties for Factory's `concreteEval` operations.
States that concrete evaluators are well-behaved with respect to
the operational semantics: they are metadata-independent, and if
the inputs to a factory operation are further reduced, the output
is also further reduced (joinable via StepStar).
-/
structure FactorySemConfluent (F : @Factory Tbase) (rf : Env Tbase) where
  /-- `concreteEval` is independent of metadata (up to `eraseMetadata`):
      if the same function is called with the same arguments but
      different metadata, the results agree modulo metadata. -/
  eval_metadata_indep :
    ∀ fn, fn ∈ F → ∀ denotefn, fn.concreteEval = some denotefn →
      ∀ m₁ m₂ args e₁ e₂,
        denotefn m₁ args = some e₁ → denotefn m₂ args = some e₂ →
        e₁.eraseMetadata = e₂.eraseMetadata
  /-- `concreteEval` is confluent with argument stepping:
      if `denotefn m args = some result` and we step the arguments
      (each arg via `ReflTrans Step`), then `denotefn` also succeeds
      on the stepped arguments, and the two results are joinable
      via `ReflTrans Step` modulo `eraseMetadata`. -/
  eval_arg_step :
    ∀ fn, fn ∈ F → ∀ denotefn, fn.concreteEval = some denotefn →
      ∀ m args result, denotefn m args = some result →
        ∀ args',
          args.length = args'.length →
          (∀ i (hi₁ : i < args.length) (hi₂ : i < args'.length),
            ReflTrans (Step F rf) args[i] args'[i]) →
          ∃ result', denotefn m args' = some result' ∧
            ∃ e₃ e₃',
              ReflTrans (Step F rf) result e₃ ∧
              ReflTrans (Step F rf) result' e₃' ∧
              e₃.eraseMetadata = e₃'.eraseMetadata

/-- Single-step canonicalization: either a Step reduction, or going under
    one binder (abs/quant) or app sub-expression by one Canonicalize step.
    This is a small-step relation; `CanonStar` is its reflexive-transitive closure. -/
inductive Canonicalize (F : @Factory Tbase) (rf : Env Tbase)
    : LExpr Tbase.mono → LExpr Tbase.mono → Prop where
/-- Lift a Step into Canonicalize. -/
| step : Step F rf a b → Canonicalize F rf a b
/-- Go under abs binder. -/
| abs : Canonicalize F rf body body' →
    Canonicalize F rf (.abs m n t body) (.abs m n t body')
/-- Go under quant: step the trigger. -/
| quant_tr : Canonicalize F rf tr tr' →
    Canonicalize F rf (.quant m qk n ty tr body) (.quant m qk n ty tr' body)
/-- Go under quant: step the body. -/
| quant_body : Canonicalize F rf body body' →
    Canonicalize F rf (.quant m qk n ty tr body) (.quant m qk n ty tr body')
/-- Go inside app: step the function. -/
| app_fn : Canonicalize F rf f f' →
    Canonicalize F rf (.app m f a) (.app m f' a)
/-- Go inside app: step the argument. -/
| app_arg : Canonicalize F rf a a' →
    Canonicalize F rf (.app m f a) (.app m f a')
/-- Go inside ite: step the condition. -/
| ite_cond : Canonicalize F rf c c' →
    Canonicalize F rf (.ite m c t f) (.ite m c' t f)
/-- Go inside ite: step the then branch. -/
| ite_then : Canonicalize F rf t t' →
    Canonicalize F rf (.ite m c t f) (.ite m c t' f)
/-- Go inside ite: step the else branch. -/
| ite_else : Canonicalize F rf f f' →
    Canonicalize F rf (.ite m c t f) (.ite m c t f')
/-- Go inside eq: step the lhs. -/
| eq_lhs : Canonicalize F rf e1 e1' →
    Canonicalize F rf (.eq m e1 e2) (.eq m e1' e2)
/-- Go inside eq: step the rhs. -/
| eq_rhs : Canonicalize F rf e2 e2' →
    Canonicalize F rf (.eq m e1 e2) (.eq m e1 e2')

/-- CanonStar: reflexive-transitive closure of Canonicalize (= Step ∪ structural). -/
abbrev CanonStar (F : @Factory Tbase) (rf : Env Tbase) :=
  ReflTrans (Canonicalize F rf)

-- Convenience constructors and derived lemmas.
namespace CanonStar

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]
    {F : @Factory Tbase} {rf : Env Tbase}

/-- Lift ReflTrans Step into CanonStar. -/
theorem ofStepStar (h : ReflTrans (Step F rf) a b) : CanonStar F rf a b := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.step hab) ih

/-- CanonStar is transitive (inherited from ReflTrans). -/
theorem trans (h₁ : CanonStar F rf a b) (h₂ : CanonStar F rf b c) :
    CanonStar F rf a c := by
  induction h₁ with
  | refl => exact h₂
  | step _ _ _ hab _ ih => exact .step _ _ _ hab (ih h₂)

/-- Lift CanonStar under abs. -/
theorem abs (h : CanonStar F rf body body') :
    CanonStar F rf (.abs m n t body) (.abs m n t body') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.abs hab) ih

/-- Lift CanonStar under quant trigger. -/
theorem quant_tr (h : CanonStar F rf tr tr') :
    CanonStar F rf (.quant m qk n ty tr body) (.quant m qk n ty tr' body) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.quant_tr hab) ih

/-- Lift CanonStar under quant body. -/
theorem quant_body (h : CanonStar F rf body body') :
    CanonStar F rf (.quant m qk n ty tr body) (.quant m qk n ty tr body') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.quant_body hab) ih

/-- Lift CanonStar under app function. -/
theorem app_fn (h : CanonStar F rf f f') :
    CanonStar F rf (.app m f a) (.app m f' a) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.app_fn hab) ih

/-- Lift CanonStar under app argument. -/
theorem app_arg (h : CanonStar F rf a a') :
    CanonStar F rf (.app m f a) (.app m f a') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.app_arg hab) ih

/-- Lift CanonStar under ite condition. -/
theorem ite_cond (h : CanonStar F rf c c') :
    CanonStar F rf (.ite m c t f) (.ite m c' t f) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.ite_cond hab) ih

/-- Lift CanonStar under ite then branch. -/
theorem ite_then (h : CanonStar F rf t t') :
    CanonStar F rf (.ite m c t f) (.ite m c t' f) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.ite_then hab) ih

/-- Lift CanonStar under ite else branch. -/
theorem ite_else (h : CanonStar F rf f f') :
    CanonStar F rf (.ite m c t f) (.ite m c t f') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.ite_else hab) ih

/-- Lift CanonStar under eq lhs. -/
theorem eq_lhs (h : CanonStar F rf e1 e1') :
    CanonStar F rf (.eq m e1 e2) (.eq m e1' e2) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.eq_lhs hab) ih

/-- Lift CanonStar under eq rhs. -/
theorem eq_rhs (h : CanonStar F rf e2 e2') :
    CanonStar F rf (.eq m e1 e2) (.eq m e1 e2') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih => exact .step _ _ _ (.eq_rhs hab) ih

end CanonStar

/--
Value equivalence for canonical values. Two canonical values are `ValEquiv`
when they have the same observable structure modulo metadata:
- Constants and operators: same value/name.
- Abstractions/quantifiers: bodies canonicalize to structurally equal
  expressions (modulo metadata). This handles e.g. `\x. 1+1 ≡ \x. 2`.
- Factory applications: equivalent function part and equivalent argument,
  with an explicit guard that the application is canonical.

This captures "indistinguishable from the outside user": an observer cannot
tell apart two `ValEquiv` values by any sequence of applications or pattern
matches, because they have identical structure at every observable level.
-/
inductive ValEquiv (F : @Factory Tbase) (rf : Env Tbase)
    : LExpr Tbase.mono → LExpr Tbase.mono → Prop where
/-- Constants: same constant value. -/
| const : ValEquiv F rf (.const m₁ c) (.const m₂ c)
/-- Factory operators: same name and type. -/
| op : ValEquiv F rf (.op m₁ n t) (.op m₂ n t)
/-- Abstractions: both sides are canonical (closed), and bodies canonicalize
    to equal expressions (modulo metadata). -/
| abs :
    LExpr.isCanonicalValue F (.abs m₁ n t b₁) = true →
    LExpr.isCanonicalValue F (.abs m₂ n t b₂) = true →
    CanonStar F rf b₁ b₁' → CanonStar F rf b₂ b₂' →
    b₁'.eraseMetadata = b₂'.eraseMetadata →
    ValEquiv F rf (.abs m₁ n t b₁) (.abs m₂ n t b₂)
/-- Quantifiers: both sides are canonical (closed), and sub-expressions
    canonicalize to equal (modulo metadata). -/
| quant :
    LExpr.isCanonicalValue F (.quant m₁ qk n ty t₁ b₁) = true →
    LExpr.isCanonicalValue F (.quant m₂ qk n ty t₂ b₂) = true →
    CanonStar F rf t₁ t₁' → CanonStar F rf t₂ t₂' →
    t₁'.eraseMetadata = t₂'.eraseMetadata →
    CanonStar F rf b₁ b₁' → CanonStar F rf b₂ b₂' →
    b₁'.eraseMetadata = b₂'.eraseMetadata →
    ValEquiv F rf (.quant m₁ qk n ty t₁ b₁) (.quant m₂ qk n ty t₂ b₂)
/-- Canonical factory applications: equivalent function and argument parts.
    The `isCanonicalValue` guard ensures this only relates canonical apps. -/
| app :
    LExpr.isCanonicalValue F (.app m₁ f₁ a₁) = true →
    ValEquiv F rf f₁ f₂ → ValEquiv F rf a₁ a₂ →
    ValEquiv F rf (.app m₁ f₁ a₁) (.app m₂ f₂ a₂)

-- Reflexivity, symmetry, transitivity are proved after the helper lemmas
-- (see after canonical_value_not_step).

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
theorem ReflTrans_trans {r : Relation (LExpr Tbase.mono)} {x y z : LExpr Tbase.mono}
    (h1 : ReflTrans r x y) (h2 : ReflTrans r y z) : ReflTrans r x z := by
  induction h1 with
  | refl => exact h2
  | step _ b _ hab _ ih => exact ReflTrans.step _ b _ hab (ih h2)

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_ite_cond (F : @Factory Tbase) (rf : Env Tbase)
    (c c' t f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) c c') :
    ∃ m', ReflTrans (Step F rf) (.ite m c t f) (.ite m' c' t f) := by
  induction h with
  | refl => exact ⟨m, ReflTrans.refl _⟩
  | step x y z hxy _ ih =>
    obtain ⟨m1, h1⟩ := ih
    exact ⟨m1, ReflTrans.step _ (.ite m y t f) _
      (Step.ite_reduce_cond (m' := m) x y t f hxy) h1⟩

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_ite_then (F : @Factory Tbase) (rf : Env Tbase)
    (c t t' f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) t t') :
    ∃ m', ReflTrans (Step F rf) (.ite m c t f) (.ite m' c t' f) := by
  induction h with
  | refl => exact ⟨m, ReflTrans.refl _⟩
  | step x y z hxy _ ih =>
    obtain ⟨m1, h1⟩ := ih
    exact ⟨m1, ReflTrans.step _ (.ite m c y f) _
      (Step.ite_reduce_then_branch (m' := m) c x y f hxy) h1⟩

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_ite_else (F : @Factory Tbase) (rf : Env Tbase)
    (c t f f' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) f f') :
    ∃ m', ReflTrans (Step F rf) (.ite m c t f) (.ite m' c t f') := by
  induction h with
  | refl => exact ⟨m, ReflTrans.refl _⟩
  | step x y z hxy _ ih =>
    obtain ⟨m1, h1⟩ := ih
    exact ⟨m1, ReflTrans.step _ (.ite m c t y) _
      (Step.ite_reduce_else_branch (m' := m) c t x y hxy) h1⟩

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_eq_lhs (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) e1 e1') :
    ∃ m', ReflTrans (Step F rf) (.eq m e1 e2) (.eq m' e1' e2) := by
  induction h with
  | refl => exact ⟨m, ReflTrans.refl _⟩
  | step x y z hxy _ ih =>
    obtain ⟨m1, h1⟩ := ih
    exact ⟨m1, ReflTrans.step _ (.eq m y e2) _
      (Step.eq_reduce_lhs (m' := m) x y e2 hxy) h1⟩

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_eq_rhs (F : @Factory Tbase) (rf : Env Tbase)
    (e1 : LExpr Tbase.mono)
    (e2 e2' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) e2 e2') :
    ∃ m', ReflTrans (Step F rf) (.eq m e1 e2) (.eq m' e1 e2') := by
  induction h with
  | refl => exact ⟨m, ReflTrans.refl _⟩
  | step x y z hxy _ ih =>
    obtain ⟨m1, h1⟩ := ih
    exact ⟨m1, ReflTrans.step _ (.eq m e1 y) _
      (Step.eq_reduce_rhs (m' := m) e1 x y hxy) h1⟩

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_app_fn (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) e1 e1') :
    ReflTrans (Step F rf) (.app m e1 e2) (.app m e1' e2) := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.app m y e2) _
      (Step.reduce_1 (m' := m) x y e2 hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_app_arg (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e2 e2' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) e2 e2') :
    ReflTrans (Step F rf) (.app m e1 e2) (.app m e1 e2') := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.app m e1 y) _
      (Step.reduce_2 (m' := m) e1 x y hxy) ih

---------------------------------------------------------------------
-- Helper lemmas for substFvar / substFvars

private theorem Maps_findD_find?_none [DecidableEq α]
    (ms : Maps α β) (x : α) (d : β)
    (h : Maps.find? ms x = none) :
    Maps.findD ms x d = d := by
  induction ms with
  | nil => simp [Maps.findD]
  | cons m rest ih =>
    simp only [Maps.find?, Maps.findD] at h ⊢
    split <;> simp_all

private theorem Maps_findD_find?_some [DecidableEq α]
    (ms : Maps α β) (x : α) (d : β) (v : β)
    (h : Maps.find? ms x = some v) :
    Maps.findD ms x d = v := by
  induction ms with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Maps.find?, Maps.findD] at h ⊢
    split <;> simp_all

private theorem substFvar_no_freeVars
    {T : LExprParams} [DecidableEq T.IDMeta]
    (e : LExpr T.mono) (h : LExpr.freeVars e = [])
    (fr : Identifier T.IDMeta) (to : LExpr T.mono) :
    LExpr.substFvar e fr to = e := by
  induction e with
  | const => simp [LExpr.substFvar]
  | op => simp [LExpr.substFvar]
  | bvar => simp [LExpr.substFvar]
  | fvar => simp [LExpr.freeVars] at h
  | abs _ _ _ _ ih => simp [LExpr.freeVars] at h; simp [LExpr.substFvar, ih h]
  | quant _ _ _ _ _ _ ih1 ih2 =>
    simp [LExpr.freeVars] at h; simp [LExpr.substFvar, ih1 h.1, ih2 h.2]
  | app _ _ _ ih1 ih2 =>
    simp [LExpr.freeVars] at h; simp [LExpr.substFvar, ih1 h.1, ih2 h.2]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp [LExpr.freeVars] at h; simp [LExpr.substFvar, ih1 h.1, ih2 h.2.1, ih3 h.2.2]
  | eq _ _ _ ih1 ih2 =>
    simp [LExpr.freeVars] at h; simp [LExpr.substFvar, ih1 h.1, ih2 h.2]

-- substFvar is identity when the target identifier is not a free variable.
private theorem substFvar_not_freeVar
    {T : LExprParams} [DecidableEq T.IDMeta]
    (e : LExpr T.mono) (fr : Identifier T.IDMeta) (to : LExpr T.mono)
    (h : fr ∉ (LExpr.freeVars e).map Prod.fst) :
    LExpr.substFvar e fr to = e := by
  induction e with
  | const => simp [LExpr.substFvar]
  | op => simp [LExpr.substFvar]
  | bvar => simp [LExpr.substFvar]
  | fvar _ x _ =>
    simp [LExpr.freeVars] at h
    simp only [LExpr.substFvar]; split <;> simp_all
  | abs _ _ _ _ ih =>
    simp only [LExpr.freeVars] at h; simp [LExpr.substFvar, ih h]
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.freeVars, List.map_append, List.mem_append, not_or] at h
    simp [LExpr.substFvar, ih1 h.1, ih2 h.2]
  | quant _ _ _ _ _ _ ih1 ih2 =>
    simp only [LExpr.freeVars, List.map_append, List.mem_append, not_or] at h
    simp [LExpr.substFvar, ih1 h.1, ih2 h.2]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.freeVars, List.map_append, List.mem_append, not_or] at h
    simp [LExpr.substFvar, ih1 h.1.1, ih2 h.1.2, ih3 h.2]
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.freeVars, List.map_append, List.mem_append, not_or] at h
    simp [LExpr.substFvar, ih1 h.1, ih2 h.2]

-- freeVars is invariant under eraseMetadata.
private theorem freeVars_eraseMetadata {T : LExprParamsT}
    (e : LExpr T) :
    LExpr.freeVars e.eraseMetadata = LExpr.freeVars e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs _ _ _ _ ih => exact ih
  | app _ _ _ ih1 ih2 => show _ ++ _ = _ ++ _; exact congr (congrArg _ ih1) ih2
  | quant _ _ _ _ _ _ ih1 ih2 => show _ ++ _ = _ ++ _; exact congr (congrArg _ ih1) ih2
  | ite _ _ _ _ ih1 ih2 ih3 =>
    show _ ++ _ ++ _ = _ ++ _ ++ _
    unfold LExpr.eraseMetadata at ih1 ih2 ih3; rw [ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => show _ ++ _ = _ ++ _; exact congr (congrArg _ ih1) ih2

-- If two expressions have the same eraseMetadata, they have the same freeVars.
private theorem freeVars_of_eraseMetadata_eq {T : LExprParamsT}
    (e₁ e₂ : LExpr T) (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.freeVars e₁ = LExpr.freeVars e₂ := by
  have h1 := freeVars_eraseMetadata e₁
  have h2 := freeVars_eraseMetadata e₂
  rw [h] at h1; rw [← h1, h2]

-- substFvar commutes with eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvar_eraseMetadata_comm
    (e : LExpr Tbase.mono) (fr : Tbase.Identifier) (to : LExpr Tbase.mono) :
    (LExpr.substFvar e fr to).eraseMetadata =
      LExpr.substFvar e.eraseMetadata fr to.eraseMetadata := by
  induction e with
  | fvar _ x _ =>
    simp only [LExpr.substFvar, LExpr.eraseMetadata, LExpr.replaceMetadata]
    split <;> simp_all [LExpr.substFvar, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | const | op | bvar => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.substFvar]
  | abs _ _ _ _ ih => exact congrArg (LExpr.abs () _ _) ih
  | app _ _ _ ih1 ih2 => exact congr (congrArg _ ih1) ih2
  | eq _ _ _ ih1 ih2 => exact congr (congrArg _ ih1) ih2
  | quant _ _ _ _ _ _ ih1 ih2 => exact congr (congrArg _ ih1) ih2
  | ite _ _ _ _ ih1 ih2 ih3 => exact congr (congr (congrArg _ ih1) ih2) ih3

-- Corollary: substFvar preserves eraseMetadata equality.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvar_eraseMetadata_congr
    (e₁ e₂ : LExpr Tbase.mono) (fr : Tbase.Identifier) (to : LExpr Tbase.mono)
    (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.substFvar e₁ fr to).eraseMetadata = (LExpr.substFvar e₂ fr to).eraseMetadata := by
  rw [substFvar_eraseMetadata_comm, substFvar_eraseMetadata_comm, h]

-- Extension to substFvars: preserves eraseMetadata equality.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_eraseMetadata_congr
    (e₁ e₂ : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.substFvars e₁ sm).eraseMetadata = (LExpr.substFvars e₂ sm).eraseMetadata := by
  simp only [LExpr.substFvars]
  induction sm generalizing e₁ e₂ with
  | nil => simp [List.foldl]; exact h
  | cons p rest ih =>
    simp only [List.foldl]
    exact ih _ _ (substFvar_eraseMetadata_congr e₁ e₂ p.1 p.2 h)

private theorem substFvars_of_substFvar_id [DecidableEq T.IDMeta] [BEq T.IDMeta]
    (e : LExpr ⟨T, GenericTy⟩)
    (h : ∀ fr to, LExpr.substFvar e fr to = e)
    (sm : List (Identifier T.IDMeta × LExpr ⟨T, GenericTy⟩)) :
    List.foldl (fun e (p : Identifier T.IDMeta × LExpr ⟨T, GenericTy⟩) =>
      LExpr.substFvar e p.1 p.2) e sm = e := by
  induction sm with
  | nil => rfl
  | cons p rest ih => simp [List.foldl, h, ih]

set_option checkBinderAnnotations false in
private theorem substFvarsFromState_closed
    {Tbase : LExprParams} [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono)
    (h : LExpr.freeVars e = []) :
    LExpr.substFvarsFromState σ e = e := by
  simp [LExpr.substFvarsFromState, LExpr.substFvars]
  exact substFvars_of_substFvar_id _ (substFvar_no_freeVars e h) _

/-- If `Maps.find?` returns `none` for `x`, then `x` is not a key in the
flattened single map. -/
private theorem Maps_find?_none_substFvars_fvar [DecidableEq α]
    (ms : Maps α β) (x : α) (h : Maps.find? ms x = none) :
    Map.find? ms.toSingleMap x = none := by
  induction ms with
  | nil =>
    show Map.find? ([] : Maps α β).flatten x = none
    rw [List.flatten_nil]
    rfl
  | cons m rest ih =>
    simp only [Maps.find?] at h
    cases hm : Map.find? m x with
    | some v => rw [hm] at h; simp at h
    | none =>
      rw [hm] at h
      have ih_rest := ih h
      have hm_not_mem := Map.findNone_eq_notmem_mapfst.mpr hm
      have hr_not_mem := Map.findNone_eq_notmem_mapfst.mpr ih_rest
      apply Map.findNone_eq_notmem_mapfst.mp
      show ¬ x ∈ List.map Prod.fst ((m :: rest : Maps α β).flatten)
      rw [List.flatten_cons, List.map_append, List.mem_append]
      exact fun hor => hor.elim hm_not_mem hr_not_mem

set_option checkBinderAnnotations false in
/-- If `x` is not found in any scope, `substFvarsFromState` on `.fvar x` is
the identity. -/
private theorem substFvarsFromState_fvar_none
    {Tbase : LExprParams} [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (m_meta : Tbase.Metadata) (x : Tbase.Identifier)
    (ty : Option LMonoTy) (h : Maps.find? σ.state x = none) :
    LExpr.substFvarsFromState σ (.fvar m_meta x ty) = .fvar m_meta x ty := by
  have h_flat := Maps_find?_none_substFvars_fvar σ.state x h
  have h_not_mem := Map.findNone_eq_notmem_mapfst.mpr h_flat
  -- The mapped list preserves keys, so x is not a key there either
  have h_mapped_not_mem : ¬ x ∈ (σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v))).map Prod.fst := by
    simp only [List.map_map] at *
    exact h_not_mem
  simp only [LExpr.substFvarsFromState, LExpr.substFvars]
  generalize σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v)) = sm at h_mapped_not_mem
  induction sm with
  | nil => rfl
  | cons p rest ih_sm =>
    simp only [List.foldl]
    have h_ne : p.1 ≠ x := by
      intro h_eq
      exact h_mapped_not_mem (by rw [List.map_cons]; exact List.mem_cons.mpr (.inl h_eq.symm))
    rw [substFvar_not_freeVar (.fvar m_meta x ty) p.1 p.2 (by
      simp only [LExpr.freeVars, List.map, List.mem_cons, List.mem_nil_iff, or_false]
      exact fun h => h_ne h)]
    exact ih_sm (fun hmem => h_mapped_not_mem (List.mem_cons_of_mem _ hmem))

/-- If `substFvars e sm` is closed, appending more substitutions has no effect. -/
private theorem substFvars_append_closed
    {T : LExprParams} [DecidableEq T.IDMeta]
    (e : LExpr T.mono)
    (sm1 sm2 : Map (Identifier T.IDMeta) (LExpr T.mono))
    (h : LExpr.freeVars (LExpr.substFvars e sm1) = []) :
    LExpr.substFvars e (sm1 ++ sm2) = LExpr.substFvars e sm1 := by
  simp only [LExpr.substFvars] at *
  rw [List.foldl_append]
  induction sm2 with
  | nil => simp [List.foldl]
  | cons p rest ih =>
    simp only [List.foldl]; rw [substFvar_no_freeVars _ h]; exact ih

-- substFvar with a closed value doesn't grow freeVars: if k was not free
-- in e, it's not free after substFvar e fr to (when to is closed).
private theorem substFvar_freeVars_not_mem
    {T : LExprParams} [DecidableEq T.IDMeta]
    (e : LExpr T.mono) (fr : T.Identifier) (to : LExpr T.mono)
    (hto : LExpr.freeVars to = [])
    (k : Identifier T.IDMeta)
    (hk : k ∉ (LExpr.freeVars e).map Prod.fst) :
    k ∉ (LExpr.freeVars (LExpr.substFvar e fr to)).map Prod.fst := by
  induction e with
  | const => simp [LExpr.substFvar, LExpr.freeVars]
  | op => simp [LExpr.substFvar, LExpr.freeVars]
  | bvar => simp [LExpr.substFvar, LExpr.freeVars]
  | fvar m x ty =>
    simp only [LExpr.substFvar]
    split
    · simp [LExpr.freeVars, hto]
    · exact hk
  | abs m name ty body ih =>
    simp only [LExpr.substFvar, LExpr.freeVars] at *; exact ih hk
  | quant m qk name ty tr body ih1 ih2 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨ih1 hk.1, ih2 hk.2⟩
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨ih1 hk.1, ih2 hk.2⟩
  | ite m c t f ih1 ih2 ih3 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨⟨ih1 hk.1.1, ih2 hk.1.2⟩, ih3 hk.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨ih1 hk.1, ih2 hk.2⟩

-- After substFvar e fr v where v is closed, fr is not free in the result.
private theorem substFvar_eliminates_key
    {T : LExprParams} [DecidableEq T.IDMeta]
    (e : LExpr T.mono) (fr : T.Identifier) (v : LExpr T.mono)
    (hv : LExpr.freeVars v = []) :
    fr ∉ (LExpr.freeVars (LExpr.substFvar e fr v)).map Prod.fst := by
  induction e with
  | const => simp [LExpr.substFvar, LExpr.freeVars]
  | op => simp [LExpr.substFvar, LExpr.freeVars]
  | bvar => simp [LExpr.substFvar, LExpr.freeVars]
  | fvar m x ty =>
    simp only [LExpr.substFvar]
    split
    · simp [LExpr.freeVars, hv]
    · rename_i h_ne
      simp only [LExpr.freeVars, List.map, List.mem_cons, List.mem_nil_iff, or_false]
      intro h_eq; simp [h_eq] at h_ne
  | abs _ _ _ _ ih => simp only [LExpr.substFvar, LExpr.freeVars] at *; exact ih
  | quant _ _ _ _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨ih1, ih2⟩
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨ih1, ih2⟩
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨⟨ih1, ih2⟩, ih3⟩
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvar, LExpr.freeVars, List.map_append, List.mem_append, not_or] at *
    exact ⟨ih1, ih2⟩

-- substFvars preserves "not free": if k ∉ freeVars e and all values in sm are
-- closed, then k ∉ freeVars (substFvars e sm).
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_preserves_not_free
    (e : LExpr Tbase.mono)
    (sm : List (Tbase.Identifier × LExpr Tbase.mono))
    (k : Tbase.Identifier)
    (hk : k ∉ (LExpr.freeVars e).map Prod.fst)
    (h_vals : ∀ p, p ∈ sm → LExpr.freeVars p.2 = []) :
    k ∉ (LExpr.freeVars (LExpr.substFvars e sm)).map Prod.fst := by
  induction sm generalizing e with
  | nil => simp only [LExpr.substFvars, List.foldl]; exact hk
  | cons p rest ih =>
    simp only [LExpr.substFvars, List.foldl] at *
    exact ih (LExpr.substFvar e p.1 p.2)
      (substFvar_freeVars_not_mem e p.1 p.2 (h_vals p (.head _)) k hk)
      (fun q hm => h_vals q (.tail _ hm))

-- substFvars with closed values: idempotent.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_idem
    (e : LExpr Tbase.mono)
    (sm : List (Tbase.Identifier × LExpr Tbase.mono))
    (h_vals : ∀ p, p ∈ sm → LExpr.freeVars p.2 = []) :
    LExpr.substFvars (LExpr.substFvars e sm) sm = LExpr.substFvars e sm := by
  induction sm generalizing e with
  | nil => rfl
  | cons p rest ih =>
    have hpv : LExpr.freeVars p.2 = [] := h_vals p (.head _)
    have h_rest : ∀ q, q ∈ rest → LExpr.freeVars q.2 = [] :=
      fun q hm => h_vals q (.tail _ hm)
    let e₁ := LExpr.substFvar e p.1 p.2
    -- substFvars e (p :: rest) = substFvars e₁ rest
    show LExpr.substFvars (LExpr.substFvars e₁ rest) (p :: rest) =
         LExpr.substFvars e₁ rest
    -- LHS unfolds to: substFvars (substFvar (substFvars e₁ rest) p.1 p.2) rest
    show LExpr.substFvars (LExpr.substFvar (LExpr.substFvars e₁ rest) p.1 p.2) rest =
         LExpr.substFvars e₁ rest
    -- Step 1: substFvar (substFvars e₁ rest) p.1 p.2 = substFvars e₁ rest
    have h_elim := substFvar_eliminates_key e p.1 p.2 hpv
    have h_not_free := substFvars_preserves_not_free _ rest p.1 h_elim h_rest
    rw [substFvar_not_freeVar _ p.1 p.2 h_not_free]
    -- Step 2: substFvars (substFvars e₁ rest) rest = substFvars e₁ rest (by IH)
    exact ih e₁ h_rest

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_const'
    (m : Tbase.Metadata) (c : LConst)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.const m c) sm = LExpr.const m c := by
  simp only [LExpr.substFvars]
  induction sm with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_op'
    (m : Tbase.Metadata) (n : Identifier Tbase.IDMeta) (t : Option Tbase.mono.TypeType)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.op m n t) sm = LExpr.op m n t := by
  simp only [LExpr.substFvars]
  induction sm with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_bvar
    (m : Tbase.Metadata) (i : Nat)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.bvar m i) sm = LExpr.bvar m i := by
  simp only [LExpr.substFvars]
  induction sm with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvarsFromState_const
    (σ : LState Tbase) (m : Tbase.Metadata) (c : LConst) :
    LExpr.substFvarsFromState σ (LExpr.const m c) = LExpr.const m c := by
  simp [LExpr.substFvarsFromState, substFvars_const']

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvarsFromState_op
    (σ : LState Tbase) (m : Tbase.Metadata) (n : Identifier Tbase.IDMeta)
    (t : Option Tbase.mono.TypeType) :
    LExpr.substFvarsFromState σ (LExpr.op m n t) = LExpr.op m n t := by
  simp [LExpr.substFvarsFromState, substFvars_op']

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvarsFromState_bvar
    (σ : LState Tbase) (m : Tbase.Metadata) (i : Nat) :
    LExpr.substFvarsFromState σ (LExpr.bvar m i) = LExpr.bvar m i := by
  simp [LExpr.substFvarsFromState, substFvars_bvar]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem substFvars_ite
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.ite m c t f) sm =
      LExpr.ite m (LExpr.substFvars c sm) (LExpr.substFvars t sm) (LExpr.substFvars f sm) := by
  simp only [LExpr.substFvars]
  induction sm generalizing c t f with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem substFvars_eq
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.eq m e1 e2) sm =
      LExpr.eq m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm) := by
  simp only [LExpr.substFvars]
  induction sm generalizing e1 e2 with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem substFvars_app
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.app m e1 e2) sm =
      LExpr.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm) := by
  simp only [LExpr.substFvars]
  induction sm generalizing e1 e2 with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem substFvars_abs
    (m : Tbase.Metadata) (name : String) (ty : Option LMonoTy) (body : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (.abs m name ty body) sm = .abs m name ty (LExpr.substFvars body sm) := by
  simp only [LExpr.substFvars]
  induction sm generalizing body with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem substFvars_quant
    (m : Tbase.Metadata) (qk : QuantifierKind) (name : String) (ty : Option LMonoTy)
    (tr body : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (.quant m qk name ty tr body) sm =
      .quant m qk name ty (LExpr.substFvars tr sm) (LExpr.substFvars body sm) := by
  simp only [LExpr.substFvars]
  induction sm generalizing tr body with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

---------------------------------------------------------------------
-- StepStar congruence through substFvar/substFvars.
-- If a →* a', then substFvar body x a →* substFvar body x a'.
-- Provable by induction on body using Step's congruence rules
-- (reduce_1/2, ite_reduce_*, eq_reduce_*). The abs/quant cases
-- require a Step rule for stepping inside binders (which doesn't
-- exist), so those cases are left as sorry.

-- Metadata-preserving ite/eq congruence lemmas (the existing StepStar_ite_*
-- return ∃ m', but we need metadata preserved for substFvar composition).

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_ite_cond_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c c' t f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) c c') :
    ReflTrans (Step F rf) (.ite m c t f) (.ite m c' t f) := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m y t f) _
      (Step.ite_reduce_cond (m' := m) x y t f hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_ite_then_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c t t' f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) t t') :
    ReflTrans (Step F rf) (.ite m c t f) (.ite m c t' f) := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m c y f) _
      (Step.ite_reduce_then_branch (m' := m) c x y f hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_ite_else_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c t f f' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) f f') :
    ReflTrans (Step F rf) (.ite m c t f) (.ite m c t f') := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m c t y) _
      (Step.ite_reduce_else_branch (m' := m) c t x y hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_eq_lhs_pres (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) e1 e1') :
    ReflTrans (Step F rf) (.eq m e1 e2) (.eq m e1' e2) := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.eq m y e2) _
      (Step.eq_reduce_lhs (m' := m) x y e2 hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_eq_rhs_pres (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e2 e2' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) e2 e2') :
    ReflTrans (Step F rf) (.eq m e1 e2) (.eq m e1 e2') := by
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.eq m e1 y) _
      (Step.eq_reduce_rhs (m' := m) e1 x y hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_substFvar (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono) (fr : Tbase.Identifier)
    (a a' : LExpr Tbase.mono)
    (h : ReflTrans (Step F rf) a a') :
    ReflTrans (Step F rf) (LExpr.substFvar body fr a) (LExpr.substFvar body fr a') := by
  induction body with
  | const => simp [LExpr.substFvar]; exact ReflTrans.refl _
  | op => simp [LExpr.substFvar]; exact ReflTrans.refl _
  | bvar => simp [LExpr.substFvar]; exact ReflTrans.refl _
  | fvar m x ty =>
    simp only [LExpr.substFvar]
    split
    · exact h
    · exact ReflTrans.refl _
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvar]
    exact ReflTrans_trans
      (StepStar_app_fn F rf _ _ _ m ih1)
      (StepStar_app_arg F rf _ _ _ m ih2)
  | ite m c t f ih1 ih2 ih3 =>
    simp only [LExpr.substFvar]
    exact ReflTrans_trans
      (ReflTrans_trans
        (StepStar_ite_cond_pres F rf _ _ _ _ m ih1)
        (StepStar_ite_then_pres F rf _ _ _ _ m ih2))
      (StepStar_ite_else_pres F rf _ _ _ _ m ih3)
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvar]
    exact ReflTrans_trans
      (StepStar_eq_lhs_pres F rf _ _ _ m ih1)
      (StepStar_eq_rhs_pres F rf _ _ _ m ih2)
  | abs m name ty body ih =>
    -- Step cannot go under abs binders. This case would need a rule like
    -- Step.reduce_abs or Canonicalize-based stepping.
    sorry
  | quant m qk name ty tr body ih1 ih2 =>
    -- Step cannot go under quant binders.
    sorry

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_substFvars (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono)
    (sm sm' : Map Tbase.Identifier (LExpr Tbase.mono))
    (h_keys : sm.map Prod.fst = sm'.map Prod.fst)
    (h_vals : ∀ k v v', List.Mem (k, v) sm → List.Mem (k, v') sm' →
      ReflTrans (Step F rf) v v') :
    ReflTrans (Step F rf) (LExpr.substFvars body sm) (LExpr.substFvars body sm') := by
  induction body with
  | const => rw [substFvars_const', substFvars_const']; exact ReflTrans.refl _
  | op => rw [substFvars_op', substFvars_op']; exact ReflTrans.refl _
  | bvar => rw [substFvars_bvar, substFvars_bvar]; exact ReflTrans.refl _
  | fvar m x ty =>
    -- The fold replaces x with the matching value from sm/sm', then applies
    -- remaining substitutions to that value. Proving the result steps correctly
    -- requires a recursive call on the matched value (not a sub-expression of
    -- .fvar), which structural induction on body cannot provide.
    sorry
  | app m e1 e2 ih1 ih2 =>
    rw [substFvars_app, substFvars_app]
    exact ReflTrans_trans
      (StepStar_app_fn F rf _ _ _ m ih1)
      (StepStar_app_arg F rf _ _ _ m ih2)
  | ite m c t f ih1 ih2 ih3 =>
    rw [substFvars_ite, substFvars_ite]
    exact ReflTrans_trans
      (ReflTrans_trans
        (StepStar_ite_cond_pres F rf _ _ _ _ m ih1)
        (StepStar_ite_then_pres F rf _ _ _ _ m ih2))
      (StepStar_ite_else_pres F rf _ _ _ _ m ih3)
  | eq m e1 e2 ih1 ih2 =>
    rw [substFvars_eq, substFvars_eq]
    exact ReflTrans_trans
      (StepStar_eq_lhs_pres F rf _ _ _ m ih1)
      (StepStar_eq_rhs_pres F rf _ _ _ m ih2)
  | abs m name ty body ih =>
    -- Step cannot go under abs binders.
    sorry
  | quant m qk name ty tr body ih1 ih2 =>
    -- Step cannot go under quant binders.
    sorry

-- Stepping the last arg in a zip-based substFvars: if a →* a', then
-- substFvars body (zip keys (pre ++ [a])) →* substFvars body (zip keys (pre ++ [a'])).
-- Uses fold decomposition: the shared prefix fold is identical, only the last
-- substFvar call differs, which is handled by StepStar_substFvar.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_substFvars_last_arg (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono)
    (keys : List Tbase.Identifier) (pre : List (LExpr Tbase.mono))
    (a a' : LExpr Tbase.mono)
    (h : ReflTrans (Step F rf) a a')
    (h_len : keys.length = pre.length + 1) :
    ReflTrans (Step F rf)
      (LExpr.substFvars body (keys.zip (pre ++ [a])))
      (LExpr.substFvars body (keys.zip (pre ++ [a']))) := by
  -- Split keys at the boundary
  have h_take_len : (keys.take pre.length).length = pre.length := by
    simp [Nat.min_eq_left (by omega : pre.length ≤ keys.length)]
  -- zip distributes over the split
  have h_zip : ∀ x, keys.zip (pre ++ [x]) =
      (keys.take pre.length).zip pre ++ (keys.drop pre.length).zip [x] := by
    intro x
    rw [← List.zip_append h_take_len, List.take_append_drop]
  -- The drop has exactly 1 element
  have h_drop_one : ∃ k, keys.drop pre.length = [k] := by
    have h_drop_len : (keys.drop pre.length).length = 1 := by simp; omega
    exact match keys.drop pre.length, h_drop_len with | [k], _ => ⟨k, rfl⟩
  obtain ⟨k_last, h_dk⟩ := h_drop_one
  -- Rewrite using fold decomposition
  simp only [LExpr.substFvars, h_zip, List.foldl_append, h_dk, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  -- Goal: substFvar X k_last a →* substFvar X k_last a'
  exact StepStar_substFvar F rf _ k_last a a' h

---------------------------------------------------------------------
-- Helper lemma: for the concreteEval factory case. When concreteEval
-- succeeds on evaluated args, we need to relate the result to what
-- happens with original args via the Step relation.
-- If concreteEval also succeeds on original args, we use eval_fn + IH
-- and need to relate the two results.
-- If concreteEval fails on original args, we need a different strategy.

private theorem eval_StepStar_factory_ceval
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
    (hEnv : ∀ x v, Scopes.toEnv σ.state x = some v →
              LExpr.isCanonicalValue σ.config.factory v)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : σ.config.factory.callOfLFunc e = some (op_expr, args, lfunc))
    (ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono))
    (h_ceval : lfunc.concreteEval = some ceval)
    (e'_ceval : LExpr Tbase.mono)
    (h_ceval_succ : ceval (LExpr.mkApp e.metadata op_expr
        (args.map (fun a => LExpr.eval n σ a))).metadata (args.map (fun a => LExpr.eval n σ a)) = some e'_ceval)
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ e',
        ReflTrans (Step σ.config.factory (Scopes.toEnv σ.state)) e e' ∧
        ValEquiv σ.config.factory (Scopes.toEnv σ.state)
          (LExpr.substFvarsFromState σ e') (LExpr.substFvarsFromState σ (LExpr.eval n σ e))) :
    ∃ (e' : LExpr Tbase.mono),
      ReflTrans (Step σ.config.factory (Scopes.toEnv σ.state)) e e' ∧
      ValEquiv σ.config.factory (Scopes.toEnv σ.state)
        (LExpr.substFvarsFromState σ e') (LExpr.substFvarsFromState σ (LExpr.eval n σ e'_ceval)) := by
  -- Apply IH to e'_ceval: this gives us the RHS equation directly.
  obtain ⟨e'_c, hstep_c, hsubst_c⟩ := ih e'_ceval
  exact ⟨e'_c,
    -- Stepping: e →* e'_c. Composing e →* e'_ceval with e'_ceval →* e'_c.
    -- The first part (e →* e'_ceval) requires stepping each arg to its
    -- evaluated form and then applying eval_fn, which needs the evaluated
    -- args to match. This is left as a separate obligation.
    sorry,
    hsubst_c⟩

---------------------------------------------------------------------
-- Structural lemma: getLFuncCall decomposes e into (op, args), and
-- mkApp reconstructs from (op, args). After eraseMetadata, these
-- are the same structure.

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem eraseMetadata_mkApp
    (m : Tbase.Metadata) (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) :
    (LExpr.mkApp m op args).eraseMetadata =
      LExpr.mkApp () op.eraseMetadata (args.map LExpr.eraseMetadata) := by
  induction args generalizing op with
  | nil => simp [LExpr.mkApp]
  | cons a rest ih =>
    simp only [LExpr.mkApp, List.map]
    exact ih (.app m op a)

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem eraseMetadata_mkApp_congr
    (m1 m2 : Tbase.Metadata) (op : LExpr Tbase.mono)
    (args1 args2 : List (LExpr Tbase.mono))
    (h_args : args1.map LExpr.eraseMetadata = args2.map LExpr.eraseMetadata) :
    (LExpr.mkApp m1 op args1).eraseMetadata =
      (LExpr.mkApp m2 op args2).eraseMetadata := by
  rw [eraseMetadata_mkApp, eraseMetadata_mkApp, h_args]

/-
Structural lemma: getLFuncCall.go decomposes nested apps. If
  getLFuncCall.go e acc = (op, args)
then e rebuilt as mkApp with the args (minus acc) gives back the
original expression, modulo metadata.

More precisely: e.eraseMetadata = mkApp () op.eraseMetadata (args_from_e.map eraseMetadata)
where args = args_from_e ++ acc.
-/
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getLFuncCall_go_eraseMetadata
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (op, args)) :
    LExpr.mkApp () e.eraseMetadata (acc.map LExpr.eraseMetadata) =
      LExpr.mkApp () op.eraseMetadata (args.map LExpr.eraseMetadata) := by
  -- Induction following getLFuncCall.go's recursion structure
  -- go matches: app _ (app _ e' arg1) arg2 | app _ (op m fn ty) arg1 | _
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    -- go recurses: go e' ([arg1, arg2] ++ acc)
    simp only [getLFuncCall.go] at h
    -- The recursive call gives us the same conclusion with e' and extended acc
    have ih := getLFuncCall_go_eraseMetadata e' ([arg1, arg2] ++ acc) op args h
    -- Now relate: mkApp () (app () (app () e'.eM arg1.eM) arg2.eM) (acc.map eM)
    --           = mkApp () e'.eM (([arg1,arg2]++acc).map eM)
    -- Both sides unfold to mkApp () e'.eM [arg1.eM, arg2.eM, ...acc.map eM]
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata] at ih ⊢
    exact ih
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h
    cases h; rfl
  | .app m1 (.const m2 c) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.bvar m2 i) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.fvar m2 x ty) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.abs m2 n ty body) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.quant m2 k n ty tr body) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.ite m2 c t f) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.eq m2 e1 e2) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .const _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .op _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .bvar _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  termination_by e.sizeOf

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getLFuncCall_eraseMetadata_mkApp
    (e : LExpr Tbase.mono) (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono))
    (h : getLFuncCall e = (op, args)) :
    e.eraseMetadata = LExpr.mkApp () op.eraseMetadata (args.map LExpr.eraseMetadata) := by
  unfold getLFuncCall at h
  have h2 := getLFuncCall_go_eraseMetadata e [] op args h
  simp [LExpr.mkApp, List.map] at h2
  exact h2

---------------------------------------------------------------------
-- Helper: substFvars on an .op node is identity (no free vars)

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_op
    (m : Tbase.Metadata) (name : Identifier Tbase.IDMeta)
    (ty : Option LMonoTy)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.op m name ty) sm = LExpr.op m name ty := by
  simp only [LExpr.substFvars]
  induction sm with
  | nil => simp [List.foldl]
  | cons p rest ih => simp [List.foldl, LExpr.substFvar, ih]

---------------------------------------------------------------------
-- Structural lemma: substFvars + eraseMetadata distribute through
-- getLFuncCall's decomposition.

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_getLFuncCall_go_eraseMetadata
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono))
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (op, args)) :
    LExpr.mkApp () (LExpr.substFvars e sm).eraseMetadata
        ((acc.map (LExpr.substFvars · sm)).map LExpr.eraseMetadata) =
      LExpr.mkApp () (LExpr.substFvars op sm).eraseMetadata
        ((args.map (LExpr.substFvars · sm)).map LExpr.eraseMetadata) := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [getLFuncCall.go] at h
    have ih := substFvars_getLFuncCall_go_eraseMetadata e' ([arg1, arg2] ++ acc) op args sm h
    simp only [substFvars_app, LExpr.eraseMetadata, LExpr.replaceMetadata] at ih ⊢
    exact ih
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [substFvars_app, substFvars_op]; rfl
  | .app m1 (.const m2 c) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.bvar m2 i) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.fvar m2 x ty) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.abs m2 n ty body) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.quant m2 k n ty tr body) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.ite m2 c t f) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .app m1 (.eq m2 e1 e2) arg2 =>
    simp only [getLFuncCall.go] at h; cases h; rfl
  | .const _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .op _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .bvar _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; cases h; rfl
  termination_by e.sizeOf

-- Top-level version: if `getLFuncCall e = (op, args)`, then
-- `(substFvars e sm).eraseMetadata = mkApp () (substFvars op sm).eraseMetadata
--   ((args.map (substFvars · sm)).map eraseMetadata)`.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_getLFuncCall_eraseMetadata
    (e : LExpr Tbase.mono) (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono))
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (h : getLFuncCall e = (op, args)) :
    (LExpr.substFvars e sm).eraseMetadata =
      LExpr.mkApp () (LExpr.substFvars op sm).eraseMetadata
        ((args.map (LExpr.substFvars · sm)).map LExpr.eraseMetadata) := by
  unfold getLFuncCall at h
  have h2 := substFvars_getLFuncCall_go_eraseMetadata e [] op args sm h
  simp only [LExpr.mkApp, List.map] at h2
  exact h2

---------------------------------------------------------------------
-- Structural lemma: substFvars distributes through mkApp

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem substFvars_mkApp
    (m : Tbase.Metadata) (op : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) :
    LExpr.substFvars (LExpr.mkApp m op args) sm =
      LExpr.mkApp m (LExpr.substFvars op sm) (args.map (LExpr.substFvars · sm)) := by
  induction args generalizing op with
  | nil => simp [LExpr.mkApp, List.map]
  | cons a rest ih =>
    simp only [LExpr.mkApp, List.map]
    rw [ih]
    congr 1
    exact substFvars_app m op a sm

---------------------------------------------------------------------
-- Helper: callOfLFunc decomposes via getLFuncCall with an .op head.

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem callOfLFunc_getLFuncCall
    {F : @Factory Tbase} {e : LExpr Tbase.mono}
    {op_expr : LExpr Tbase.mono} {args : List (LExpr Tbase.mono)} {lfunc : LFunc Tbase}
    (h : F.callOfLFunc e = some (op_expr, args, lfunc)) :
    getLFuncCall e = (op_expr, args) ∧ ∃ m name ty, op_expr = .op m name ty := by
  -- Follow the pattern from callOfLFunc_smaller
  simp [Factory.callOfLFunc] at h
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h
  cases op' <;> simp at h
  rename_i m_op name_op ty_op
  split at h
  · simp at h
  · split at h
    · simp at h; obtain ⟨rfl, rfl, _⟩ := h; exact ⟨rfl, _, _, _, rfl⟩
    · simp at h

---------------------------------------------------------------------
-- Helpers: step function/args through mkApp structure.
-- These rely on the relaxed reduce_2 (no canonical value check).

-- Step function part through mkApp. Since StepStar_app_fn preserves
-- metadata, this produces exactly mkApp m fn' args.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_mkApp_fn (F : @Factory Tbase) (rf : Env Tbase)
    (fn fn' : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (m : Tbase.Metadata)
    (h : ReflTrans (Step F rf) fn fn') :
    ReflTrans (Step F rf) (LExpr.mkApp m fn args) (LExpr.mkApp m fn' args) := by
  induction args generalizing fn fn' with
  | nil => exact h
  | cons a rest ih =>
    simp only [LExpr.mkApp]
    exact ih (.app m fn a) (.app m fn' a) (StepStar_app_fn F rf fn fn' a m h)

-- Step all args through mkApp. Since StepStar_app_arg preserves metadata,
-- this produces exactly mkApp m fn args'.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_mkApp_args (F : @Factory Tbase) (rf : Env Tbase)
    (fn : LExpr Tbase.mono) (args args' : List (LExpr Tbase.mono))
    (m : Tbase.Metadata)
    (h_len : args.length = args'.length)
    (h_steps : ∀ i (hi : i < args.length),
      ReflTrans (Step F rf) (args.get ⟨i, hi⟩) (args'.get ⟨i, h_len ▸ hi⟩)) :
    ReflTrans (Step F rf) (LExpr.mkApp m fn args) (LExpr.mkApp m fn args') := by
  induction args generalizing fn args' m with
  | nil =>
    cases args' with
    | nil => exact ReflTrans.refl _
    | cons => simp at h_len
  | cons a rest ih =>
    match args', h_len with
    | a' :: rest', h_len =>
      simp only [LExpr.mkApp]
      -- Step a →* a'
      have h_a : ReflTrans (Step F rf) a a' := by
        have := h_steps 0 (by simp)
        simpa using this
      -- Lift a→a' through app: (app m fn a) →* (app m fn a')
      have h_app := StepStar_app_arg F rf fn a a' m h_a
      -- Lift through mkApp(rest): mkApp (app m fn a) rest →* mkApp (app m fn a') rest
      have h_lift := StepStar_mkApp_fn F rf _ _ rest m h_app
      -- IH: step remaining args: mkApp (app m fn a') rest →* mkApp (app m fn a') rest'
      have h_rest_len : rest.length = rest'.length := by simp at h_len; exact h_len
      have h_rest_steps : ∀ i (hi : i < rest.length),
          ReflTrans (Step F rf) (rest.get ⟨i, hi⟩) (rest'.get ⟨i, h_rest_len ▸ hi⟩) := by
        intro i hi
        have := h_steps (i + 1) (by simp; omega)
        simpa using this
      have h_rest := ih (.app m fn a') rest' m h_rest_len h_rest_steps
      -- Compose
      exact ReflTrans_trans h_lift h_rest

---------------------------------------------------------------------
-- Step args within the actual expression structure from getLFuncCall.go.
-- This follows the go recursion, stepping each arg and lifting through
-- the real per-level metadata (not uniform mkApp metadata).

-- getLFuncCall.go always returns (op, inner ++ acc) for some inner list.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getLFuncCall_go_acc_suffix
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (op : LExpr Tbase.mono) (all_args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (op, all_args)) :
    ∃ inner, all_args = inner ++ acc := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [getLFuncCall.go] at h
    obtain ⟨inner', h_inner'⟩ := getLFuncCall_go_acc_suffix e' ([arg1, arg2] ++ acc) op all_args h
    exact ⟨inner' ++ [arg1, arg2], by rw [h_inner']; simp [List.append_assoc]⟩
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[arg1], rfl⟩
  | .app m1 (.const _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .app m1 (.bvar _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .app m1 (.fvar _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .app m1 (.abs _ _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .app m1 (.quant _ _ _ _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .app m1 (.ite _ _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .app m1 (.eq _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .const _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .op _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .bvar _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl⟩
  termination_by e.sizeOf

-- go e acc = (op, inner ++ acc) and go e acc' = (op, inner ++ acc') for the same inner.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getLFuncCall_go_acc_change
    (e : LExpr Tbase.mono) (acc acc' : List (LExpr Tbase.mono))
    (op : LExpr Tbase.mono) (all_args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (op, all_args)) :
    ∃ inner, all_args = inner ++ acc ∧
      getLFuncCall.go e acc' = (op, inner ++ acc') := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [getLFuncCall.go] at h
    obtain ⟨inner', h_eq, h_go'⟩ :=
      getLFuncCall_go_acc_change e' ([arg1, arg2] ++ acc) ([arg1, arg2] ++ acc') op all_args h
    exact ⟨inner' ++ [arg1, arg2], by rw [h_eq]; simp [List.append_assoc],
      by simp only [getLFuncCall.go]; rw [h_go']; simp [List.append_assoc]⟩
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨[arg1], rfl, rfl⟩
  | .app m1 (.const _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .app m1 (.bvar _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .app m1 (.fvar _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .app m1 (.abs _ _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .app m1 (.quant _ _ _ _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .app m1 (.ite _ _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .app m1 (.eq _ _ _) _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .const _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .op _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .bvar _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, rfl⟩
  termination_by e.sizeOf

-- If callOfLFunc succeeds on (.app m e1 e2), replacing e2 with e2' gives
-- the same function with updated args (e2 → e2' at the last position).
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem callOfLFunc_replace_last_arg
    (F : @Factory Tbase) (e1 e2 e2' : LExpr Tbase.mono) (m m' : Tbase.Metadata)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (fn : LFunc Tbase)
    (h : F.callOfLFunc (.app m e1 e2) = some (op, args, fn)) :
    ∃ pre, args = pre ++ [e2] ∧
      F.callOfLFunc (.app m' e1 e2') = some (op, pre ++ [e2'], fn) := by
  -- getLFuncCall decomposes via go, putting e2 in the accumulator.
  -- The go recursion depends only on e1, so replacing e2→e2' preserves op.
  have ⟨h_glfc, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall h
  -- Get the inner prefix and the modified getLFuncCall result
  have h_split : ∃ pre, args = pre ++ [e2] ∧
      getLFuncCall (.app m' e1 e2') = (op, pre ++ [e2']) := by
    unfold getLFuncCall at h_glfc ⊢
    match e1 with
    | .app m1 e1' arg1 =>
      simp only [getLFuncCall.go, List.append_nil] at h_glfc ⊢
      obtain ⟨inner, h_eq, h_go'⟩ :=
        getLFuncCall_go_acc_change e1' [arg1, e2] [arg1, e2'] op args h_glfc
      exact ⟨inner ++ [arg1], by rw [h_eq]; simp [List.append_assoc],
        by rw [h_go']; simp [List.append_assoc]⟩
    | .op m1 fn_name fn_ty =>
      simp only [getLFuncCall.go, List.append_nil] at h_glfc
      obtain ⟨rfl, rfl⟩ := h_glfc; exact ⟨[], rfl, by simp [getLFuncCall.go]⟩
    | .const _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _
    | .ite _ _ _ _ | .eq _ _ _ =>
      simp only [getLFuncCall.go] at h_glfc
      obtain ⟨rfl, _⟩ := h_glfc; simp_all
  obtain ⟨pre, h_args_eq, h_glfc'⟩ := h_split
  refine ⟨pre, h_args_eq, ?_⟩
  -- callOfLFunc = getLFuncCall + match op + factory lookup + arity check.
  -- op and fn are the same; arity is preserved since |pre ++ [e2]| = |pre ++ [e2']|.
  subst h_args_eq; subst h_op_eq
  -- Extract factory lookup and arity check from h
  simp only [Factory.callOfLFunc] at h
  rw [h_glfc] at h; simp only at h
  -- h is now about getFactoryLFunc + arity check on (pre ++ [e2])
  cases h_fac : Factory.getFactoryLFunc F name_op.name with
  | none => simp [h_fac] at h
  | some func =>
    simp only [h_fac] at h
    simp only [Factory.callOfLFunc, h_glfc', h_fac]
    -- Both share the same arity check value (lengths are equal)
    have h_len : (pre ++ [e2']).length = (pre ++ [e2]).length := by simp
    -- Split the arity match in h to extract fn = func
    split at h <;> simp at h
    obtain ⟨_, rfl, rfl⟩ := h
    -- Now rebuild with same arity check for pre ++ [e2']
    rename_i h_arity
    rw [h_len, h_arity]

---------------------------------------------------------------------
-- Helpers for canonical_value_not_step

-- Helper: getFactoryLFunc returns a factory member.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getFactoryLFunc_mem
    (F : @Factory Tbase) (name : String) (func : LFunc Tbase)
    (h : F.getFactoryLFunc name = some func) : func ∈ F := by
  simp only [Factory.getFactoryLFunc] at h
  have h2 : F.toList.find? (fun fn => fn.name.name == name) = some func := by
    rw [Array.find?_toList]; exact h
  exact Array.mem_def.mpr (List.mem_of_find?_eq_some h2)

-- Helper: callOfLFunc result is a factory member.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem callOfLFunc_func_mem
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (func : LFunc Tbase)
    (aPA : Bool)
    (h : F.callOfLFunc e (allowPartialApp := aPA) = some (op, args, func)) :
    func ∈ F := by
  simp only [Factory.callOfLFunc] at h
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h
  cases op' <;> simp at h
  rename_i m_op name_op ty_op
  cases h_gf : F.getFactoryLFunc name_op.name with
  | none => simp [h_gf] at h
  | some func' =>
    simp only [h_gf] at h
    cases aPA <;> simp at h <;> split at h <;> simp at h
    all_goals (obtain ⟨_, _, rfl⟩ := h; exact getFactoryLFunc_mem F _ _ h_gf)

-- callOfLFunc (non-partial) checks args.length == fn.inputs.length.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem callOfLFunc_arity
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (fn : LFunc Tbase)
    (h : F.callOfLFunc e = some (op, args, fn)) :
    args.length = fn.inputs.length := by
  simp only [Factory.callOfLFunc] at h
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h
  cases op' <;> simp at h
  rename_i m_op name_op ty_op
  cases h_gf : F.getFactoryLFunc name_op.name with
  | none => simp [h_gf] at h
  | some func =>
    simp only [h_gf] at h
    split at h
    · -- matchesArg = true: extract the arity and the result
      rename_i h_arity
      simp at h; obtain ⟨_, rfl, rfl⟩ := h
      simp at h_arity; exact h_arity
    · simp at h

-- Helper: if callOfLFunc with partial app returns (op, args, f) with the
-- canonical condition (isConstr || blt), and callOfLFunc with full arity
-- also succeeds, then isConstr must be true.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem callOfLFunc_partial_full_isConstr
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (h_partial : F.callOfLFunc e (allowPartialApp := true) = some (op, args, f))
    (h_cond : (f.isConstr || Nat.blt args.length f.inputs.length) = true)
    (op2 : LExpr Tbase.mono) (args2 : List (LExpr Tbase.mono)) (f2 : LFunc Tbase)
    (h_full : F.callOfLFunc e (allowPartialApp := false) = some (op2, args2, f2)) :
    f2.isConstr = true := by
  simp only [Factory.callOfLFunc] at h_partial h_full
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h_partial h_full
  cases op' <;> simp at h_partial h_full
  rename_i m_op name_op ty_op
  cases h_gf : F.getFactoryLFunc name_op.name with
  | none => simp [h_gf] at h_partial
  | some func' =>
    simp only [h_gf] at h_partial h_full
    -- h_partial is a match on ble, h_full is a match on ==
    split at h_full <;> simp at h_full
    · rename_i h_eq
      split at h_partial <;> simp at h_partial
      · obtain ⟨_, rfl, rfl⟩ := h_partial
        obtain ⟨_, rfl, rfl⟩ := h_full
        -- h_eq: args.length == f.inputs.length, h_cond: isConstr || blt
        simp only [Bool.or_eq_true] at h_cond
        cases h_cond with
        | inl h => exact h
        | inr h =>
          simp [Nat.blt] at h
          simp [Nat.beq_eq] at h_eq
          omega

-- Helper: for e = .app m e1 e2, if callOfLFunc (with any allowPartialApp)
-- succeeds with nonempty args, then e2 is the last arg and thus e2 ∈ args.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem callOfLFunc_app_arg_mem
    (F : @Factory Tbase) (e1 e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (aPA : Bool)
    (h : F.callOfLFunc (.app m e1 e2) (allowPartialApp := aPA) = some (op, args, f)) :
    e2 ∈ args := by
  -- Unfold callOfLFunc to get getLFuncCall result
  unfold Factory.callOfLFunc at h
  cases h_lfc : getLFuncCall (.app m e1 e2) with | mk op' args' =>
  simp only [h_lfc] at h
  -- h is now about matching on op'
  cases op' with
  | op m_op name_op ty_op =>
    -- op' is .op, so callOfLFunc continues
    -- Extract args = args' from h
    simp only [Option.map] at h
    split at h
    · simp at h
    · rename_i func h_func
      split at h
      · rename_i h_arity
        simp at h
        obtain ⟨_, rfl, _⟩ := h
        -- Now: e2 ∈ args', h_lfc : getLFuncCall (.app m e1 e2) = (.op .., args')
        unfold getLFuncCall at h_lfc
        cases e1 with
        | app m2 e1' e1'' =>
          simp only [getLFuncCall.go] at h_lfc
          obtain ⟨inner, h_inner⟩ := getLFuncCall_go_acc_suffix e1' [e1'', e2] _ _ h_lfc
          rw [h_inner]; simp
        | op m2 fn ty =>
          simp only [getLFuncCall.go] at h_lfc
          obtain ⟨_, rfl⟩ := h_lfc; simp
        | const _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | bvar _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | fvar _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | abs _ _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | ite _ _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | eq _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
      · simp at h
  | _ => simp at h

-- Helper: go (.app m e1 e2) acc = go e1 ([e2] ++ acc) when e1 = .app or e1 = .op
-- For other e1, the first component is not .op in either case.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getLFuncCall_go_app_acc
    (e1 e2 : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (op_m : Tbase.mono.base.Metadata)
    (op_n : Identifier Tbase.mono.base.IDMeta)
    (op_t : Option Tbase.mono.TypeType)
    (args : List (LExpr Tbase.mono))
    (m : Tbase.Metadata)
    (h : getLFuncCall.go e1 ([e2] ++ acc) = (LExpr.op op_m op_n op_t, args)) :
    getLFuncCall.go (LExpr.app m e1 e2) acc = (LExpr.op op_m op_n op_t, args) := by
  match e1 with
  | .app m' (.app m'' e' arg0) arg1 =>
    -- go (.app m (.app m' (.app m'' e' arg0) arg1) e2) acc
    --   = go (.app m'' e' arg0) ([arg1, e2] ++ acc)   (first case of go)
    -- go (.app m' (.app m'' e' arg0) arg1) ([e2] ++ acc)
    --   = go e' ([arg0, arg1] ++ [e2] ++ acc)          (first case of go)
    -- We need: go (.app m'' e' arg0) ([arg1, e2] ++ acc) = (.op .., args)
    -- Apply recursively with e1 := e', e2 := arg0, acc := [arg1, e2] ++ acc
    simp only [getLFuncCall.go]
    simp only [getLFuncCall.go] at h
    exact getLFuncCall_go_app_acc e' arg0 ([arg1, e2] ++ acc) op_m op_n op_t args m'' h
  | .app m' (.op m'' fn ty) arg1 =>
    -- go (.app m (.app m' (.op ..) arg1) e2) acc = go (.op ..) ([arg1, e2] ++ acc) = (.op .., [arg1, e2] ++ acc)
    -- go (.app m' (.op ..) arg1) ([e2] ++ acc) = (.op .., [arg1, e2] ++ acc)
    simp only [getLFuncCall.go]
    simp only [getLFuncCall.go] at h
    exact h
  | .app m' (.const _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .app m' (.bvar _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .app m' (.fvar _ _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .app m' (.abs _ _ _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .app m' (.quant _ _ _ _ _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .app m' (.ite _ _ _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .app m' (.eq _ _ _) arg1 =>
    simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .op _ fn ty =>
    simp only [getLFuncCall.go]
    simp only [getLFuncCall.go] at h
    exact h
  | .const _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .bvar _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; simp [Prod.mk.injEq] at h
  termination_by e1.sizeOf

-- Helper: if `.app m e1 e2` is canonical, then `e1` is also canonical.
-- Needed for the `reduce_1` case: stepping the function part of a canonical app.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem isCanonicalValue_app_left
    (F : @Factory Tbase) (m : Tbase.Metadata)
    (e1 e2 : LExpr Tbase.mono)
    (hc : LExpr.isCanonicalValue F (.app m e1 e2) = true) :
    LExpr.isCanonicalValue F e1 = true := by
  -- The .app case of isCanonicalValue goes to the callOfLFunc branch.
  -- Extract the callOfLFunc result from hc.
  unfold LExpr.isCanonicalValue at hc
  split at hc
  · -- callOfLFunc returned some (op, args, f)
    rename_i op args f h_call
    simp only [Bool.and_eq_true] at hc
    obtain ⟨h_cond, h_all⟩ := hc
    -- Unfold callOfLFunc to get getLFuncCall information
    unfold Factory.callOfLFunc at h_call
    cases h_lfc : getLFuncCall (.app m e1 e2) with | mk op' args' =>
    simp only [h_lfc] at h_call
    cases op' with
    | op m_op name_op ty_op =>
      simp only at h_call
      cases h_gf : Factory.getFactoryLFunc F name_op.name with
      | none => simp [h_gf] at h_call
      | some func =>
        simp only [h_gf] at h_call
        split at h_call <;> simp at h_call
        rename_i h_ble
        obtain ⟨rfl, rfl, rfl⟩ := h_call
        -- Now: args = args', f = func
        -- Unfold getLFuncCall to analyze it
        unfold getLFuncCall at h_lfc
        -- Case split on e1
        cases e1 with
        | op m2 fn2 ty2 =>
          -- getLFuncCall.go (.app m (.op ..) e2) [] = (.op .., [e2])
          simp only [getLFuncCall.go] at h_lfc
          obtain ⟨rfl, rfl⟩ := h_lfc
          -- isCanonicalValue F (.op m2 fn2 ty2)
          -- callOfLFunc F (.op ..) true uses same factory function, arity 0 ≤ inputs.length
          -- For .op, isCanonicalValue goes to callOfLFunc branch with 0 args
          -- callOfLFunc F (.op ..) true: getLFuncCall returns (.op .., [])
          -- then getFactoryLFunc succeeds (h_gf), ble 0 inputs.length = true
          -- Result: (isConstr || blt 0 inputs.length) && [].all .. which simplifies
          have h_cv : Factory.callOfLFunc F (.op m_op name_op ty_op) (allowPartialApp := true)
              = some (.op m_op name_op ty_op, [], func) := by
            simp only [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go, h_gf]
            have : Nat.ble 0 func.inputs.length = true := by simp [Nat.ble_eq]
            simp [this]
          unfold LExpr.isCanonicalValue
          -- split on callOfLFunc result
          split
          · -- some case: need (isConstr || blt) && all
            rename_i op' args' f' h_cv2
            rw [h_cv] at h_cv2
            obtain ⟨rfl, rfl, rfl⟩ := h_cv2
            simp only [Bool.and_eq_true, List.length_nil, Bool.or_eq_true]
            refine ⟨?_, ?_⟩
            · -- isConstr or blt 0 inputs.length
              simp only [ite_true] at h_ble
              simp only [List.append_nil, List.length_cons, List.length_nil, Nat.ble_eq] at h_ble
              exact Or.inr (by simp [Nat.blt]; omega)
            · -- [].all ... = true: trivial
              simp
          · -- none case: contradiction with h_cv
            rename_i h_none
            rw [h_cv] at h_none
            simp at h_none
        | app m2 e1' e1'' =>
          -- getLFuncCall.go on (.app m (.app m2 e1' e1'') e2) [] = go e1' [e1'', e2]
          simp only [getLFuncCall.go] at h_lfc
          -- Use acc_change to get go e1' [e1''] result
          obtain ⟨inner, h_eq, h_go_e1''⟩ :=
            getLFuncCall_go_acc_change e1' [e1'', e2] [e1''] (.op m_op name_op ty_op) args' h_lfc
          -- h_eq: args' = inner ++ [e1'', e2]
          -- h_go_e1'': go e1' [e1''] = (.op .., inner ++ [e1''])
          -- Show: callOfLFunc F (.app m2 e1' e1'') true = some (op, inner ++ [e1''], func)
          have h_call_e1 : Factory.callOfLFunc F (.app m2 e1' e1'') (allowPartialApp := true)
              = some (.op m_op name_op ty_op, inner ++ [e1''], func) := by
            simp only [Factory.callOfLFunc]
            -- getLFuncCall (.app m2 e1' e1'') = go (.app m2 e1' e1'') []
            -- go (.app m2 e1' e1'') [] evaluates by case-splitting on e1'
            -- But go e1' [e1''] = (.op .., inner ++ [e1'']) by h_go_e1''
            -- We need getLFuncCall (.app m2 e1' e1'') to give same result
            -- getLFuncCall (.app m2 e1' e1'') = go (.app m2 e1' e1'') []
            -- For .app _ e1' e1'' with e1' being various constructors:
            -- case e1' = .app _ e'' a: go (.app m2 (.app _ e'' a) e1'') [] = go e'' [a, e1'']
            --   and go e1' [e1''] = go (.app _ e'' a) [e1''] = go e'' [a, e1''] (same!)
            -- case e1' = .op ...: both give (.op .., [e1''])
            -- case e1' = other: go (.app m2 other e1'') [] = (.app m2 other e1'', [])
            --   but go other [e1''] = (other, [e1'']) with op not .op -> getLFuncCall gives non-.op head
            --   However h_go_e1'' says go e1' [e1''] = (.op .., ..), so this case can't happen
            -- The key: go (.app m2 e1' e1'') [] and go e1' [e1''] give same (op, args)
            -- when e1' is .app or .op, and when e1' is other, go e1' [e1''] gives (e1', [e1''])
            -- which can't have .op as first component unless e1' is .op
            -- Let's prove getLFuncCall (.app m2 e1' e1'') = (.op .., inner ++ [e1''])
            have h_lfc2 : getLFuncCall (.app m2 e1' e1'') = (.op m_op name_op ty_op, inner ++ [e1'']) := by
              unfold getLFuncCall
              exact getLFuncCall_go_app_acc e1' e1'' [] m_op name_op ty_op (inner ++ [e1'']) m2 (by simpa using h_go_e1'')
            simp only [h_lfc2, h_gf]
            have h_ble2 : Nat.ble (inner.length + 1) func.inputs.length = true := by
              simp only [ite_true] at h_ble
              rw [h_eq] at h_ble
              simp only [Nat.ble_eq] at h_ble ⊢
              simp only [List.length_append, List.length_cons, List.length_nil] at h_ble ⊢
              omega
            simp [h_ble2]
          -- Now use h_call_e1
          unfold LExpr.isCanonicalValue
          split
          · -- some case
            rename_i op' args_inner f' h_cv2
            rw [h_call_e1] at h_cv2
            obtain ⟨rfl, rfl, rfl⟩ := h_cv2
            simp only [Bool.and_eq_true]
            refine ⟨?_, ?_⟩
            · -- Arity/constructor condition
              simp only [Bool.or_eq_true] at h_cond ⊢
              cases h_cond with
              | inl h => exact Or.inl h
              | inr h =>
                right
                simp [Nat.blt] at h ⊢
                rw [h_eq] at h; simp [List.length_append, List.length_cons, List.length_nil] at h ⊢
                omega
            · -- All args (inner ++ [e1'']) are canonical
              -- h_all and the goal both have the attach.map pattern.
              -- The key insight: both are equivalent to List.all (isCanonicalValue F)
              -- Let me try to directly relate them using the membership approach.
              -- First, convert h_all to a plain membership form
              rw [h_eq] at h_all
              -- h_all : ((inner ++ [e1'', e2]).attach.map ...).all id = true
              -- Goal : ((inner ++ [e1'']).attach.map ...).all id = true
              -- Use the fact that List.all on attach.map is equivalent to List.all on the original
              -- after erasing the attach
              have h_all' : (inner ++ [e1'', e2]).all (LExpr.isCanonicalValue F) = true := by
                rw [show (inner ++ [e1'', e2]).all (LExpr.isCanonicalValue F) =
                    ((inner ++ [e1'', e2]).attach.map (fun ⟨x, _⟩ => LExpr.isCanonicalValue F x)).all id
                  from by simp [List.all_map]]
                -- Now need to relate to h_all, which has the `have` inside
                -- The `have` doesn't change the value, so they should be definitionally equal
                exact h_all
              -- Now derive the goal
              suffices (inner ++ [e1'']).all (LExpr.isCanonicalValue F) = true by
                rw [show (inner ++ [e1'']).all (LExpr.isCanonicalValue F) =
                    ((inner ++ [e1'']).attach.map (fun ⟨x, _⟩ => LExpr.isCanonicalValue F x)).all id
                  from by simp [List.all_map]] at this
                exact this
              rw [List.all_eq_true] at h_all' ⊢
              intro x hx
              apply h_all'
              -- x ∈ inner ++ [e1''] implies x ∈ inner ++ [e1'', e2]
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
              rcases hx with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
          · -- none case
            rename_i h_none
            rw [h_call_e1] at h_none
            simp at h_none
        | const _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | bvar _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | fvar _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | abs _ _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | ite _ _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
        | eq _ _ _ => simp only [getLFuncCall.go] at h_lfc; simp [Prod.mk.injEq] at h_lfc
    | _ => simp at h_call
  · -- callOfLFunc returned none: hc = false, contradiction
    simp at hc

-- Helper: extract `isCanonicalValue F x = true` for `x ∈ args` from the
-- `all` condition in `isCanonicalValue`.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem isCanonicalValue_args_all
    (F : @Factory Tbase) (args : List (LExpr Tbase.mono))
    (h_all : args.all (LExpr.isCanonicalValue F) = true)
    (x : LExpr Tbase.mono) (hx : x ∈ args) :
    LExpr.isCanonicalValue F x = true := by
  rw [List.all_eq_true] at h_all
  exact h_all x hx

-- Canonical values have no free variables.
-- This is key for substFvarsFromState idempotency.
-- Placed here (after callOfLFunc helpers) so the app case proof has access to
-- isCanonicalValue_app_left and callOfLFunc_app_arg_mem.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem isCanonicalValue_no_freeVars
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (hc : LExpr.isCanonicalValue F e = true) :
    LExpr.freeVars e = [] := by
  induction e with
  | const => simp [LExpr.freeVars]
  | op => simp [LExpr.freeVars]
  | bvar =>
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | fvar =>
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | abs m name ty body ih =>
    simp [LExpr.freeVars]
    simp only [LExpr.isCanonicalValue] at hc
    simp only [LExpr.closed, LExpr.freeVars] at hc
    cases h : LExpr.freeVars body with
    | nil => rfl
    | cons _ _ => simp [h, List.isEmpty] at hc
  | quant m qk name ty tr body ih1 ih2 =>
    simp only [LExpr.freeVars]
    simp only [LExpr.isCanonicalValue] at hc
    simp only [LExpr.closed, LExpr.freeVars] at hc
    cases h : LExpr.freeVars tr ++ LExpr.freeVars body with
    | nil =>
      have := List.append_eq_nil_iff.mp h
      simp [this.1, this.2]
    | cons _ _ => simp [h, List.isEmpty] at hc
  | app m e1 e2 ih1 ih2 =>
    have h1 := isCanonicalValue_app_left F m e1 e2 hc
    simp only [LExpr.isCanonicalValue] at hc
    split at hc
    · rename_i op args f h_call
      simp only [Bool.and_eq_true] at hc
      simp at hc
      have h_mem := callOfLFunc_app_arg_mem F e1 e2 m op args f _ h_call
      have h2 := hc.2 e2 h_mem
      simp [LExpr.freeVars, ih1 h1, ih2 h2]
    · simp at hc
  | ite =>
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | eq =>
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc

-- Substituting into a canonical value is identity (canonical values have no fvars).
private theorem substFvar_canonical
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (hc : LExpr.isCanonicalValue F e = true)
    (fr : Identifier Tbase.IDMeta) (to : LExpr Tbase.mono) :
    LExpr.substFvar e fr to = e :=
  substFvar_no_freeVars e (isCanonicalValue_no_freeVars F e hc) fr to

-- substFvarsFromState is idempotent when env values are canonical.
private theorem substFvarsFromState_idem
    (σ : LState Tbase) (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (hEnv : ∀ x v, Scopes.toEnv σ.state x = some v →
              LExpr.isCanonicalValue F v = true) :
    LExpr.substFvarsFromState σ (LExpr.substFvarsFromState σ e) =
      LExpr.substFvarsFromState σ e := by
  simp only [LExpr.substFvarsFromState]
  apply substFvars_idem
  -- Need: all values in toSingleMap (including shadowed entries) have empty freeVars.
  -- Current hEnv only covers the first-match (toEnv) values, not shadowed entries.
  -- This requires either: (a) strengthening hEnv to cover all scopes, or
  -- (b) proving substFvars_idem with a weaker "effective values only" condition.
  sorry

-- Canonical values are normal forms: no Step rule can fire on them.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem canonical_value_not_step
    (F : @Factory Tbase) (rf : Env Tbase)
    (e : LExpr Tbase.mono)
    (hWF : FactoryWF F)
    (hc : LExpr.isCanonicalValue F e = true) :
    ∀ e', ¬ Step F rf e e' := by
  -- By structural induction on e
  induction e with
  | const => intro e' h; exact step_const_stuck F rf _ _ h
  | bvar =>
    intro e' hstep; cases hstep with
    | expand_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
  | fvar =>
    intro e' hstep
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | ite =>
    intro e' hstep
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | eq =>
    intro e' hstep
    simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | abs =>
    intro e' hstep; cases hstep with
    | expand_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
  | quant =>
    intro e' hstep; cases hstep with
    | expand_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
  | op =>
    intro e' hstep
    simp [LExpr.isCanonicalValue] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ fn h_call h_body _ =>
      split at hc
      · rename_i op_c args_c f_c h_call_partial
        simp only [Bool.and_eq_true] at hc
        have h_isConstr := callOfLFunc_partial_full_isConstr F _ op_c args_c f_c
          h_call_partial hc.1 _ _ fn h_call
        have h_wf_fn := hWF.lfuncs_wf fn (callOfLFunc_func_mem F _ _ _ fn false h_call)
        have ⟨h_no_body, _⟩ := h_wf_fn.constr_no_eval h_isConstr
        simp [h_no_body] at h_body
      · simp at hc
    | eval_fn _ _ _ _ fn _ h_call h_ceval _ =>
      split at hc
      · rename_i op_c args_c f_c h_call_partial
        simp only [Bool.and_eq_true] at hc
        have h_isConstr := callOfLFunc_partial_full_isConstr F _ op_c args_c f_c
          h_call_partial hc.1 _ _ fn h_call
        have h_wf_fn := hWF.lfuncs_wf fn (callOfLFunc_func_mem F _ _ _ fn false h_call)
        have ⟨_, h_no_ceval⟩ := h_wf_fn.constr_no_eval h_isConstr
        simp [h_no_ceval] at h_ceval
      · simp at hc
  | app m_app e1 e2 ih1 ih2 =>
    intro e' hstep
    simp [LExpr.isCanonicalValue] at hc
    cases hstep with
    | beta _ _ _ hv _ =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
    | reduce_2 _ _ e2' h_step_e2 =>
      split at hc
      · rename_i op args f h_call
        simp only [Bool.and_eq_true] at hc
        have h_mem := callOfLFunc_app_arg_mem F e1 e2 m_app op args f _ h_call
        have h_e2_can := isCanonicalValue_args_all F args hc.2 e2 h_mem
        exact ih2 h_e2_can e2' h_step_e2
      · simp at hc
    | reduce_1 _ e1' _ h_step_e1 =>
      have h_e1_can : LExpr.isCanonicalValue F e1 = true := by
        apply isCanonicalValue_app_left F m_app e1 e2
        simp [LExpr.isCanonicalValue]
        split at hc
        · exact hc
        · simp at hc
      exact ih1 h_e1_can e1' h_step_e1
    | expand_fn _ _ _ _ _ fn h_call h_body _ =>
      split at hc
      · rename_i op_c args_c f_c h_call_partial
        simp only [Bool.and_eq_true] at hc
        have h_isConstr := callOfLFunc_partial_full_isConstr F _ op_c args_c f_c
          h_call_partial hc.1 _ _ fn h_call
        have h_wf_fn := hWF.lfuncs_wf fn (callOfLFunc_func_mem F _ _ _ fn false h_call)
        have ⟨h_no_body, _⟩ := h_wf_fn.constr_no_eval h_isConstr
        simp [h_no_body] at h_body
      · simp at hc
    | eval_fn _ _ _ _ fn _ h_call h_ceval _ =>
      split at hc
      · rename_i op_c args_c f_c h_call_partial
        simp only [Bool.and_eq_true] at hc
        have h_isConstr := callOfLFunc_partial_full_isConstr F _ op_c args_c f_c
          h_call_partial hc.1 _ _ fn h_call
        have h_wf_fn := hWF.lfuncs_wf fn (callOfLFunc_func_mem F _ _ _ fn false h_call)
        have ⟨_, h_no_ceval⟩ := h_wf_fn.constr_no_eval h_isConstr
        simp [h_no_ceval] at h_ceval
      · simp at hc

---------------------------------------------------------------------
-- Confluence helpers

-- Canonicalize.trans was previously stated here but is false — see the note
-- above the Canonicalize definition for the counterexample.

-- If Step F rf a a', then CanonStar F rf (substFvar body x a) (substFvar body x a').
-- Uses CanonStar (not Canonicalize) because base cases (const/op/bvar) and ite/eq
-- don't have Canonicalize constructors. The abs/quant/app cases go through
-- Canonicalize wrapped in CanonStar; ite/eq use StepStar lifted to CanonStar.
theorem CanonStar_substFvar
    {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]
    (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono) (x : Identifier Tbase.IDMeta)
    (a a' : LExpr Tbase.mono)
    (h : Step F rf a a') :
    CanonStar F rf (LExpr.substFvar body x a) (LExpr.substFvar body x a') := by
  induction body with
  | const => simp [LExpr.substFvar]; exact .refl _
  | op => simp [LExpr.substFvar]; exact .refl _
  | bvar => simp [LExpr.substFvar]; exact .refl _
  | fvar m y ty =>
    simp only [LExpr.substFvar]
    split
    · exact .step _ _ _ (.step h) (.refl _)
    · exact .refl _
  | abs m name ty body' ih =>
    simp only [LExpr.substFvar]
    exact CanonStar.abs ih
  | quant m qk name ty tr body' ih_tr ih_body =>
    simp only [LExpr.substFvar]
    exact CanonStar.trans (CanonStar.quant_tr ih_tr) (CanonStar.quant_body ih_body)
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvar]
    exact CanonStar.trans (CanonStar.app_fn ih1) (CanonStar.app_arg ih2)
  | ite m c t f ih1 ih2 ih3 =>
    simp only [LExpr.substFvar]
    exact CanonStar.trans (CanonStar.trans (CanonStar.ite_cond ih1) (CanonStar.ite_then ih2))
                          (CanonStar.ite_else ih3)
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvar]
    exact CanonStar.trans (CanonStar.eq_lhs ih1) (CanonStar.eq_rhs ih2)

-- Multi-step version: if a →* a' (via ReflTrans Step), then
-- CanonStar (substFvar body x a) (substFvar body x a').
-- Works for ALL body constructors (including abs/quant) because
-- CanonStar can go under binders where Step cannot.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem CanonStar_substFvar_star
    {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]
    (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono) (x : Identifier Tbase.IDMeta)
    (a a' : LExpr Tbase.mono)
    (h : ReflTrans (Step F rf) a a') :
    CanonStar F rf (LExpr.substFvar body x a) (LExpr.substFvar body x a') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hab _ ih =>
    exact CanonStar.trans (CanonStar_substFvar F rf body x _ _ hab) ih

---------------------------------------------------------------------
-- Confluence

-- eraseMetadata congruence lemmas for compound expressions.
-- These avoid needing simp/unfold in the diamond/confluence proofs.
-- eraseMetadata congruence lemmas.
-- We use tactic proofs with delta/dsimp to reduce through the let-bindings
-- in LExpr.replaceMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
private theorem eraseMetadata_app_congr
    {m₁ m₂ : Tbase.Metadata} {f₁ f₂ a₁ a₂ : LExpr Tbase.mono}
    (hf : f₁.eraseMetadata = f₂.eraseMetadata)
    (ha : a₁.eraseMetadata = a₂.eraseMetadata) :
    (LExpr.app m₁ f₁ a₁).eraseMetadata = (LExpr.app m₂ f₂ a₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congr (congrArg _ hf) ha

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
private theorem eraseMetadata_ite_congr
    {m₁ m₂ : Tbase.Metadata} {c₁ c₂ t₁ t₂ f₁ f₂ : LExpr Tbase.mono}
    (hc : c₁.eraseMetadata = c₂.eraseMetadata)
    (ht : t₁.eraseMetadata = t₂.eraseMetadata)
    (hf : f₁.eraseMetadata = f₂.eraseMetadata) :
    (LExpr.ite m₁ c₁ t₁ f₁).eraseMetadata = (LExpr.ite m₂ c₂ t₂ f₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]
  exact congr (congr (congrArg _ hc) ht) hf

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
private theorem eraseMetadata_eq_congr
    {m₁ m₂ : Tbase.Metadata} {l₁ l₂ r₁ r₂ : LExpr Tbase.mono}
    (hl : l₁.eraseMetadata = l₂.eraseMetadata)
    (hr : r₁.eraseMetadata = r₂.eraseMetadata) :
    (LExpr.eq m₁ l₁ r₁).eraseMetadata = (LExpr.eq m₂ l₂ r₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congr (congrArg _ hl) hr

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
private theorem eraseMetadata_abs_congr
    {m₁ m₂ : Tbase.Metadata} {n : String}
    {t : Option Tbase.mono.TypeType} {b₁ b₂ : LExpr Tbase.mono}
    (hb : b₁.eraseMetadata = b₂.eraseMetadata) :
    (LExpr.abs m₁ n t b₁).eraseMetadata = (LExpr.abs m₂ n t b₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congrArg _ hb

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
private theorem eraseMetadata_quant_congr
    {m₁ m₂ : Tbase.Metadata} {qk : QuantifierKind} {n : String}
    {ty : Option Tbase.mono.TypeType} {tr₁ tr₂ b₁ b₂ : LExpr Tbase.mono}
    (htr : tr₁.eraseMetadata = tr₂.eraseMetadata)
    (hb : b₁.eraseMetadata = b₂.eraseMetadata) :
    (LExpr.quant m₁ qk n ty tr₁ b₁).eraseMetadata = (LExpr.quant m₂ qk n ty tr₂ b₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congr (congrArg _ htr) hb

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] in
private theorem eraseMetadata_const_congr
    {m₁ m₂ : Tbase.Metadata} {c : LConst} :
    (LExpr.const m₁ c : LExpr Tbase.mono).eraseMetadata = (LExpr.const m₂ c).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]

-- Local diamond property for Step: if e steps to both e₁ and e₂,
-- they can be joined via further stepping (ReflTrans Step) to expressions
-- that agree modulo metadata.
-- Note: With the new Canonicalize (value-only, under binders), the diamond
-- for Step is stated in terms of StepStar rather than Canonicalize, since
-- Step operates at the expression level (not under binders).
theorem Step_diamond
    {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]
    (F : @Factory Tbase) (rf : Env Tbase)
    (hWF : FactoryWF F)
    (hFC : FactorySemConfluent F rf)
    (e e₁ e₂ : LExpr Tbase.mono)
    (h₁ : Step F rf e e₁) (h₂ : Step F rf e e₂) :
    ∃ e₃ e₃', ReflTrans (Step F rf) e₁ e₃ ∧ ReflTrans (Step F rf) e₂ e₃' ∧
      e₃.eraseMetadata = e₃'.eraseMetadata := by
  cases h₁ with
  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = expand_fvar
  -- ═══════════════════════════════════════════════════════════════
  | expand_fvar x₁ e_val₁ hrf₁ =>
    cases h₂ with
    | expand_fvar x₂ e_val₂ hrf₂ =>
      rw [hrf₁] at hrf₂; cases hrf₂
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, rfl⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = beta
  -- ═══════════════════════════════════════════════════════════════
  | @beta m1 m2 name ty e_body v2 eres hv₂ heres =>
    cases h₂ with
    | beta e_body₂ v2₂ eres₂ hv₂' heres₂ =>
      subst heres; subst heres₂
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, rfl⟩
    | reduce_1 e1 e1' e2 h_step =>
      -- e1 = .abs m2 name ty e_body can't step
      cases h_step with
      | expand_fn _ _ _ _ _ _ h_call =>
        simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
      | eval_fn _ _ _ _ _ _ h_call =>
        simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | reduce_2 e1 e2 e2' h_step =>
      exact absurd h_step (canonical_value_not_step F rf v2 hWF hv₂ e2')
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = reduce_2 (step the argument)
  -- ═══════════════════════════════════════════════════════════════
  | @reduce_2 m m' e1 e2 e2' h_step₁ =>
    cases h₂ with
    | beta e_body v2 eres hv₂ heres =>
      exact absurd h_step₁ (canonical_value_not_step F rf e2 hWF hv₂ e2')
    | @reduce_2 _ m2' _ _ e2'' h_step₂ =>
      -- Both step the argument: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC e2 e2' e2'' h_step₁ h_step₂
      exact ⟨.app m' e1 e₃, .app m2' e1 e₃',
             StepStar_app_arg F rf e1 e2' e₃ m' hc₁,
             StepStar_app_arg F rf e1 e2'' e₃' m2' hc₂,
             eraseMetadata_app_congr rfl heq⟩
    | @reduce_1 _ m1' _ e1' _ h_step₂ =>
      -- Independent: one steps fn, other steps arg. Join via one Step on each side.
      exact ⟨.app m' e1' e2', .app m1' e1' e2',
             ReflTrans.step _ _ _ (Step.reduce_1 (m' := m') e1 e1' e2' h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.reduce_2 (m' := m1') e1' e2 e2' h_step₁) (ReflTrans.refl _),
             eraseMetadata_app_congr rfl rfl⟩
    | expand_fn e_full callee fnbody new_body args fn h_call h_body h_new =>
      -- reduce_2 steps e2→e2', expand_fn expands with args including e2.
      -- Join: expand_fn on (.app m' e1 e2') gives substFvars fnbody (keys.zip args'),
      -- and we step from substFvars fnbody (keys.zip args) via StepStar_substFvars.
      obtain ⟨pre, h_args_eq, h_call'⟩ :=
        callOfLFunc_replace_last_arg F e1 e2 e2' m m' callee args fn h_call
      let new_body' := LExpr.substFvars fnbody (fn.inputs.keys.zip (pre ++ [e2']))
      refine ⟨new_body', new_body',
        -- e₁ = .app m' e1 e2' →* new_body' (via expand_fn)
        ReflTrans.step _ _ _ (Step.expand_fn (.app m' e1 e2') callee fnbody
          new_body' (pre ++ [e2']) fn h_call' h_body rfl) (ReflTrans.refl _),
        -- e₂ = new_body →* new_body' (via StepStar_substFvars)
        ?_,
        rfl⟩
      subst h_new; rw [h_args_eq]
      exact StepStar_substFvars_last_arg F rf fnbody fn.inputs.keys pre e2 e2'
        (.step _ _ _ h_step₁ (.refl _))
        (by have := callOfLFunc_arity F _ _ _ _ h_call; simp_all)
    | eval_fn _ callee_r _ args_r fn_r denotefn_r h_call_r h_ceval_r h_res_r =>
      -- h₁ = reduce_2 (e2→e2'), h₂ = eval_fn. Symmetric to eval_fn vs reduce_2.
      obtain ⟨pre, h_args_eq, h_call'⟩ :=
        callOfLFunc_replace_last_arg F e1 e2 e2' _ _ callee_r args_r fn_r h_call_r
      let args' := pre ++ [e2']
      have h_len : args_r.length = args'.length := by simp [h_args_eq, args']
      have h_per_arg : ∀ i (hi₁ : i < args_r.length) (hi₂ : i < args'.length),
          ReflTrans (Step F rf) args_r[i] args'[i] := by
        intro i hi₁ hi₂
        rw [h_args_eq] at hi₁
        simp only [h_args_eq]
        by_cases h : i < pre.length
        · -- i < pre.length: both lists give pre[i] → refl
          change ReflTrans (Step F rf) (pre ++ [e2])[i] (pre ++ [e2'])[i]
          simp [List.getElem_append_left h]; exact .refl _
        · -- i = pre.length: e2 → e2' via h_step₁
          have hi : i = pre.length := by simp at hi₁; omega
          subst hi
          change ReflTrans (Step F rf) (pre ++ [e2])[pre.length] (pre ++ [e2'])[pre.length]
          simp [List.getElem_append_right]; exact .step _ _ _ h_step₁ (.refl _)
      have h_mem := callOfLFunc_func_mem F _ _ _ fn_r false h_call_r
      obtain ⟨result', h_ceval', e₃, e₃', h_s₃, h_s₃', h_eq₃⟩ :=
        hFC.eval_arg_step fn_r h_mem denotefn_r h_ceval_r _ args_r _ h_res_r.symm
          args' h_len h_per_arg
      -- e₁ = .app m' e1 e2' (from reduce_2), e₂ = eval result (from eval_fn)
      -- e₁ →Step (eval_fn on stepped args) result' →* e₃'
      -- e₂ →* e₃
      exact ⟨e₃', e₃,
        .step _ result' _
          (.eval_fn _ callee_r result' args' fn_r denotefn_r h_call' h_ceval_r h_ceval'.symm)
          h_s₃',
        h_s₃, h_eq₃.symm⟩

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = reduce_1 (step the function)
  -- ═══════════════════════════════════════════════════════════════
  | @reduce_1 m m' e1 e1' e2 h_step₁ =>
    cases h₂ with
    | beta e_body v2 eres hv₂ heres =>
      cases h_step₁ with
      | expand_fn _ _ _ _ _ _ h_call =>
        simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
      | eval_fn _ _ _ _ _ _ h_call =>
        simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | @reduce_1 _ m1' _ e1'' _ h_step₂ =>
      -- Both step the function: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC e1 e1' e1'' h_step₁ h_step₂
      exact ⟨.app m' e₃ e2, .app m1' e₃' e2,
             StepStar_app_fn F rf e1' e₃ e2 m' hc₁,
             StepStar_app_fn F rf e1'' e₃' e2 m1' hc₂,
             eraseMetadata_app_congr heq rfl⟩
    | @reduce_2 _ m2' _ _ e2' h_step₂ =>
      -- Independent: one steps fn, other steps arg.
      exact ⟨.app m' e1' e2', .app m2' e1' e2',
             ReflTrans.step _ _ _ (Step.reduce_2 (m' := m') e1' e2 e2' h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.reduce_1 (m' := m2') e1 e1' e2' h_step₁) (ReflTrans.refl _),
             eraseMetadata_app_congr rfl rfl⟩
    | expand_fn e_full callee fnbody new_body args fn h_call h_body h_new =>
      -- expand_fn vs reduce_1: requires callOfLFunc decomposition analysis
      sorry -- requires StepStar_substFvar for the multi-variable case
    | eval_fn e_full callee e_result args fn denotefn h_call h_ceval h_res =>
      -- eval_fn vs reduce_1: concreteEval result is opaque w.r.t. function stepping.
      sorry -- requires concreteEval WF conditions

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = ite_reduce_then
  -- ═══════════════════════════════════════════════════════════════
  | ite_reduce_then _ _ =>
    cases h₂ with
    | ite_reduce_then =>
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, rfl⟩
    | ite_reduce_cond _ econd' _ _ h_step =>
      exact absurd h_step (step_const_stuck F rf _ _)
    | ite_reduce_then_branch _ _ ethen' _ h_step =>
      -- h₁ chose then-branch (ethen), h₂ stepped it to ethen'.
      -- e₁ = ethen. e₂ = .ite m' (.const true) ethen' eelse.
      -- e₁ →* ethen' via h_step. e₂ → ethen' via ite_reduce_then.
      exact ⟨_, _,
             ReflTrans.step _ _ _ h_step (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_then (m := _) (mc := _) ethen' _) (ReflTrans.refl _),
             rfl⟩
    | ite_reduce_else_branch _ _ _ eelse' h_step =>
      -- h₁ chose then-branch (ethen). h₂ stepped else-branch to eelse'.
      -- e₁ = ethen. e₂ = .ite m' (.const true) ethen eelse'.
      -- e₂ → ethen via ite_reduce_then. Both reach ethen.
      exact ⟨_, _,
             ReflTrans.refl _,
             ReflTrans.step _ _ _ (Step.ite_reduce_then (m := _) (mc := _) _ eelse') (ReflTrans.refl _),
             rfl⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = ite_reduce_else
  -- ═══════════════════════════════════════════════════════════════
  | ite_reduce_else _ _ =>
    cases h₂ with
    | ite_reduce_else =>
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, rfl⟩
    | ite_reduce_cond _ econd' _ _ h_step =>
      exact absurd h_step (step_const_stuck F rf _ _)
    | ite_reduce_then_branch _ _ ethen' _ h_step =>
      exact ⟨_, _,
             ReflTrans.refl _,
             ReflTrans.step _ _ _ (Step.ite_reduce_else (m := _) (mc := _) ethen' _) (ReflTrans.refl _),
             rfl⟩
    | ite_reduce_else_branch _ _ _ eelse' h_step =>
      -- h₁ = ite_reduce_else: e₁ = eelse. h₂ stepped eelse to eelse'.
      -- e₁ →* eelse' via h_step. e₂ → eelse' via ite_reduce_else.
      exact ⟨_, _,
             ReflTrans.step _ _ _ h_step (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_else (m := _) (mc := _) _ eelse') (ReflTrans.refl _),
             rfl⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = ite_reduce_cond
  -- ═══════════════════════════════════════════════════════════════
  | @ite_reduce_cond m m' econd econd' ethen eelse h_step₁ =>
    cases h₂ with
    | ite_reduce_then =>
      exact absurd h_step₁ (step_const_stuck F rf _ _)
    | ite_reduce_else =>
      exact absurd h_step₁ (step_const_stuck F rf _ _)
    | @ite_reduce_cond _ m2' _ econd'' _ _ h_step₂ =>
      -- Both step the condition: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC econd econd' econd'' h_step₁ h_step₂
      -- Lift through ite_cond
      obtain ⟨m1'', hss1⟩ := StepStar_ite_cond F rf econd' e₃ ethen eelse m' hc₁
      obtain ⟨m2'', hss2⟩ := StepStar_ite_cond F rf econd'' e₃' ethen eelse m2' hc₂
      exact ⟨.ite m1'' e₃ ethen eelse, .ite m2'' e₃' ethen eelse,
             hss1, hss2,
             eraseMetadata_ite_congr heq rfl rfl⟩
    | @ite_reduce_then_branch _ m2' _ _ ethen' _ h_step₂ =>
      -- Independent: cond steps and then-branch steps. Join via Step on each side.
      exact ⟨.ite m' econd' ethen' eelse, .ite m2' econd' ethen' eelse,
             ReflTrans.step _ _ _ (Step.ite_reduce_then_branch (m' := m') econd' ethen ethen' eelse h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_cond (m' := m2') econd econd' ethen' eelse h_step₁) (ReflTrans.refl _),
             eraseMetadata_ite_congr rfl rfl rfl⟩
    | @ite_reduce_else_branch _ m2' _ _ _ eelse' h_step₂ =>
      exact ⟨.ite m' econd' ethen eelse', .ite m2' econd' ethen eelse',
             ReflTrans.step _ _ _ (Step.ite_reduce_else_branch (m' := m') econd' ethen eelse eelse' h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_cond (m' := m2') econd econd' ethen eelse' h_step₁) (ReflTrans.refl _),
             eraseMetadata_ite_congr rfl rfl rfl⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = ite_reduce_then_branch
  -- ═══════════════════════════════════════════════════════════════
  | @ite_reduce_then_branch m_tb m'_tb econd_tb ethen_tb ethen'_tb eelse_tb h_step₁ =>
    cases h₂ with
    | ite_reduce_then =>
      -- h₂ chose then-branch. h₁ stepped then-branch to ethen'_tb.
      -- e₁ = .ite m'_tb econd_tb ethen'_tb eelse_tb. e₂ = ethen_tb.
      -- e₁ steps via ite_reduce_then to ethen'_tb. e₂ steps to ethen'_tb via h_step₁.
      exact ⟨_, _,
             ReflTrans.step _ _ _ (Step.ite_reduce_then (m := m'_tb) (mc := _) ethen'_tb _) (ReflTrans.refl _),
             ReflTrans.step _ _ _ h_step₁ (ReflTrans.refl _),
             rfl⟩
    | ite_reduce_else =>
      -- h₂ chose else-branch. h₁ stepped then-branch.
      -- e₁ = .ite m'_tb econd_tb ethen'_tb eelse_tb. e₂ = eelse_tb.
      -- e₁ steps via ite_reduce_else to eelse_tb.
      exact ⟨_, _,
             ReflTrans.step _ _ _ (Step.ite_reduce_else (m := m'_tb) (mc := _) ethen'_tb _) (ReflTrans.refl _),
             ReflTrans.refl _,
             rfl⟩
    | @ite_reduce_cond _ m2' _ econd' _ _ h_step₂ =>
      exact ⟨.ite m'_tb econd' ethen'_tb eelse_tb, .ite m2' econd' ethen'_tb eelse_tb,
             ReflTrans.step _ _ _ (Step.ite_reduce_cond (m' := m'_tb) econd_tb econd' ethen'_tb eelse_tb h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_then_branch (m' := m2') econd' ethen_tb ethen'_tb eelse_tb h_step₁) (ReflTrans.refl _),
             eraseMetadata_ite_congr rfl rfl rfl⟩
    | @ite_reduce_then_branch _ m2' _ _ ethen'' _ h_step₂ =>
      -- Both step the then-branch: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC ethen_tb ethen'_tb ethen'' h_step₁ h_step₂
      obtain ⟨m1'', hss1⟩ := StepStar_ite_then F rf econd_tb ethen'_tb e₃ eelse_tb m'_tb hc₁
      obtain ⟨m2'', hss2⟩ := StepStar_ite_then F rf econd_tb ethen'' e₃' eelse_tb m2' hc₂
      exact ⟨.ite m1'' econd_tb e₃ eelse_tb, .ite m2'' econd_tb e₃' eelse_tb,
             hss1, hss2,
             eraseMetadata_ite_congr rfl heq rfl⟩
    | @ite_reduce_else_branch _ m2' _ _ _ eelse' h_step₂ =>
      exact ⟨.ite m'_tb econd_tb ethen'_tb eelse', .ite m2' econd_tb ethen'_tb eelse',
             ReflTrans.step _ _ _ (Step.ite_reduce_else_branch (m' := m'_tb) econd_tb ethen'_tb eelse_tb eelse' h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_then_branch (m' := m2') econd_tb ethen_tb ethen'_tb eelse' h_step₁) (ReflTrans.refl _),
             eraseMetadata_ite_congr rfl rfl rfl⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = ite_reduce_else_branch
  -- ═══════════════════════════════════════════════════════════════
  | @ite_reduce_else_branch m_eb m'_eb econd_eb ethen_eb eelse_eb eelse'_eb h_step₁ =>
    cases h₂ with
    | ite_reduce_then =>
      exact ⟨_, _,
             ReflTrans.step _ _ _ (Step.ite_reduce_then (m := m'_eb) (mc := _) _ eelse'_eb) (ReflTrans.refl _),
             ReflTrans.refl _,
             rfl⟩
    | ite_reduce_else =>
      -- h₂ chose else-branch. h₁ stepped it to eelse'_eb.
      -- e₁ = .ite m'_eb econd_eb ethen_eb eelse'_eb. e₂ = eelse_eb.
      -- e₁ steps via ite_reduce_else to eelse'_eb. e₂ steps to eelse'_eb via h_step₁.
      exact ⟨_, _,
             ReflTrans.step _ _ _ (Step.ite_reduce_else (m := m'_eb) (mc := _) _ eelse'_eb) (ReflTrans.refl _),
             ReflTrans.step _ _ _ h_step₁ (ReflTrans.refl _),
             rfl⟩
    | @ite_reduce_cond _ m2' _ econd' _ _ h_step₂ =>
      exact ⟨.ite m'_eb econd' ethen_eb eelse'_eb, .ite m2' econd' ethen_eb eelse'_eb,
             ReflTrans.step _ _ _ (Step.ite_reduce_cond (m' := m'_eb) econd_eb econd' ethen_eb eelse'_eb h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_else_branch (m' := m2') econd' ethen_eb eelse_eb eelse'_eb h_step₁) (ReflTrans.refl _),
             eraseMetadata_ite_congr rfl rfl rfl⟩
    | @ite_reduce_then_branch _ m2' _ _ ethen' _ h_step₂ =>
      exact ⟨.ite m'_eb econd_eb ethen' eelse'_eb, .ite m2' econd_eb ethen' eelse'_eb,
             ReflTrans.step _ _ _ (Step.ite_reduce_then_branch (m' := m'_eb) econd_eb ethen_eb ethen' eelse'_eb h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.ite_reduce_else_branch (m' := m2') econd_eb ethen' eelse_eb eelse'_eb h_step₁) (ReflTrans.refl _),
             eraseMetadata_ite_congr rfl rfl rfl⟩
    | @ite_reduce_else_branch _ m2' _ _ _ eelse'' h_step₂ =>
      -- Both step the else-branch: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC eelse_eb eelse'_eb eelse'' h_step₁ h_step₂
      obtain ⟨m1'', hss1⟩ := StepStar_ite_else F rf econd_eb ethen_eb eelse'_eb e₃ m'_eb hc₁
      obtain ⟨m2'', hss2⟩ := StepStar_ite_else F rf econd_eb ethen_eb eelse'' e₃' m2' hc₂
      exact ⟨.ite m1'' econd_eb ethen_eb e₃, .ite m2'' econd_eb ethen_eb e₃',
             hss1, hss2,
             eraseMetadata_ite_congr rfl rfl heq⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = eq_reduce_true
  -- ═══════════════════════════════════════════════════════════════
  | @eq_reduce_true m mc v1 v2 hv₁ hv₂ heres =>
    cases h₂ with
    | @eq_reduce_true _ mc' _ _ hv₁' hv₂' heres' =>
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, eraseMetadata_const_congr⟩
    | @eq_reduce_false _ mc' _ _ hv₁' hv₂' heres' _ _ =>
      exfalso; unfold LExpr.eql at heres heres'; split at heres <;> simp_all
    | eq_reduce_lhs _ e1' _ h_step =>
      exact absurd h_step (canonical_value_not_step F rf v1 hWF hv₁ e1')
    | @eq_reduce_rhs _ _ _ _ e2' h_step =>
      exact absurd h_step (canonical_value_not_step F rf v2 hWF hv₂ e2')
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = eq_reduce_false
  -- ═══════════════════════════════════════════════════════════════
  | @eq_reduce_false m mc v1 v2 hv₁ hv₂ heres hcb₁ hcb₂ =>
    cases h₂ with
    | @eq_reduce_true _ mc' _ _ hv₁' hv₂' heres' =>
      exfalso; unfold LExpr.eql at heres heres'; split at heres <;> simp_all
    | @eq_reduce_false _ mc' _ _ hv₁' hv₂' heres' _ _ =>
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, eraseMetadata_const_congr⟩
    | eq_reduce_lhs _ e1' _ h_step =>
      exact absurd h_step (canonical_value_not_step F rf v1 hWF hv₁ e1')
    | @eq_reduce_rhs _ _ _ _ e2' h_step =>
      exact absurd h_step (canonical_value_not_step F rf v2 hWF hv₂ e2')
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = eq_reduce_lhs
  -- ═══════════════════════════════════════════════════════════════
  | @eq_reduce_lhs m m' e1 e1' e2 h_step₁ =>
    cases h₂ with
    | @eq_reduce_true _ mc _ _ hv₁ hv₂ heres =>
      exact absurd h_step₁ (canonical_value_not_step F rf e1 hWF hv₁ e1')
    | @eq_reduce_false _ mc _ _ hv₁ hv₂ heres hcb₁ hcb₂ =>
      exact absurd h_step₁ (canonical_value_not_step F rf e1 hWF hv₁ e1')
    | @eq_reduce_lhs _ m2' _ e1'' _ h_step₂ =>
      -- Both step the LHS: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC e1 e1' e1'' h_step₁ h_step₂
      obtain ⟨m1'', hss1⟩ := StepStar_eq_lhs F rf e1' e₃ e2 m' hc₁
      obtain ⟨m2'', hss2⟩ := StepStar_eq_lhs F rf e1'' e₃' e2 m2' hc₂
      exact ⟨.eq m1'' e₃ e2, .eq m2'' e₃' e2,
             hss1, hss2,
             eraseMetadata_eq_congr heq rfl⟩
    | @eq_reduce_rhs _ m2' _ _ e2' h_step₂ =>
      -- LHS steps e1→e1', RHS steps e2→e2'. Join at (.eq _ e1' e2').
      exact ⟨.eq m' e1' e2', .eq m2' e1' e2',
             ReflTrans.step _ _ _ (Step.eq_reduce_rhs (m' := m') e1' e2 e2' h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.eq_reduce_lhs (m' := m2') e1 e1' e2' h_step₁) (ReflTrans.refl _),
             eraseMetadata_eq_congr rfl rfl⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = eq_reduce_rhs
  -- ═══════════════════════════════════════════════════════════════
  | @eq_reduce_rhs m m' e1 e2 e2' h_step₁ =>
    cases h₂ with
    | @eq_reduce_true _ mc' _ _ hv₁' hv₂ heres =>
      exact absurd h_step₁ (canonical_value_not_step F rf e2 hWF hv₂ e2')
    | @eq_reduce_false _ mc' _ _ hv₁' hv₂ heres hcb₁ hcb₂ =>
      exact absurd h_step₁ (canonical_value_not_step F rf e2 hWF hv₂ e2')
    | eq_reduce_lhs _ e1' _ h_step₂ =>
      -- RHS steps e2→e2', LHS steps e1→e1'. Join at (.eq _ e1' e2').
      exact ⟨.eq m' e1' e2', .eq m' e1' e2',
             ReflTrans.step _ _ _ (Step.eq_reduce_lhs (m' := m') e1 e1' e2' h_step₂) (ReflTrans.refl _),
             ReflTrans.step _ _ _ (Step.eq_reduce_rhs (m' := m') e1' e2 e2' h_step₁) (ReflTrans.refl _),
             rfl⟩
    | @eq_reduce_rhs _ m2' _ _ e2'' h_step₂ =>
      -- Both step the RHS: use IH on the sub-step
      have ⟨e₃, e₃', hc₁, hc₂, heq⟩ := Step_diamond F rf hWF hFC e2 e2' e2'' h_step₁ h_step₂
      obtain ⟨m1'', hss1⟩ := StepStar_eq_rhs F rf e1 e2' e₃ m' hc₁
      obtain ⟨m2'', hss2⟩ := StepStar_eq_rhs F rf e1 e2'' e₃' m2' hc₂
      exact ⟨.eq m1'' e1 e₃, .eq m2'' e1 e₃',
             hss1, hss2,
             eraseMetadata_eq_congr rfl heq⟩
    | expand_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = expand_fn
  -- ═══════════════════════════════════════════════════════════════
  | expand_fn e_full callee₁ fnbody₁ new_body₁ args₁ fn₁ h_call₁ h_body₁ h_new₁ =>
    cases h₂ with
    | expand_fvar =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | beta e_body v2 eres hv₂ heres =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | expand_fn _ callee₂ fnbody₂ new_body₂ args₂ fn₂ h_call₂ h_body₂ h_new₂ =>
      rw [h_call₁] at h_call₂; cases h_call₂
      rw [h_body₁] at h_body₂; cases h_body₂
      subst h_new₁; subst h_new₂
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, rfl⟩
    | eval_fn _ callee₂ e_result args₂ fn₂ denotefn h_call₂ h_ceval₂ h_res₂ =>
      rw [h_call₁] at h_call₂; cases h_call₂
      have h_wf := hWF.lfuncs_wf fn₁ (callOfLFunc_func_mem F _ _ _ fn₁ false h_call₁)
      have h_boc := h_wf.toFuncWF.body_or_concreteEval
      simp [h_body₁, h_ceval₂] at h_boc
    | reduce_1 _ e1' _ h_step =>
      sorry -- requires StepStar_substFvar for the multi-variable case
    | @reduce_2 _ m₂' e1_r e2_r e2' h_step =>
      -- expand_fn (h₁) expands with args including e2_r,
      -- reduce_2 (h₂) steps e2_r→e2'. Symmetric to reduce_2 vs expand_fn.
      obtain ⟨pre, h_args_eq, h_call'⟩ :=
        callOfLFunc_replace_last_arg F e1_r e2_r e2' _ m₂' callee₁ args₁ fn₁ h_call₁
      let new_body' := LExpr.substFvars fnbody₁ (fn₁.inputs.keys.zip (pre ++ [e2']))
      refine ⟨new_body', new_body',
        -- e₁ = new_body₁ →* new_body' (via StepStar_substFvars)
        ?_,
        -- e₂ = .app m₂' e1_r e2' →* new_body' (via expand_fn)
        ReflTrans.step _ _ _ (Step.expand_fn (.app m₂' e1_r e2') callee₁ fnbody₁
          new_body' (pre ++ [e2']) fn₁ h_call' h_body₁ rfl) (ReflTrans.refl _),
        rfl⟩
      subst h_new₁; rw [h_args_eq]
      exact StepStar_substFvars_last_arg F rf fnbody₁ fn₁.inputs.keys pre e2_r e2'
        (.step _ _ _ h_step (.refl _))
        (by have := callOfLFunc_arity F _ _ _ _ h_call₁; simp_all)
    | ite_reduce_then =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_else =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_cond _ _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_then_branch _ _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_else_branch _ _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_true _ _ _ _ _ =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_false _ _ _ _ _ _ _ =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_lhs _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_rhs _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁

  -- ═══════════════════════════════════════════════════════════════
  -- Case: h₁ = eval_fn
  -- ═══════════════════════════════════════════════════════════════
  | eval_fn e_full callee₁ e_result₁ args₁ fn₁ denotefn₁ h_call₁ h_ceval₁ h_res₁ =>
    cases h₂ with
    | expand_fvar =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | beta e_body v2 eres hv₂ heres =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | expand_fn _ callee₂ fnbody₂ new_body₂ args₂ fn₂ h_call₂ h_body₂ h_new₂ =>
      rw [h_call₁] at h_call₂; cases h_call₂
      have h_wf := hWF.lfuncs_wf fn₁ (callOfLFunc_func_mem F _ _ _ fn₁ false h_call₁)
      have h_boc := h_wf.toFuncWF.body_or_concreteEval
      simp [h_body₂, h_ceval₁] at h_boc
    | eval_fn _ callee₂ e_result₂ args₂ fn₂ denotefn₂ h_call₂ h_ceval₂ h_res₂ =>
      rw [h_call₁] at h_call₂; cases h_call₂
      rw [h_ceval₁] at h_ceval₂; cases h_ceval₂
      -- Same function, same args, same denotefn. But metadata m may differ.
      -- Use FactorySemConfluent.eval_metadata_indep to close.
      have h_mem := callOfLFunc_func_mem F _ _ _ fn₁ false h_call₁
      have heq := hFC.eval_metadata_indep fn₁ h_mem denotefn₁ h_ceval₁
        _ _ _ _ _ (h_res₁.symm) (h_res₂.symm)
      exact ⟨_, _, ReflTrans.refl _, ReflTrans.refl _, heq⟩
    | reduce_1 _ e1' _ h_step =>
      sorry -- requires callOfLFunc inner-arg replacement + hFC.eval_arg_step
    | @reduce_2 _ m₂' e1_r e2_r e2' h_step =>
      -- eval_fn (h₁) vs reduce_2 (h₂): last arg stepped e2_r→e2'.
      -- Use callOfLFunc_replace_last_arg to get eval_fn on stepped app.
      -- Then use hFC.eval_arg_step to join results.
      obtain ⟨pre, h_args_eq, h_call'⟩ :=
        callOfLFunc_replace_last_arg F e1_r e2_r e2' _ m₂' callee₁ args₁ fn₁ h_call₁
      let args' := pre ++ [e2']
      have h_len : args₁.length = args'.length := by simp [h_args_eq, args']
      have h_per_arg : ∀ i (hi₁ : i < args₁.length) (hi₂ : i < args'.length),
          ReflTrans (Step F rf) args₁[i] args'[i] := by
        intro i hi₁ hi₂
        rw [h_args_eq] at hi₁
        simp only [h_args_eq]
        by_cases h : i < pre.length
        · change ReflTrans (Step F rf) (pre ++ [e2_r])[i] (pre ++ [e2'])[i]
          simp [List.getElem_append_left h]; exact .refl _
        · have hi : i = pre.length := by simp at hi₁; omega
          subst hi
          change ReflTrans (Step F rf) (pre ++ [e2_r])[pre.length] (pre ++ [e2'])[pre.length]
          simp [List.getElem_append_right]; exact .step _ _ _ h_step (.refl _)
      have h_mem := callOfLFunc_func_mem F _ _ _ fn₁ false h_call₁
      obtain ⟨result', h_ceval', e₃, e₃', h_s₃, h_s₃', h_eq₃⟩ :=
        hFC.eval_arg_step fn₁ h_mem denotefn₁ h_ceval₁ _ args₁ _ h_res₁.symm
          args' h_len h_per_arg
      exact ⟨e₃, e₃', h_s₃,
        .step _ result' _
          (.eval_fn _ callee₁ result' args' fn₁ denotefn₁ h_call' h_ceval₁ h_ceval'.symm)
          h_s₃', h_eq₃⟩
    | ite_reduce_then =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_else =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_cond _ _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_then_branch _ _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | ite_reduce_else_branch _ _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_true _ _ _ _ _ =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_false _ _ _ _ _ _ _ =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_lhs _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
    | eq_reduce_rhs _ _ _ h_step =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call₁
  termination_by e.sizeOf

-- NOTE: Canonicalize_deterministic (previously here) was removed because Step is
-- not deterministic — the same expression can be canonicalized in multiple ways
-- (e.g., Canonicalize.refl vs going deeper). This also invalidated
-- Canonicalize_confluent which depended on it.
--
-- ValEquiv.trans (abs/quant cases) previously used Canonicalize_deterministic
-- to show that two canonicalizations of the same body b₂ agree modulo eM.
-- Without it, these cases need Canonicalize confluence, which itself requires
-- Step confluence (Step_diamond). The abs/quant cases of ValEquiv.trans now
-- use sorry for this specific sub-goal.

---------------------------------------------------------------------
-- ValEquiv properties (proved after helper lemmas are available)

-- Reflexivity: every canonical value is ValEquiv to itself.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem ValEquiv.refl (F : @Factory Tbase) (rf : Env Tbase) (e : LExpr Tbase.mono)
    (hc : LExpr.isCanonicalValue F e = true) :
    ValEquiv F rf e e := by
  induction e with
  | const => exact .const
  | op => exact .op
  | abs => exact .abs hc hc (.refl _) (.refl _) rfl
  | quant => exact .quant hc hc (.refl _) (.refl _) rfl (.refl _) (.refl _) rfl
  | app m e1 e2 ih1 ih2 =>
    have h_e1 := isCanonicalValue_app_left F m e1 e2 hc
    simp [LExpr.isCanonicalValue] at hc
    split at hc
    · rename_i op args f h_call
      simp only [Bool.and_eq_true] at hc
      have h_mem := callOfLFunc_app_arg_mem F e1 e2 m op args f _ h_call
      have h_e2 := isCanonicalValue_args_all F args hc.2 e2 h_mem
      exact .app (by simp [LExpr.isCanonicalValue]; split <;> simp_all) (ih1 h_e1) (ih2 h_e2)
    · simp at hc
  | bvar => simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | fvar => simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | ite => simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | eq => simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc

-- Helper: getLFuncCall.go on ValEquiv-related expressions produces the same op head
-- (modulo metadata) and same-length args.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem getLFuncCall_go_ValEquiv
    (F : @Factory Tbase) (rf : Env Tbase)
    {e₁ e₂ : LExpr Tbase.mono}
    (hv : ValEquiv F rf e₁ e₂)
    (acc₁ acc₂ : List (LExpr Tbase.mono))
    (h_acc_len : acc₁.length = acc₂.length)
    (op_m : Tbase.mono.base.Metadata)
    (op_n : Identifier Tbase.mono.base.IDMeta)
    (op_t : Option Tbase.mono.TypeType)
    (args₁ : List (LExpr Tbase.mono))
    (h_go : getLFuncCall.go e₁ acc₁ = (.op op_m op_n op_t, args₁)) :
    ∃ m₂ args₂,
      getLFuncCall.go e₂ acc₂ = (.op m₂ op_n op_t, args₂) ∧
      args₂.length = args₁.length := by
  suffices h : ∀ n (e₁ e₂ : LExpr Tbase.mono), e₁.sizeOf ≤ n → ValEquiv F rf e₁ e₂ →
    ∀ acc₁ acc₂ args₁, acc₁.length = acc₂.length →
    getLFuncCall.go e₁ acc₁ = (.op op_m op_n op_t, args₁) →
    ∃ m₂ args₂, getLFuncCall.go e₂ acc₂ = (.op m₂ op_n op_t, args₂) ∧
      args₂.length = args₁.length by
    exact h _ e₁ e₂ (Nat.le_refl _) hv acc₁ acc₂ args₁ h_acc_len h_go
  intro n
  induction n with
  | zero =>
    intro e₁ e₂ h_size
    have := LExpr.sizeOf_pos e₁; omega
  | succ n ih =>
    intro e₁ e₂ h_size hv acc₁ acc₂ args₁ h_acc_len h_go
    cases hv with
    | const =>
      simp only [getLFuncCall.go] at h_go
      exact absurd (congrArg Prod.fst h_go) (by simp)
    | op =>
      simp only [getLFuncCall.go] at h_go
      obtain ⟨rfl, rfl⟩ := h_go
      simp only [getLFuncCall.go]
      exact ⟨_, _, rfl, h_acc_len.symm⟩
    | abs =>
      simp only [getLFuncCall.go] at h_go
      exact absurd (congrArg Prod.fst h_go) (by simp)
    | quant =>
      simp only [getLFuncCall.go] at h_go
      exact absurd (congrArg Prod.fst h_go) (by simp)
    | app hc hf ha =>
      cases hf with
      | const =>
        simp only [getLFuncCall.go] at h_go
        exact absurd (congrArg Prod.fst h_go) (by simp)
      | op =>
        simp only [getLFuncCall.go] at h_go
        obtain ⟨rfl, rfl⟩ := h_go
        simp only [getLFuncCall.go]
        exact ⟨_, _, rfl, by simp [h_acc_len]⟩
      | abs _ _ _ _ _ =>
        simp only [getLFuncCall.go] at h_go
        exact absurd (congrArg Prod.fst h_go) (by simp)
      | quant _ _ _ _ _ _ _ _ =>
        simp only [getLFuncCall.go] at h_go
        exact absurd (congrArg Prod.fst h_go) (by simp)
      | app hc' hf' ha' =>
        simp only [getLFuncCall.go] at h_go
        simp only [getLFuncCall.go]
        exact ih _ _ (by simp at h_size ⊢; omega) hf' _ _ _ (by simp [h_acc_len]) h_go

-- Helper: canonical transfer for individual ValEquiv pairs (all cases).
-- This is needed by the getLFuncCall args canonical sub-proof.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem isCanonicalValue_ValEquiv_individual
    (F : @Factory Tbase) (rf : Env Tbase) {e₁ e₂ : LExpr Tbase.mono}
    (hv : ValEquiv F rf e₁ e₂) (hc : LExpr.isCanonicalValue F e₁ = true)
    (ih_app : ∀ (m₁ m₂ : Tbase.Metadata) (f₁ f₂ a₁ a₂ : LExpr Tbase.mono),
      (LExpr.app m₁ f₁ a₁).sizeOf ≤ e₁.sizeOf →
      LExpr.isCanonicalValue F (.app m₁ f₁ a₁) = true →
      ValEquiv F rf f₁ f₂ → ValEquiv F rf a₁ a₂ →
      LExpr.isCanonicalValue F (.app m₂ f₂ a₂) = true) :
    LExpr.isCanonicalValue F e₂ = true := by
  cases hv with
  | const => simp [LExpr.isCanonicalValue]
  | op =>
    simp only [LExpr.isCanonicalValue] at hc ⊢
    split at hc
    · rename_i _ _ _ h₁; split
      · rename_i _ _ _ h₂
        simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h₁ h₂
        split at h₁ <;> split at h₂ <;> simp_all
        split at h₁ <;> split at h₂ <;> simp_all
      · rename_i h₂
        simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h₁ h₂
        split at h₁ <;> split at h₂ <;> simp_all
        split at h₁ <;> split at h₂ <;> simp_all
    · simp at hc
  | abs _ hcv2 _ _ _ => exact hcv2
  | quant _ hcv2 _ _ _ _ _ _ => exact hcv2
  | app hc_guard hf ha =>
    exact ih_app _ _ _ _ _ _ (Nat.le_refl _) hc hf ha

-- If (.app m₁ f₁ a₁) is canonical and ValEquiv F f₁ f₂ and ValEquiv F a₁ a₂,
-- then (.app m₂ f₂ a₂) is also canonical (for any m₂).
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem isCanonicalValue_ValEquiv_app
    (F : @Factory Tbase) (rf : Env Tbase) (m₁ m₂ : Tbase.Metadata)
    (f₁ f₂ a₁ a₂ : LExpr Tbase.mono)
    (hc : LExpr.isCanonicalValue F (.app m₁ f₁ a₁) = true)
    (hf : ValEquiv F rf f₁ f₂)
    (ha : ValEquiv F rf a₁ a₂) :
    LExpr.isCanonicalValue F (.app m₂ f₂ a₂) = true := by
  suffices hsuff : ∀ n (m₁ m₂ : Tbase.Metadata) (f₁ f₂ a₁ a₂ : LExpr Tbase.mono),
    (LExpr.app m₁ f₁ a₁).sizeOf ≤ n →
    LExpr.isCanonicalValue F (.app m₁ f₁ a₁) = true →
    ValEquiv F rf f₁ f₂ → ValEquiv F rf a₁ a₂ →
    LExpr.isCanonicalValue F (.app m₂ f₂ a₂) = true by
    exact hsuff _ m₁ m₂ f₁ f₂ a₁ a₂ (Nat.le_refl _) hc hf ha
  intro n
  induction n with
  | zero =>
    intro m₁' _ f₁' _ a₁' _ h_size
    have := LExpr.sizeOf_pos (LExpr.app m₁' f₁' a₁'); omega
  | succ n ih =>
    intro m₁ m₂ f₁ f₂ a₁ a₂ h_size hc hf ha
    have hc_orig := hc
    simp only [LExpr.isCanonicalValue] at hc
    split at hc
    · rename_i op₁ args₁ func h_call₁
      simp only [Bool.and_eq_true] at hc
      obtain ⟨h_cond₁, h_all₁⟩ := hc
      simp at h_all₁  -- convert from attach.map form to ∀ form
      unfold Factory.callOfLFunc at h_call₁
      cases h_lfc₁ : getLFuncCall (.app m₁ f₁ a₁) with | mk op₁' args₁' =>
      simp only [h_lfc₁] at h_call₁
      cases op₁' with
      | op m_op n_op t_op =>
        cases h_gf : Factory.getFactoryLFunc F n_op.name with
        | none => simp [h_gf] at h_call₁
        | some func' =>
          simp only [h_gf] at h_call₁
          split at h_call₁ <;> simp at h_call₁
          rename_i h_ble
          obtain ⟨rfl, rfl, rfl⟩ := h_call₁
          unfold getLFuncCall at h_lfc₁
          have h_go_ve := getLFuncCall_go_ValEquiv F rf (e₂ := .app m₂ f₂ a₂)
            (ValEquiv.app hc_orig hf ha)
            [] [] rfl m_op n_op t_op args₁' h_lfc₁
          obtain ⟨m₂_op, args₂, h_go₂, h_len₂⟩ := h_go_ve
          -- Prove all args₂ canonical by sub-induction on getLFuncCall spine
          have h_args₂_all : ∀ x ∈ args₂, LExpr.isCanonicalValue F x = true := by
            suffices hsub : ∀ k (e₁ e₂ : LExpr Tbase.mono), e₁.sizeOf ≤ k →
              e₁.sizeOf ≤ n.succ →
              ValEquiv F rf e₁ e₂ →
              ∀ acc₁ acc₂, acc₁.length = acc₂.length →
              (∀ x ∈ acc₂, LExpr.isCanonicalValue F x = true) →
              ∀ args₁', getLFuncCall.go e₁ acc₁ = (.op m_op n_op t_op, args₁') →
              (∀ x ∈ args₁', LExpr.isCanonicalValue F x = true) →
              ∀ m₂' args₂', getLFuncCall.go e₂ acc₂ = (.op m₂' n_op t_op, args₂') →
              ∀ x ∈ args₂', LExpr.isCanonicalValue F x = true by
              exact hsub _ _ _ (Nat.le_refl _) h_size
                (ValEquiv.app hc_orig hf ha)
                [] [] rfl (by simp) args₁' h_lfc₁ h_all₁ m₂_op args₂ h_go₂
            intro k
            induction k with
            | zero => intro e₁ _; have := LExpr.sizeOf_pos e₁; omega
            | succ k ihk =>
              intro e₁ e₂ h_sz h_sz_n hve acc₁ acc₂ h_alen h_acc₂_can
                args₁' h_go₁' h_all₁' m₂' args₂' h_go₂'
              cases hve with
              | const =>
                simp only [getLFuncCall.go] at h_go₁'
                exact absurd (congrArg Prod.fst h_go₁') (by simp)
              | op =>
                simp only [getLFuncCall.go] at h_go₂'
                obtain ⟨rfl, rfl⟩ := h_go₂'; exact h_acc₂_can
              | abs =>
                simp only [getLFuncCall.go] at h_go₁'
                exact absurd (congrArg Prod.fst h_go₁') (by simp)
              | quant =>
                simp only [getLFuncCall.go] at h_go₁'
                exact absurd (congrArg Prod.fst h_go₁') (by simp)
              | app hc_inner hf_inner ha_inner =>
                cases hf_inner with
                | const =>
                  simp only [getLFuncCall.go] at h_go₁'
                  exact absurd (congrArg Prod.fst h_go₁') (by simp)
                | op =>
                  simp only [getLFuncCall.go] at h_go₁' h_go₂'
                  obtain ⟨rfl, rfl⟩ := h_go₁'
                  obtain ⟨rfl, rfl⟩ := h_go₂'
                  intro x hx; simp at hx
                  rcases hx with rfl | hx
                  · exact isCanonicalValue_ValEquiv_individual F rf ha_inner
                      (h_all₁' _ (by simp))
                      (fun m₁' m₂' f₁' f₂' a₁' a₂' h_sz' hc' hf' ha' =>
                        ih m₁' m₂' f₁' f₂' a₁' a₂' (by simp at h_sz_n; omega) hc' hf' ha')
                  · exact h_acc₂_can x hx
                | abs _ _ _ _ _ =>
                  simp only [getLFuncCall.go] at h_go₁'
                  exact absurd (congrArg Prod.fst h_go₁') (by simp)
                | quant _ _ _ _ _ _ _ _ =>
                  simp only [getLFuncCall.go] at h_go₁'
                  exact absurd (congrArg Prod.fst h_go₁') (by simp)
                | app hc_inner2 hf_inner2 ha_inner2 =>
                  simp only [getLFuncCall.go] at h_go₁' h_go₂'
                  -- Inner args b₁ and a₁ are members of args₁'
                  obtain ⟨inner_args, h_inner_eq⟩ := getLFuncCall_go_acc_suffix _ _ _ _ h_go₁'
                  -- Transfer b₁ → b₂ and a₁ → a₂ canonical using outer IH
                  have h_b₂_can := isCanonicalValue_ValEquiv_individual F rf ha_inner2
                    (h_all₁' _ (by rw [h_inner_eq]; simp))
                    (fun m₁' m₂' f₁' f₂' a₁' a₂' h_sz' hc' hf' ha' =>
                      ih m₁' m₂' f₁' f₂' a₁' a₂' (by simp at h_sz_n; omega) hc' hf' ha')
                  have h_a₂_can := isCanonicalValue_ValEquiv_individual F rf ha_inner
                    (h_all₁' _ (by rw [h_inner_eq]; simp))
                    (fun m₁' m₂' f₁' f₂' a₁' a₂' h_sz' hc' hf' ha' =>
                      ih m₁' m₂' f₁' f₂' a₁' a₂' (by simp at h_sz_n; omega) hc' hf' ha')
                  apply ihk _ _ (by simp at h_sz h_sz_n ⊢; omega) (by simp at h_sz_n; omega) hf_inner2
                    _ _ (by simp [h_alen])
                    (fun x hx => ?_)
                    _ h_go₁' h_all₁' _ _ h_go₂'
                  · simp at hx; rcases hx with rfl | rfl | hx
                    · exact h_b₂_can
                    · exact h_a₂_can
                    · exact h_acc₂_can x hx
          -- Build RHS canonical
          simp only [LExpr.isCanonicalValue]
          split
          · rename_i op₂ args₂' func₂ h_call₂
            simp only [Bool.and_eq_true]
            unfold Factory.callOfLFunc at h_call₂
            cases h_lfc₂ : getLFuncCall (.app m₂ f₂ a₂) with | mk op₂' args₂'' =>
            simp only [h_lfc₂] at h_call₂
            unfold getLFuncCall at h_lfc₂
            rw [h_go₂] at h_lfc₂
            obtain ⟨rfl, rfl⟩ := h_lfc₂
            simp only [h_gf] at h_call₂
            split at h_call₂ <;> simp at h_call₂
            obtain ⟨rfl, rfl, rfl⟩ := h_call₂
            refine ⟨by rw [h_len₂]; exact h_cond₁, ?_⟩
            simp; exact h_args₂_all
          · rename_i h_none₂
            unfold Factory.callOfLFunc at h_none₂
            cases h_lfc₂ : getLFuncCall (.app m₂ f₂ a₂) with | mk op₂' args₂'' =>
            simp only [h_lfc₂] at h_none₂
            unfold getLFuncCall at h_lfc₂
            rw [h_go₂] at h_lfc₂
            obtain ⟨rfl, rfl⟩ := h_lfc₂
            simp only [h_gf] at h_none₂
            split at h_none₂
            · simp at h_none₂
            · rename_i h_not_ble; rw [h_len₂] at h_not_ble; simp at h_not_ble; exact absurd h_ble (by simp [h_not_ble])
      | _ => simp at h_call₁
    · simp at hc

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem ValEquiv.symm {F : @Factory Tbase} {rf : Env Tbase} {e₁ e₂ : LExpr Tbase.mono}
    (h : ValEquiv F rf e₁ e₂) :
    ValEquiv F rf e₂ e₁ := by
  induction h with
  | const => exact .const
  | op => exact .op
  | abs hcv1 hcv2 hc1 hc2 heq => exact .abs hcv2 hcv1 hc2 hc1 heq.symm
  | quant hcv1 hcv2 hct1 hct2 heqt hcb1 hcb2 heqb =>
    exact .quant hcv2 hcv1 hct2 hct1 heqt.symm hcb2 hcb1 heqb.symm
  | app hc hf ha ihf iha =>
    exact .app (isCanonicalValue_ValEquiv_app _ _ _ _ _ _ _ _ hc hf ha) ihf iha

-- Transitivity requires confluence of Canonicalize (different canonicalization
-- paths for the middle expression must produce eraseMetadata-equal results).
theorem ValEquiv.trans
    {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]
    {F : @Factory Tbase} {rf : Env Tbase}
    (hWF : FactoryWF F)
    {e₁ e₂ e₃ : LExpr Tbase.mono}
    (h₁ : ValEquiv F rf e₁ e₂) (h₂ : ValEquiv F rf e₂ e₃) :
    ValEquiv F rf e₁ e₃ := by
  induction h₁ generalizing e₃ with
  | const => cases h₂; exact .const
  | op => cases h₂; exact .op
  | abs hc₁ hc₂ cs₁ cs₂ heq₁₂ =>
    cases h₂ with
    | abs hc₂' hc₃ cs₂' cs₃ heq₂₃ =>
      -- cs₁: b₁ →CS→ ?, cs₂: b₂ →CS→ ?, heq₁₂: ?.eM = ?.eM
      -- cs₂': b₂ →CS→ ??, cs₃: b₃ →CS→ ??, heq₂₃: ??.eM = ??.eM
      -- Use cs₁ for b₁ side, cs₃ for b₃ side.
      -- Bridge: heq₁₂ relates cs₁-endpoint to cs₂-endpoint,
      -- heq₂₃ relates cs₂'-endpoint to cs₃-endpoint.
      -- Need CanonStar confluence: cs₂-endpoint.eM = cs₂'-endpoint.eM.
      -- CanonStar confluence: cs₂ and cs₂' both start from b₂, so their
      -- endpoints agree modulo eraseMetadata.
      have h_bridge := heq₁₂.trans (Eq.trans (sorry) heq₂₃)
      exact .abs hc₁ hc₃ cs₁ cs₃ h_bridge
  | quant hc₁ hc₂ ct₁ ct₂ heqt cb₁ cb₂ heqb =>
    cases h₂ with
    | quant hc₂' hc₃ ct₂' ct₃ heqt' cb₂' cb₃ heqb' =>
      have h_bridge_t := heqt.trans (Eq.trans (sorry) heqt')
      have h_bridge_b := heqb.trans (Eq.trans (sorry) heqb')
      exact .quant hc₁ hc₃ ct₁ ct₃ h_bridge_t cb₁ cb₃ h_bridge_b
  | app hc₁ hf₁₂ ha₁₂ ih_f ih_a =>
    -- e₁ = .app m₁ f₁ a₁, e₂ = .app m₂ f₂ a₂
    -- hf₁₂ : ValEquiv F rf f₁ f₂, ha₁₂ : ValEquiv F rf a₁ a₂
    -- ih_f : ∀ e₃, ValEquiv F rf f₂ e₃ → ValEquiv F rf f₁ e₃
    -- ih_a : ∀ e₃, ValEquiv F rf a₂ e₃ → ValEquiv F rf a₁ e₃
    cases h₂ with
    | app hc₂ hf₂₃ ha₂₃ =>
      exact .app hc₁ (ih_f hf₂₃) (ih_a ha₂₃)

---------------------------------------------------------------------

-- mkApp distributes over append.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem mkApp_append
    (m : Tbase.Metadata) (fn : LExpr Tbase.mono)
    (xs ys : List (LExpr Tbase.mono)) :
    LExpr.mkApp m fn (xs ++ ys) = LExpr.mkApp m (LExpr.mkApp m fn xs) ys := by
  induction xs generalizing fn with
  | nil => simp [LExpr.mkApp]
  | cons x rest ih => simp [LExpr.mkApp, ih]

-- Generalized version for any LExprParamsT (needed for erased-metadata expressions).
private theorem mkApp_append_gen {T : LExprParamsT}
    (m : T.base.Metadata) (fn : LExpr T)
    (xs ys : List (LExpr T)) :
    LExpr.mkApp m fn (xs ++ ys) = LExpr.mkApp m (LExpr.mkApp m fn xs) ys := by
  induction xs generalizing fn with
  | nil => simp [LExpr.mkApp]
  | cons x rest ih => simp [LExpr.mkApp, ih]

-- Step all args within the actual expression structure identified by
-- getLFuncCall. The result e' satisfies e'.eM = mkApp () op.eM (args'.map eM).
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_getLFuncCall_args
    {F : @Factory Tbase} {rf : Env Tbase}
    (e : LExpr Tbase.mono) (op : LExpr Tbase.mono)
    (args args' : List (LExpr Tbase.mono))
    (h_get : getLFuncCall e = (op, args))
    (h_len : args.length = args'.length)
    (h_steps : ∀ i (hi : i < args.length),
      ReflTrans (Step F rf) (args.get ⟨i, hi⟩) (args'.get ⟨i, h_len ▸ hi⟩)) :
    ∃ e', ReflTrans (Step F rf) e e' ∧
      e'.eraseMetadata = LExpr.mkApp () op.eraseMetadata
        (args'.map LExpr.eraseMetadata) := by
  unfold getLFuncCall at h_get
  match e with
  | .app m1 (.app m2 e_inner a1) a2 =>
    simp only [getLFuncCall.go] at h_get
    obtain ⟨inner_args, h_split, h_get_inner⟩ :=
      getLFuncCall_go_acc_change e_inner [a1, a2] [] op args h_get
    simp at h_get_inner
    -- args = inner_args ++ [a1, a2], getLFuncCall e_inner = (op, inner_args)
    -- Decompose args' similarly
    have h_ia_len : inner_args.length + 2 = args'.length := by
      rw [← h_len, h_split]; simp
    have h_drop_len : (args'.drop inner_args.length).length = 2 := by simp; omega
    obtain ⟨a1', a2', h_drop⟩ : ∃ a1' a2', args'.drop inner_args.length = [a1', a2'] := by
      match args'.drop inner_args.length, h_drop_len with
      | [x, y], _ => exact ⟨x, y, rfl⟩
    have h_args'_split : args' = args'.take inner_args.length ++ [a1', a2'] := by
      have := (List.take_append_drop inner_args.length args').symm
      rwa [h_drop] at this
    -- IH on e_inner
    have h_ia'_len : inner_args.length = (args'.take inner_args.length).length := by simp; omega
    have h_inner_steps : ∀ i (hi : i < inner_args.length),
        ReflTrans (Step F rf) (inner_args.get ⟨i, hi⟩)
          ((args'.take inner_args.length).get ⟨i, h_ia'_len ▸ hi⟩) := by
      intro i hi
      have h1 := h_steps i (by rw [h_split]; simp; omega)
      simp only [h_split, h_args'_split] at h1
      grind
    obtain ⟨e_inner', h_step_inner, h_eq_inner⟩ :=
      StepStar_getLFuncCall_args e_inner op inner_args (args'.take inner_args.length)
        h_get_inner h_ia'_len h_inner_steps
    -- Step a1 and a2
    have h_args_len : args.length = inner_args.length + 2 := by rw [h_split]; simp
    have h_step_a1 : ReflTrans (Step F rf) a1 a1' := by
      have h1 := h_steps inner_args.length (by omega)
      simp only [h_split, h_args'_split] at h1; grind
    have h_step_a2 : ReflTrans (Step F rf) a2 a2' := by
      have h1 := h_steps (inner_args.length + 1) (by omega)
      simp only [h_split, h_args'_split] at h1; grind
    -- Compose stepping
    have step1 := StepStar_app_fn F rf e_inner e_inner' a1 m2 h_step_inner
    have step2 := StepStar_app_fn F rf _ _ a2 m1 step1
    have step3 := StepStar_app_arg F rf e_inner' a1 a1' m2 h_step_a1
    have step4 := StepStar_app_fn F rf _ _ a2 m1 step3
    have step5 := StepStar_app_arg F rf (.app m2 e_inner' a1') a2 a2' m1 h_step_a2
    refine ⟨.app m1 (.app m2 e_inner' a1') a2',
      ReflTrans_trans (ReflTrans_trans step2 step4) step5, ?_⟩
    -- eraseMetadata equation:
    -- LHS: (app m1 (app m2 e_inner' a1') a2').eM
    --    = app () (app () e_inner'.eM a1'.eM) a2'.eM
    --    = app () (app () (mkApp () op.eM (take.map eM)) a1'.eM) a2'.eM   [by h_eq_inner]
    --    = mkApp () op.eM (take.map eM ++ [a1'.eM, a2'.eM])   [by mkApp_append]
    --    = mkApp () op.eM (args'.map eM)   [by h_args'_split]
    -- RHS: mkApp () op.eM (args'.map eM)   [by eraseMetadata_mkApp]
    show (LExpr.app m1 (.app m2 e_inner' a1') a2').eraseMetadata =
      LExpr.mkApp () op.eraseMetadata (args'.map LExpr.eraseMetadata)
    -- Unfold the LHS to mkApp form
    change LExpr.mkApp () (LExpr.mkApp () e_inner'.eraseMetadata [a1'.eraseMetadata]) [a2'.eraseMetadata] =
      LExpr.mkApp () op.eraseMetadata (args'.map LExpr.eraseMetadata)
    rw [h_eq_inner, ← mkApp_append_gen, ← mkApp_append_gen]
    simp only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc]
    congr 1
    rw [h_args'_split, List.map_append, List.map_cons, List.map_cons, List.map_nil]
    congr 1; grind
  | .app m1 (.op m2 fn ty) a1 =>
    -- Base: args = [a1], step a1 via StepStar_app_arg
    simp only [getLFuncCall.go] at h_get
    obtain ⟨rfl, rfl⟩ := h_get
    match args', h_len with
    | [a1'], _ =>
      have h_a := h_steps 0 (by simp)
      simp at h_a
      exact ⟨.app m1 (.op m2 fn ty) a1', StepStar_app_arg F rf _ _ _ m1 h_a, rfl⟩
  | .app m1 (.const _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .app m1 (.bvar _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .app m1 (.fvar _ _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .app m1 (.abs _ _ _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .app m1 (.quant _ _ _ _ _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .app m1 (.ite _ _ _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .app m1 (.eq _ _ _) _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .const _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .op _ _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .bvar _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  | .eq _ _ _ => simp only [getLFuncCall.go] at h_get; obtain ⟨rfl, rfl⟩ := h_get; match args', h_len with | [], _ => exact ⟨_, ReflTrans.refl _, rfl⟩
  termination_by e.sizeOf

---------------------------------------------------------------------
-- Helper lemma: for the terminal factory case.

private theorem eval_StepStar_factory_terminal
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
    (hEnv : ∀ x v, Scopes.toEnv σ.state x = some v →
              LExpr.isCanonicalValue σ.config.factory v)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : σ.config.factory.callOfLFunc e = some (op_expr, args, lfunc))
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ e',
        ReflTrans (Step σ.config.factory (Scopes.toEnv σ.state)) e e' ∧
        ValEquiv σ.config.factory (Scopes.toEnv σ.state)
          (LExpr.substFvarsFromState σ e') (LExpr.substFvarsFromState σ (LExpr.eval n σ e))) :
    ∃ (e' : LExpr Tbase.mono),
      ReflTrans (Step σ.config.factory (Scopes.toEnv σ.state)) e e' ∧
      ValEquiv σ.config.factory (Scopes.toEnv σ.state)
        (LExpr.substFvarsFromState σ e')
        (LExpr.substFvarsFromState σ
          (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ)))) := by
  obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall h_call
  -- Get stepped args from IH
  let stepped_args := args.map (fun a => (ih a).choose)
  have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
  have h_per_step : ∀ i (hi : i < args.length),
      ReflTrans (Step σ.config.factory (Scopes.toEnv σ.state))
        (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
    intro i hi
    have : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [this]
    exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
  -- Step e to e' by stepping all args within the expression structure
  obtain ⟨e', h_step_e, h_e'_eq⟩ :=
    StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step
  refine ⟨e', h_step_e, ?_⟩
  -- h_e'_eq : e'.eM = mkApp () op_expr.eM (stepped_args.map eM)
  -- Bridge e' to mkApp m op stepped_args via eraseMetadata
  have h_e'_mkApp : e'.eraseMetadata =
      (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata := by
    rw [h_e'_eq, eraseMetadata_mkApp]
  -- The equation follows the same structure as the eraseMetadata proof:
  -- substFvars_eraseMetadata_congr + substFvars_mkApp + per-arg IH.
  -- With ValEquiv, we need ValEquiv congruence through substFvars + mkApp.
  -- The proof is structurally similar to the eraseMetadata version.
  sorry

---------------------------------------------------------------------
-- Main theorem

theorem eval_StepStar
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
    (hEnv : ∀ x v, Scopes.toEnv σ.state x = some v →
              LExpr.isCanonicalValue σ.config.factory v) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
      ValEquiv σ.config.factory (Scopes.toEnv σ.state)
        (LExpr.substFvarsFromState σ e') (LExpr.substFvarsFromState σ (LExpr.eval n σ e)) := by
  unfold StepStar
  induction n generalizing e with
  | zero =>
    exact ⟨e, ReflTrans.refl e, by simp [LExpr.eval]; exact ValEquiv.refl _ _ _ sorry⟩
  | succ n ih =>
    simp only [LExpr.eval]
    split
    · -- isCanonicalValue: eval (n+1) σ e = e.
      rename_i h_canonical
      have h_eval_n : LExpr.eval n σ e = e := by
        cases n with
        | zero => simp [LExpr.eval]
        | succ n' => simp [LExpr.eval, h_canonical]
      obtain ⟨e', hstep, hsubst⟩ := ih e
      exact ⟨e', hstep, by rw [show LExpr.eval n σ e = e from h_eval_n] at hsubst; exact hsubst⟩
    · rename_i h_not_canonical
      split
      · -- callOfLFunc e = some: factory function case
        rename_i op_expr args lfunc h_call
        -- Follow eval's branching: split on inline condition
        split
        · -- Inline case: body.isSome && (inline attr || constrArgAt)
          rename_i h_inline
          have h_body_some : lfunc.body.isSome := by simp_all [Bool.and_eq_true]
          obtain ⟨fnbody, h_body⟩ := Option.isSome_iff_exists.mp h_body_some
          -- Step 1: expand_fn inlines the body with original args
          have h_step : Step σ.config.factory (Scopes.toEnv σ.state) e
              (LExpr.substFvars fnbody (lfunc.inputs.keys.zip args)) :=
            Step.expand_fn e op_expr fnbody _ args lfunc h_call h_body rfl
          -- Step 2: step args within the substituted body to their evaluated forms.
          -- eval pre-evaluates args before substituting; we simulate this on the
          -- StepStar side by stepping each arg occurrence inside the body.
          let eval_args := args.map (LExpr.eval n σ)
          have h_keys_eq : (lfunc.inputs.keys.zip args).map Prod.fst =
              (lfunc.inputs.keys.zip eval_args).map Prod.fst := by
            suffices ∀ (ks : List Tbase.Identifier) (vs₁ vs₂ : List (LExpr Tbase.mono)),
                vs₁.length = vs₂.length →
                (ks.zip vs₁).map Prod.fst = (ks.zip vs₂).map Prod.fst by
              exact this _ _ _ (by simp [eval_args])
            intro ks vs₁ vs₂ hlen
            induction ks generalizing vs₁ vs₂ with
            | nil => simp
            | cons k ks ih =>
              cases vs₁ with
              | nil =>
                have h0 := hlen; simp at h0
                cases vs₂ with
                | nil => simp
                | cons _ _ => simp at h0
              | cons v₁ rest₁ =>
                cases vs₂ with
                | nil => simp at hlen
                | cons v₂ rest₂ =>
                  simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
                  exact ih rest₁ rest₂ (by simp at hlen; exact hlen)
          have h_step_body : ReflTrans (Step σ.config.factory (Scopes.toEnv σ.state))
              (LExpr.substFvars fnbody (lfunc.inputs.keys.zip args))
              (LExpr.substFvars fnbody (lfunc.inputs.keys.zip eval_args)) :=
            StepStar_substFvars σ.config.factory (Scopes.toEnv σ.state) fnbody
              (lfunc.inputs.keys.zip args) (lfunc.inputs.keys.zip eval_args)
              h_keys_eq
              (by -- per-arg: args[i] →* eval n σ args[i]
                  -- This is a stepping-simulates-evaluation property.
                  sorry)
          -- Step 3: apply IH to the body with pre-evaluated args
          obtain ⟨e', hstep', hsubst'⟩ :=
            ih (LExpr.substFvars fnbody (lfunc.inputs.keys.zip eval_args))
          -- Compose: e →Step substFvars body (zip args) →* substFvars body (zip eval_args) →* e'
          refine ⟨e', ReflTrans.step _ _ _ h_step (ReflTrans_trans h_step_body hstep'), ?_⟩
          -- Equation: IH gives ValEquiv for substFvars body (zip eval_args).
          -- eval (n+1) σ e = eval n σ (substFvars (body.get ...) (zip eval_args))
          -- which after rw [h_get] = eval n σ (substFvars fnbody (zip eval_args)).
          -- This matches the IH's eval argument, so hsubst' applies directly.
          have h_get : lfunc.body.get (by simp_all) = fnbody := by
            simp [Option.get_some, h_body]
          rw [h_get]
          exact hsubst'
        · -- Non-inline case
          rename_i h_not_inline
          split
          · -- Canonical args or constrArgAt condition
            rename_i h_canonical_args
            split
            · -- concreteEval = none: terminal, returns mkApp
              rename_i h_no_ceval
              exact eval_StepStar_factory_terminal σ e n hWF hEnv
                op_expr args lfunc h_call ih
            · -- concreteEval = some
              rename_i ceval h_ceval
              split
              · -- ceval succeeds on evaluated args: eval recurses
                rename_i e'_ceval h_ceval_succ
                exact eval_StepStar_factory_ceval σ e n hWF hEnv
                  op_expr args lfunc h_call ceval h_ceval e'_ceval h_ceval_succ ih
              · -- ceval fails: terminal, returns mkApp
                rename_i h_ceval_fail
                exact eval_StepStar_factory_terminal σ e n hWF hEnv
                  op_expr args lfunc h_call ih
          · -- Symbolic args: terminal, returns mkApp
            rename_i h_symbolic
            exact eval_StepStar_factory_terminal σ e n hWF hEnv
              op_expr args lfunc h_call ih
      · -- callOfLFunc e = none: goes through evalCore
        rename_i h_no_call
        unfold LExpr.evalCore
        split
        · -- const: substFvarsFromState preserves const
          rename_i m c
          exact ⟨_, ReflTrans.refl _, by
            simp only [substFvarsFromState_const]; exact ValEquiv.const⟩
        · -- op: substFvarsFromState preserves op
          rename_i m n t
          exact ⟨_, ReflTrans.refl _, by
            simp only [substFvarsFromState_op]; exact ValEquiv.op⟩
        · -- bvar: no ValEquiv constructor for bvar (bvar should not appear in well-formed open terms)
          exact ⟨_, ReflTrans.refl _, ValEquiv.refl _ _ _ sorry⟩
        · -- fvar m x ty
          rename_i m x ty
          cases hfind : σ.state.find? x with
          | none =>
            have hD := Maps_findD_find?_none σ.state x (ty, LExpr.fvar m x ty) hfind
            exact ⟨.fvar m x ty, ReflTrans.refl _, by rw [hD]; exact ValEquiv.refl _ _ _ sorry⟩
          | some val =>
            have henv_x : Scopes.toEnv σ.state x = some val.snd := by
              simp [Scopes.toEnv, hfind]
            have hcanon := hEnv x val.snd henv_x
            have h_eval_val : LExpr.eval n σ val.snd = val.snd := by
              cases n with
              | zero => simp [LExpr.eval]
              | succ n' => simp [LExpr.eval, hcanon]
            obtain ⟨e', hstep', hsubst'⟩ := ih val.snd
            have hD := Maps_findD_find?_some σ.state x (ty, LExpr.fvar m x ty) val hfind
            refine ⟨e', ReflTrans.step _ val.snd _ (Step.expand_fvar x val.snd henv_x) hstep', ?_⟩
            rw [hD]
            rw [show LExpr.eval n σ val.snd = val.snd from h_eval_val] at hsubst'
            exact hsubst'
        · -- abs: eval returns substFvarsFromState σ (.abs ...).
          -- By substFvarsFromState_idem, the double substitution equals single.
          rename_i m_abs name ty body
          refine ⟨_, ReflTrans.refl _, ?_⟩
          rw [substFvarsFromState_idem σ σ.config.factory _ hEnv]
          exact ValEquiv.refl _ _ _ sorry
        · -- quant: same as abs
          rename_i m_q qk name ty tr body
          refine ⟨_, ReflTrans.refl _, ?_⟩
          rw [substFvarsFromState_idem σ σ.config.factory _ hEnv]
          exact ValEquiv.refl _ _ _ sorry
        · sorry -- app: requires nested induction on expression structure
        · sorry -- eq: requires nested induction on expression structure
        · sorry -- ite: requires nested induction on expression structure

end -- public section
end Lambda
