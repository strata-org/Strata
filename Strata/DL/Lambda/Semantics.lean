/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.Scopes
public import Strata.DL.Util.Relations

/-!
  Small-step semantics for `LExpr` and soundness of `LExpr.eval`.

  This file defines a small-step reduction relation `Step` for `LExpr` and
  proves three main theorems about `Step` and `LExpr.eval`:

  - `canonical_value_not_step`: Canonical values are normal forms — no `Step`
    rule can fire on them.

  - `eval_eraseMetadata_invariant`: `LExpr.eval` is invariant under metadata
    changes: expressions that agree up to metadata evaluate to results that
    also agree up to metadata.

  - `eval_StepStar`: `LExpr.eval` is sound with respect to `Step`. For every
    expression `e`, there exists an `e'` reachable from `e` by zero or more
    `Step`s whose `eraseMetadata` equals that of `eval n σ e`.
-/

namespace Lambda

open Std (ToFormat Format format)

public section

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]

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

/-- Beta reduction. The argument `e2` need not be a canonical value;
this relaxation (compared to strict call-by-value) is necessary because `LExpr.eval`
evaluates both sub-expressions before performing substitution and we want the
semantics to be flexible enough to handle partial evaluation. -/
| beta:
  ∀ (e1 e2 eres:LExpr Tbase.mono),
    eres = LExpr.subst (fun _ => e2) e1 →
    Step F rf (.app m1 (.abs m2 name ty e1) e2) eres

/-- Argument evaluation: reduce the argument of an application.
Note: this rule does NOT require the function part to be a canonical value.
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
Note: this rule does NOT require the LHS to be a canonical value. -/
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
    new_body = LExpr.substFvarsLifting (fnbody.applySubst tySubst) (fn.inputs.keys.zip args) →
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
actually has free variables. This preserves `canonical_value_not_step`:
`isCanonicalValue` returns `true` for an abs only when it is *closed*
(`freeVars e = []`), so a canonical abs has no free variables for this rule
to fire on.
-/
| abs_subst_fvars:
  ∀ (body : LExpr Tbase.mono) (σ : LState Tbase) (x : Tbase.Identifier),
    x ∈ (LExpr.freeVars body).map Prod.fst →
    rf = Scopes.toEnv σ.state →
    Step F rf (.abs m name ty body) (.abs m' name ty (LExpr.substFvarsFromState σ body))

/-- Substitute free variables under a quantifier binder (body). Same motivation
as `abs_subst_fvars`. -/
| quant_subst_fvars_body:
  ∀ (tr body : LExpr Tbase.mono) (σ : LState Tbase) (x : Tbase.Identifier),
    x ∈ (LExpr.freeVars body).map Prod.fst →
    rf = Scopes.toEnv σ.state →
    Step F rf (.quant m qk name ty tr body) (.quant m' qk name ty tr (LExpr.substFvarsFromState σ body))

/-- Substitute free variables in the trigger of a quantifier. Same motivation
as `abs_subst_fvars`. -/
| quant_subst_fvars_trigger:
  ∀ (tr body : LExpr Tbase.mono) (σ : LState Tbase) (x : Tbase.Identifier),
    x ∈ (LExpr.freeVars tr).map Prod.fst →
    rf = Scopes.toEnv σ.state →
    Step F rf (.quant m qk name ty tr body) (.quant m' qk name ty (LExpr.substFvarsFromState σ tr) body)

omit [DecidableEq Tbase.Metadata] in
theorem step_const_stuck:
  ∀ (F:@Factory Tbase) r x e,
  ¬ Step F r (.const m x) e := by
  intros
  intro H
  contradiction

omit [DecidableEq Tbase.Metadata] in
-- If e is stuck for Step, then ReflTrans (Step) e e' implies e = e'.
theorem ReflTrans_stuck {e e' : LExpr Tbase.mono}
    (h : ReflTrans (Step F rf) e e')
    (h_stuck : ∀ e'', ¬ Step F rf e e'') :
    e = e' := by
  cases h with
  | refl => rfl
  | step _ b _ hab _ => exact absurd hab (h_stuck b)

-- canonical_value_not_step is proved after the helper lemmas below.

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
@[expose] def StepStar (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop :=
  ReflTrans (Step F rf)

---------------------------------------------------------------------

omit [DecidableEq Tbase.Metadata] in
theorem StepStar_app_fn (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf e1 e1') :
    StepStar F rf (.app m e1 e2) (.app m e1' e2) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.app m y e2) _
      (Step.reduce_1 (m' := m) x y e2 hxy) ih

omit [DecidableEq Tbase.Metadata] in
theorem StepStar_app_arg (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e2 e2' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf e2 e2') :
    StepStar F rf (.app m e1 e2) (.app m e1 e2') := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.app m e1 y) _
      (Step.reduce_2 (m' := m) e1 x y hxy) ih

---------------------------------------------------------------------

/--
Structural equality modulo metadata. An internal decomposition tool equivalent to
`e₁.eraseMetadata = e₂.eraseMetadata`, but stated as an inductive for pattern-matching
ergonomics in proofs. Not part of the public API.
-/
private inductive EMEquiv : LExpr Tbase.mono → LExpr Tbase.mono → Prop where
| const : EMEquiv (.const m₁ c) (.const m₂ c)
| op : EMEquiv (.op m₁ n t) (.op m₂ n t)
| bvar : EMEquiv (.bvar m₁ i) (.bvar m₂ i)
| fvar : EMEquiv (.fvar m₁ x ty) (.fvar m₂ x ty)
| abs : EMEquiv b₁ b₂ → EMEquiv (.abs m₁ n t b₁) (.abs m₂ n t b₂)
| quant : EMEquiv t₁ t₂ → EMEquiv b₁ b₂ →
    EMEquiv (.quant m₁ qk n ty t₁ b₁) (.quant m₂ qk n ty t₂ b₂)
| app : EMEquiv f₁ f₂ → EMEquiv a₁ a₂ → EMEquiv (.app m₁ f₁ a₁) (.app m₂ f₂ a₂)
| ite : EMEquiv c₁ c₂ → EMEquiv t₁ t₂ → EMEquiv e₁ e₂ →
    EMEquiv (.ite m₁ c₁ t₁ e₁) (.ite m₂ c₂ t₂ e₂)
| eq : EMEquiv l₁ l₂ → EMEquiv r₁ r₂ → EMEquiv (.eq m₁ l₁ r₁) (.eq m₂ l₂ r₂)

-- EMEquiv implies same eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem EMEquiv.eraseMetadata_eq
    {e₁ e₂ : LExpr Tbase.mono} (h : EMEquiv e₁ e₂) :
    e₁.eraseMetadata = e₂.eraseMetadata := by
  induction h with
  | const | op | bvar | fvar => rfl
  | abs _ ih => simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact congrArg _ ih
  | quant _ _ iht ihb =>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact congr (congrArg _ iht) ihb
  | app _ _ ihf iha =>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact congr (congrArg _ ihf) iha
  | ite _ _ _ ihc iht ihe =>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congr (congrArg _ ihc) iht) ihe
  | eq _ _ ihl ihr =>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact congr (congrArg _ ihl) ihr

-- Converse: same eraseMetadata implies EMEquiv.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem EMEquiv.of_eraseMetadata_eq
    (e₁ e₂ : LExpr Tbase.mono) (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    EMEquiv e₁ e₂ := by
  induction e₁ generalizing e₂ with
  | const m c =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> (first | injection h; subst_vars; exact .const | contradiction)
  | op m n t =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> (first | injection h; subst_vars; exact .op | contradiction)
  | bvar m i =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> (first | injection h; subst_vars; exact .bvar | contradiction)
  | fvar m x ty =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> (first | injection h; subst_vars; exact .fvar | contradiction)
  | abs m n t b ih =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i _ n₂ t₂ b₂; injection h; subst_vars
    exact .abs (ih b₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | quant m qk n ty tr b iht ihb =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i _ qk₂ n₂ ty₂ tr₂ b₂; injection h; subst_vars
    exact .quant (iht tr₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
                 (ihb b₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | app m f a ihf iha =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i _ f₂ a₂; injection h
    exact .app (ihf f₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
               (iha a₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | ite m c t f ihc iht ihf =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i _ c₂ t₂ f₂; injection h
    exact .ite (ihc c₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
               (iht t₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
               (ihf f₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
  | eq m l r ihl ihr =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i _ l₂ r₂; injection h
    exact .eq (ihl l₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))
              (ihr r₂ (by delta LExpr.eraseMetadata LExpr.replaceMetadata; assumption))


---------------------------------------------------------------------

-- Public theorem: more general version of substK_eraseMetadata_congr with different
-- substitution functions (uses EMEquiv for structural induction).
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
theorem substK_eraseMetadata_congr₂
    (e₁ : LExpr Tbase.mono) (e₂ : LExpr Tbase.mono) (k : Nat)
    (s₁ s₂ : Tbase.Metadata → LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (h_s : ∀ m₁ m₂, (s₁ m₁).eraseMetadata = (s₂ m₂).eraseMetadata) :
    (LExpr.substK k s₁ e₁).eraseMetadata = (LExpr.substK k s₂ e₂).eraseMetadata := by
  have hv := EMEquiv.of_eraseMetadata_eq _ _ h_eM
  suffices h : ∀ (e₁ e₂ : LExpr Tbase.mono) (k : Nat),
      EMEquiv e₁ e₂ →
      EMEquiv
        (LExpr.substK k s₁ e₁) (LExpr.substK k s₂ e₂) by
    exact (h e₁ e₂ k hv).eraseMetadata_eq
  intro e₁ e₂ k hv
  induction hv generalizing k with
  | const => exact .const
  | op => exact .op
  | bvar =>
    simp only [LExpr.substK]
    split
    · exact EMEquiv.of_eraseMetadata_eq _ _ (h_s _ _)
    · exact .bvar
  | fvar => exact .fvar
  | abs _ ih => simp only [LExpr.substK]; exact .abs (ih (k+1))
  | quant _ _ ihtr ihb => simp only [LExpr.substK]; exact .quant (ihtr (k+1)) (ihb (k+1))
  | app _ _ ihf iha => simp only [LExpr.substK]; exact .app (ihf k) (iha k)
  | ite _ _ _ ihc iht ihf => simp only [LExpr.substK]; exact .ite (ihc k) (iht k) (ihf k)
  | eq _ _ ihl ihr => simp only [LExpr.substK]; exact .eq (ihl k) (ihr k)

---------------------------------------------------------------------

-- Metadata-preserving ite/eq congruence lemmas (the existing StepStar_ite_*
-- return ∃ m', but we need metadata preserved for substFvar composition).

omit [DecidableEq Tbase.Metadata] in
private theorem StepStar_ite_cond_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c c' t f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf c c') :
    StepStar F rf (.ite m c t f) (.ite m c' t f) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m y t f) _
      (Step.ite_reduce_cond (m' := m) x y t f hxy) ih

omit [DecidableEq Tbase.Metadata] in
private theorem StepStar_ite_then_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c t t' f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf t t') :
    StepStar F rf (.ite m c t f) (.ite m c t' f) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m c y f) _
      (Step.ite_reduce_then_branch (m' := m) c x y f hxy) ih

omit [DecidableEq Tbase.Metadata] in
private theorem StepStar_ite_else_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c t f f' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf f f') :
    StepStar F rf (.ite m c t f) (.ite m c t f') := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m c t y) _
      (Step.ite_reduce_else_branch (m' := m) c t x y hxy) ih

omit [DecidableEq Tbase.Metadata] in
private theorem StepStar_eq_lhs_pres (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf e1 e1') :
    StepStar F rf (.eq m e1 e2) (.eq m e1' e2) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.eq m y e2) _
      (Step.eq_reduce_lhs (m' := m) x y e2 hxy) ih

omit [DecidableEq Tbase.Metadata] in
private theorem StepStar_eq_rhs_pres (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e2 e2' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf e2 e2') :
    StepStar F rf (.eq m e1 e2) (.eq m e1 e2') := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.eq m e1 y) _
      (Step.eq_reduce_rhs (m' := m) e1 x y hxy) ih

---------------------------------------------------------------------
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in

/-
Structural lemma: getLFuncCall.go decomposes nested apps. If
  getLFuncCall.go e acc = (op, args)
then e rebuilt as mkApp with the args (minus acc) gives back the
original expression, modulo metadata.

More precisely: e.eraseMetadata = mkApp () op.eraseMetadata (args_from_e.map eraseMetadata)
where args = args_from_e ++ acc.
-/
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
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


---------------------------------------------------------------------

-- getLFuncCall.go commutes with mkApp for "op-headed" expressions.
-- An expression is op-headed if it's .op or .app _ (op-headed) _.
-- For such expressions, getLFuncCall.go (mkApp m e rest) acc = getLFuncCall.go e (rest ++ acc).
private inductive OpHeaded {T : LExprParamsT} : LExpr T → Prop where
  | op : ∀ m name ty, OpHeaded (.op m name ty)
  | app : ∀ m e a, OpHeaded e → OpHeaded (.app m e a)

-- Helper: for OpHeaded e, getLFuncCall.go (.app m e c) acc = getLFuncCall.go e (c :: acc)
-- This is the "one-step peeling" property.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_go_app_opHeaded
    (m : Tbase.Metadata) (e c : LExpr Tbase.mono)
    (he : OpHeaded e)
    (acc : List (LExpr Tbase.mono)) :
    getLFuncCall.go (.app m e c) acc = getLFuncCall.go e (c :: acc) := by
  induction he generalizing m c acc with
  | op m' name ty => simp [getLFuncCall.go]
  | app m₁ e' a he_inner ih =>
    simp only [getLFuncCall.go]
    exact (ih m₁ a (c :: acc)).symm

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_go_mkApp_opHeaded
    (m : Tbase.Metadata) (e : LExpr Tbase.mono)
    (he : OpHeaded e)
    (rest acc : List (LExpr Tbase.mono)) :
    getLFuncCall.go (LExpr.mkApp m e rest) acc = getLFuncCall.go e (rest ++ acc) := by
  induction rest generalizing e he acc with
  | nil => simp [LExpr.mkApp]
  | cons c rest' ih =>
    simp only [LExpr.mkApp]
    have he' : OpHeaded (.app m e c) := .app m e c he
    rw [ih (.app m e c) he' acc, getLFuncCall_go_app_opHeaded m e c he]
    simp [List.cons_append]

-- getLFuncCall.go on mkApp with .op head
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_go_mkApp_op
    (m_app : Tbase.Metadata) (m_op : Tbase.Metadata)
    (name : Identifier Tbase.IDMeta) (ty : Option LMonoTy)
    (args acc : List (LExpr Tbase.mono)) :
    getLFuncCall.go (LExpr.mkApp m_app (LExpr.op m_op name ty) args) acc =
      (LExpr.op m_op name ty, args ++ acc) := by
  rw [getLFuncCall_go_mkApp_opHeaded m_app _ (.op m_op name ty) args acc]
  simp [getLFuncCall.go]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_mkApp_op
    (m_app : Tbase.Metadata) (m_op : Tbase.Metadata)
    (name : Identifier Tbase.IDMeta) (ty : Option LMonoTy)
    (args : List (LExpr Tbase.mono)) :
    getLFuncCall (LExpr.mkApp m_app (LExpr.op m_op name ty) args) =
      (LExpr.op m_op name ty, args) := by
  simp only [getLFuncCall]
  have h := getLFuncCall_go_mkApp_op m_app m_op name ty args []
  simp at h; exact h

-- callOfLFunc on mkApp returns the same lfunc when the head is .op with
-- the same factory entry and matching arity.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem callOfLFunc_mkApp_op
    (F : @Factory Tbase) (m_app : Tbase.Metadata)
    (op_expr : LExpr Tbase.mono) (args args' : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_op : ∃ m name ty, op_expr = .op m name ty)
    (h_call : F.callOfLFunc (LExpr.mkApp m_app op_expr args) = some (op_expr, args, lfunc))
    (h_len : args'.length = args.length) :
    F.callOfLFunc (LExpr.mkApp m_app op_expr args') = some (op_expr, args', lfunc) := by
  obtain ⟨m_op, name, ty, rfl⟩ := h_op
  simp only [Factory.callOfLFunc, getLFuncCall_mkApp_op] at h_call ⊢
  cases h_gf : F[name.name]? with
  | none => simp [h_gf] at h_call
  | some func =>
    simp only [h_gf] at h_call ⊢
    split at h_call
    · simp at h_call; obtain ⟨rfl, rfl⟩ := h_call
      rw [show args'.length = args.length from h_len]
      simp_all
    · simp at h_call

---------------------------------------------------------------------
-- Structural lemma: substFvars + eraseMetadata distribute through
-- getLFuncCall's decomposition.

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [Inhabited Tbase.IDMeta] in
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
    simp only [LExpr.substFvars_app, LExpr.eraseMetadata, LExpr.replaceMetadata] at ih ⊢
    exact ih
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [LExpr.substFvars_app, LExpr.substFvars_op']; rfl
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


---------------------------------------------------------------------
-- Structural lemma: getLFuncCall.go commutes with substFvars when the head is .op
-- (which is the case whenever callOfLFunc succeeds)

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_go_substFvars
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (m_op : Tbase.Metadata) (name_op : Identifier Tbase.IDMeta)
    (ty_op : Option LMonoTy)
    (args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (LExpr.op m_op name_op ty_op, args)) :
    getLFuncCall.go (LExpr.substFvars e sm) (acc.map (LExpr.substFvars · sm)) =
      (LExpr.op m_op name_op ty_op, args.map (LExpr.substFvars · sm)) := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [getLFuncCall.go] at h
    have ih := getLFuncCall_go_substFvars e' ([arg1, arg2] ++ acc) sm m_op name_op ty_op args h
    simp only [LExpr.substFvars_app, getLFuncCall.go, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    exact ih
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h_op, rfl⟩ := h
    simp only [LExpr.op.injEq] at h_op
    obtain ⟨rfl, rfl, rfl⟩ := h_op
    simp only [LExpr.substFvars_app, LExpr.substFvars_op', getLFuncCall.go, List.map_append, List.map]
  | .app m1 (.const m2 c) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.bvar m2 i) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.fvar m2 x ty) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.abs m2 n ty body) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.quant m2 k n ty tr body) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.ite m2 c t f) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.eq m2 e1 e2) arg2 =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .const _ _ =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .op m n t =>
    simp only [getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h_op, rfl⟩ := h
    simp only [LExpr.op.injEq] at h_op
    obtain ⟨rfl, rfl, rfl⟩ := h_op
    simp [LExpr.substFvars_op', getLFuncCall.go]
  | .bvar _ _ => simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .fvar _ _ _ => simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .abs _ _ _ _ => simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .ite _ _ _ _ => simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .eq _ _ _ => simp only [getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  termination_by e.sizeOf


---------------------------------------------------------------------
-- Helper: callOfLFunc decomposes via getLFuncCall with an .op head.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem callOfLFunc_getLFuncCall_op
    {F : @Factory Tbase} {e : LExpr Tbase.mono}
    {op_expr : LExpr Tbase.mono} {args : List (LExpr Tbase.mono)} {lfunc : LFunc Tbase}
    (h : F.callOfLFunc e = some (op_expr, args, lfunc)) :
    getLFuncCall e = (op_expr, args) ∧ ∃ m name ty, op_expr = .op m name ty :=
  ⟨callOfLFunc_getLFuncCall h, Factory.callOfLFunc_getElem? h |>.elim fun m ⟨name, ty, h_eq, _⟩ => ⟨m, name, ty, h_eq⟩⟩

---------------------------------------------------------------------
-- Step args within the actual expression structure from getLFuncCall.go.
-- This follows the go recursion, stepping each arg and lifting through
-- the real per-level metadata (not uniform mkApp metadata).

-- getLFuncCall.go always returns (op, inner ++ acc) for some inner list.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
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
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
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


---------------------------------------------------------------------
-- Helpers for canonical_value_not_step

-- Helper: if callOfLFunc with partial app returns (op, args, f) with the
-- canonical condition (isConstr || blt), and callOfLFunc with full arity
-- also succeeds, then isConstr must be true.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
/-- If `callOfLFunc` succeeds with both `allowPartialApp := true` and `false`,
the results are identical — both variants use the same `getLFuncCall` and the
same factory lookup; the only difference is the arity check. -/
private theorem callOfLFunc_partial_implies_full
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (h_partial : F.callOfLFunc e (allowPartialApp := true) = some (op, args, f))
    (h_full_some : (F.callOfLFunc e (allowPartialApp := false)).isSome) :
    F.callOfLFunc e (allowPartialApp := false) = some (op, args, f) := by
  simp only [Factory.callOfLFunc] at h_partial h_full_some ⊢
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h_partial h_full_some ⊢
  cases op' <;> simp at h_partial h_full_some ⊢
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h_partial
  | some func' =>
    simp only [h_gf] at h_partial h_full_some ⊢
    split at h_full_some <;> simp at h_full_some
    split at h_partial <;> simp at h_partial
    obtain ⟨_, rfl, rfl⟩ := h_partial
    simp_all

omit [DecidableEq
  Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
/-- When `callOfLFunc` with partial app returns a function satisfying
`isConstr || blt args.length f.inputs.length`, and `callOfLFunc` with full
arity also succeeds, the function must be a constructor.
This is because full arity implies `args.length = f.inputs.length`,
making `blt` false, so `isConstr` must hold. -/
private theorem callOfLFunc_partial_full_isConstr
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (h_partial : F.callOfLFunc e (allowPartialApp := true) = some (op, args, f))
    (h_cond : (f.isConstr || Nat.blt args.length f.inputs.length) = true)
    (op2 : LExpr Tbase.mono) (args2 : List (LExpr Tbase.mono)) (f2 : LFunc Tbase)
    (h_full : F.callOfLFunc e (allowPartialApp := false) = some (op2, args2, f2)) :
    f2.isConstr = true := by
  -- Both variants return the same result
  have h_same := callOfLFunc_partial_implies_full F e op args f h_partial (by simp [h_full])
  rw [h_same] at h_full; obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h_full
  simp only [Factory.callOfLFunc] at h_partial
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h_partial
  cases op' <;> simp at h_partial
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h_partial
  | some func' =>
    simp only [h_gf] at h_partial
    split at h_partial <;> simp at h_partial
    obtain ⟨_, _, rfl⟩ := h_partial
    rename_i h_ble
    -- From h_same (full arity), args.length = f.inputs.length
    simp only [Factory.callOfLFunc, h_lfc, h_gf] at h_same
    split at h_same <;> simp at h_same
    rename_i h_eq; simp at h_eq
    simp only [Bool.or_eq_true] at h_cond
    cases h_cond with
    | inl h => exact h
    | inr h => simp [Nat.blt] at h; rw [← h_eq, h_ble] at h; omega

-- Helper: for e = .app m e1 e2, if callOfLFunc (with any allowPartialApp)
-- succeeds with nonempty args, then e2 is the last arg and thus e2 ∈ args.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
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
    simp only [] at h
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

-- Specialized corollary of getLFuncCall_go_app_opHeaded: if `go e1 ([e2] ++ acc)`
-- returns an `.op` result, then `go (.app m e1 e2) acc` returns the same result.
-- The cleaner equation `go (.app m e c) acc = go e (c :: acc)` is
-- `getLFuncCall_go_app_opHeaded`, which requires `OpHeaded e` explicitly.
-- This variant avoids the need to construct `OpHeaded e1` at the call site.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
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
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
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
      cases h_gf : F[name_op.name]? with
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
            have h_ble : Nat.ble 0 func.inputs.length = true := by simp [Nat.ble_eq]
            simp [h_ble]
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
          simp only [getLFuncCall.go] at h_lfc
          obtain ⟨inner, h_eq, h_go_e1''⟩ :=
            getLFuncCall_go_acc_change e1' [e1'', e2] [e1''] (.op m_op name_op ty_op) args' h_lfc
          have h_call_e1 : Factory.callOfLFunc F (.app m2 e1' e1'') (allowPartialApp := true)
              = some (.op m_op name_op ty_op, inner ++ [e1''], func) := by
            simp only [Factory.callOfLFunc]
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
            · rw [h_eq] at h_all
              have h_all' : (inner ++ [e1'', e2]).all (LExpr.isCanonicalValue F) = true := by
                rw [show (inner ++ [e1'', e2]).all (LExpr.isCanonicalValue F) =
                    ((inner ++ [e1'', e2]).attach.map (fun ⟨x, _⟩ => LExpr.isCanonicalValue F x)).all id
                  from by simp [List.all_map]]
                exact h_all
              -- Now derive the goal
              suffices h_suff : (inner ++ [e1'']).all (LExpr.isCanonicalValue F) = true by
                rw [show (inner ++ [e1'']).all (LExpr.isCanonicalValue F) =
                    ((inner ++ [e1'']).attach.map (fun ⟨x, _⟩ => LExpr.isCanonicalValue F x)).all id
                  from by simp [List.all_map]] at h_suff
                exact h_suff
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
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem isCanonicalValue_args_all
    (F : @Factory Tbase) (args : List (LExpr Tbase.mono))
    (h_all : args.all (LExpr.isCanonicalValue F) = true)
    (x : LExpr Tbase.mono) (hx : x ∈ args) :
    LExpr.isCanonicalValue F x = true := by
  rw [List.all_eq_true] at h_all
  exact h_all x hx

-- Canonical values are normal forms: no Step rule can fire on them.
omit [DecidableEq Tbase.Metadata] in
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
    | expand_fn _ _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
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
  | abs _ _ _ body ih_body =>
    intro e' hstep
    -- Canonical abs is closed → freeVars body = []
    simp [LExpr.isCanonicalValue] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | abs_subst_fvars _ _ _ h_fv _ =>
      -- freeVars body = [] (from closed), so x ∉ freeVars body → contradiction
      have h_fvs : LExpr.freeVars body = [] := by
        simp [LExpr.closed, List.isEmpty_iff] at hc; exact hc
      simp [h_fvs] at h_fv
  | quant _ _ _ _ tr body ih_tr ih_body =>
    intro e' hstep
    simp [LExpr.isCanonicalValue] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | quant_subst_fvars_body _ _ _ _ h_fv _ =>
      simp [LExpr.closed, LExpr.freeVars, List.isEmpty_iff] at hc
      simp [hc.2] at h_fv
    | quant_subst_fvars_trigger _ _ _ _ h_fv _ =>
      simp [LExpr.closed, LExpr.freeVars, List.isEmpty_iff] at hc
      simp [hc.1] at h_fv
  | op =>
    intro e' hstep
    simp [LExpr.isCanonicalValue] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ fn _ h_call h_body _ _ =>
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
    | beta _ _ _ =>
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
    | expand_fn _ _ _ _ _ fn _ h_call h_body _ _ =>
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

-- eraseMetadata congruence lemmas for compound expressions.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem eraseMetadata_app_congr
    {m₁ m₂ : Tbase.Metadata} {f₁ f₂ a₁ a₂ : LExpr Tbase.mono}
    (hf : f₁.eraseMetadata = f₂.eraseMetadata)
    (ha : a₁.eraseMetadata = a₂.eraseMetadata) :
    (LExpr.app m₁ f₁ a₁).eraseMetadata = (LExpr.app m₂ f₂ a₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congr (congrArg _ hf) ha

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem eraseMetadata_ite_congr
    {m₁ m₂ : Tbase.Metadata} {c₁ c₂ t₁ t₂ f₁ f₂ : LExpr Tbase.mono}
    (hc : c₁.eraseMetadata = c₂.eraseMetadata)
    (ht : t₁.eraseMetadata = t₂.eraseMetadata)
    (hf : f₁.eraseMetadata = f₂.eraseMetadata) :
    (LExpr.ite m₁ c₁ t₁ f₁).eraseMetadata = (LExpr.ite m₂ c₂ t₂ f₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]
  exact congr (congr (congrArg _ hc) ht) hf

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem eraseMetadata_eq_congr
    {m₁ m₂ : Tbase.Metadata} {l₁ l₂ r₁ r₂ : LExpr Tbase.mono}
    (hl : l₁.eraseMetadata = l₂.eraseMetadata)
    (hr : r₁.eraseMetadata = r₂.eraseMetadata) :
    (LExpr.eq m₁ l₁ r₁).eraseMetadata = (LExpr.eq m₂ l₂ r₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congr (congrArg _ hl) hr

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem eraseMetadata_abs_congr
    {m₁ m₂ : Tbase.Metadata} {n : String}
    {t : Option Tbase.mono.TypeType} {b₁ b₂ : LExpr Tbase.mono}
    (hb : b₁.eraseMetadata = b₂.eraseMetadata) :
    (LExpr.abs m₁ n t b₁).eraseMetadata = (LExpr.abs m₂ n t b₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congrArg _ hb

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem eraseMetadata_quant_congr
    {m₁ m₂ : Tbase.Metadata} {qk : QuantifierKind} {n : String}
    {ty : Option Tbase.mono.TypeType} {tr₁ tr₂ b₁ b₂ : LExpr Tbase.mono}
    (htr : tr₁.eraseMetadata = tr₂.eraseMetadata)
    (hb : b₁.eraseMetadata = b₂.eraseMetadata) :
    (LExpr.quant m₁ qk n ty tr₁ b₁).eraseMetadata = (LExpr.quant m₂ qk n ty tr₂ b₂).eraseMetadata := by
  delta LExpr.eraseMetadata; dsimp only [LExpr.replaceMetadata]; exact congr (congrArg _ htr) hb

---------------------------------------------------------------------

-- Step all args within the actual expression structure identified by
-- getLFuncCall. The result e' satisfies e'.eM = mkApp () op.eM (args'.map eM).
 omit [DecidableEq Tbase.Metadata] in
private theorem StepStar_getLFuncCall_args
    {F : @Factory Tbase} {rf : Env Tbase}
    (e : LExpr Tbase.mono) (op : LExpr Tbase.mono)
    (args args' : List (LExpr Tbase.mono))
    (h_get : getLFuncCall e = (op, args))
    (h_len : args.length = args'.length)
    (h_steps : ∀ i (hi : i < args.length),
      StepStar F rf (args.get ⟨i, hi⟩) (args'.get ⟨i, h_len ▸ hi⟩)) :
    ∃ e', StepStar F rf e e' ∧
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
      have h_take_drop := (List.take_append_drop inner_args.length args').symm
      rwa [h_drop] at h_take_drop
    -- IH on e_inner
    have h_ia'_len : inner_args.length = (args'.take inner_args.length).length := by simp; omega
    have h_inner_steps : ∀ i (hi : i < inner_args.length),
        StepStar F rf (inner_args.get ⟨i, hi⟩)
          ((args'.take inner_args.length).get ⟨i, h_ia'_len ▸ hi⟩) := by
      intro i hi
      have h1 := h_steps i (by rw [h_split]; simp; omega)
      simp only [] at h1
      grind
    obtain ⟨e_inner', h_step_inner, h_eq_inner⟩ :=
      StepStar_getLFuncCall_args e_inner op inner_args (args'.take inner_args.length)
        h_get_inner h_ia'_len h_inner_steps
    -- Step a1 and a2
    have h_args_len : args.length = inner_args.length + 2 := by rw [h_split]; simp
    have h_step_a1 : StepStar F rf a1 a1' := by
      have h1 := h_steps inner_args.length (by omega)
      simp only [] at h1; grind
    have h_step_a2 : StepStar F rf a2 a2' := by
      have h1 := h_steps (inner_args.length + 1) (by omega)
      simp only [] at h1; grind
    -- Compose stepping
    have step1 := StepStar_app_fn F rf e_inner e_inner' a1 m2 h_step_inner
    have step2 := StepStar_app_fn F rf _ _ a2 m1 step1
    have step3 := StepStar_app_arg F rf e_inner' a1 a1' m2 h_step_a1
    have step4 := StepStar_app_fn F rf _ _ a2 m1 step3
    have step5 := StepStar_app_arg F rf (.app m2 e_inner' a1') a2 a2' m1 h_step_a2
    refine ⟨.app m1 (.app m2 e_inner' a1') a2',
      ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ step2 step4) step5, ?_⟩
    show (LExpr.app m1 (.app m2 e_inner' a1') a2').eraseMetadata =
      LExpr.mkApp () op.eraseMetadata (args'.map LExpr.eraseMetadata)
    -- Unfold the LHS to mkApp form
    change LExpr.mkApp () (LExpr.mkApp () e_inner'.eraseMetadata [a1'.eraseMetadata]) [a2'.eraseMetadata] =
      LExpr.mkApp () op.eraseMetadata (args'.map LExpr.eraseMetadata)
    rw [h_eq_inner, ← LExpr.mkApp_append, ← LExpr.mkApp_append]
    simp only [List.cons_append, List.nil_append]
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

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem eval_StepStar_factory_terminal
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : σ.config.factory.callOfLFunc e = some (op_expr, args, lfunc))
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ (e' : LExpr Tbase.mono),
        StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
        e'.eraseMetadata = (LExpr.eval n σ e).eraseMetadata) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
      e'.eraseMetadata =
        (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ))).eraseMetadata := by
  obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall_op h_call
  -- Per-arg IH: e'_i is what arg_i steps to, with e'_i.eraseMetadata = (eval arg_i).eraseMetadata
  let stepped_args := args.map (fun a => (ih a).choose)
  have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
  have h_per_step : ∀ i (hi : i < args.length),
      StepStar σ.config.factory (Scopes.toEnv σ.state)
        (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
  -- Per-arg eraseMetadata eq: e'_i.eraseMetadata = (eval arg_i).eraseMetadata
  have h_per_eM : ∀ i (hi : i < args.length),
      (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩).eraseMetadata =
        (LExpr.eval n σ (args.get ⟨i, hi⟩)).eraseMetadata := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.2
  -- Step e to e' via StepStar_getLFuncCall_args
  obtain ⟨e', h_step_e, h_e'_eq⟩ :=
    StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step
  refine ⟨e', h_step_e, ?_⟩
  -- e'.eraseMetadata = (mkApp m op (args.map eval)).eraseMetadata via eraseMetadata
  -- e'.eM = (mkApp m op stepped_args).eM = (mkApp m op (args.map eval)).eM
  have hA : e'.eraseMetadata = (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata := by
    rw [h_e'_eq, LExpr.eraseMetadata_mkApp]
  have hB : (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata =
      (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ))).eraseMetadata := by
    rw [LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp]
    congr 1
    have h_len_eq : stepped_args.length = (args.map (LExpr.eval n σ)).length := by simp [stepped_args]
    apply List.ext_getElem (by simp [h_len_eq])
    intro i hi1 hi2
    simp only [List.getElem_map]
    have hi_args : i < args.length := by simp [stepped_args] at hi1; exact hi1
    exact h_per_eM i hi_args
  rw [hA, hB]

---------------------------------------------------------------------
-- getLFuncCall.go is eraseMetadata-invariant: if e₁.eM = e₂.eM and acc₁.map eM = acc₂.map eM,
-- then getLFuncCall.go e₁ acc₁ and getLFuncCall.go e₂ acc₂ produce results with the same eM.
set_option maxHeartbeats 800000 in
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_go_eraseMetadata_congr
    (e₁ e₂ : LExpr Tbase.mono) (acc₁ acc₂ : List (LExpr Tbase.mono))
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (h_acc : acc₁.map LExpr.eraseMetadata = acc₂.map LExpr.eraseMetadata) :
    let r₁ := getLFuncCall.go e₁ acc₁
    let r₂ := getLFuncCall.go e₂ acc₂
    r₁.fst.eraseMetadata = r₂.fst.eraseMetadata ∧
    r₁.snd.map LExpr.eraseMetadata = r₂.snd.map LExpr.eraseMetadata := by
  -- Use EMEquiv to decompose eraseMetadata equality structurally
  have hv := EMEquiv.of_eraseMetadata_eq _ _ h_eM
  -- We do induction on the expression structure following getLFuncCall.go
  -- The key case is .app, which recurses on the inner function
  match e₁, e₂, hv with
  | .const _ _, .const _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .op _ _ _, .op _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .bvar _ _, .bvar _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .fvar _ _ _, .fvar _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .abs _ _ _ _, .abs _ _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .quant _ _ _ _ _ _, .quant _ _ _ _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .ite _ _ _ _, .ite _ _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .eq _ _ _, .eq _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
  | .app m₁ a₁ b₁, .app m₂ a₂ b₂, EMEquiv.app hv_a hv_b =>
    -- Case split on a₁/a₂ to follow getLFuncCall.go's pattern match
    match a₁, a₂, hv_a with
    | .app ma₁ inner₁ arg₁₁, .app ma₂ inner₂ arg₂₁, EMEquiv.app hv_inner hv_arg =>
      simp only [getLFuncCall.go]
      exact getLFuncCall_go_eraseMetadata_congr inner₁ inner₂ _ _
        hv_inner.eraseMetadata_eq
        (by simp [List.map, hv_arg.eraseMetadata_eq, hv_b.eraseMetadata_eq, h_acc])
    | .op _ _ _, .op _ _ _, hv_op =>
      simp only [getLFuncCall.go]
      exact ⟨hv_op.eraseMetadata_eq, by simp [hv_b.eraseMetadata_eq, h_acc]⟩
    | .const _ _, .const _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
    | .bvar _ _, .bvar _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
    | .fvar _ _ _, .fvar _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
    | .abs _ _ _ _, .abs _ _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
    | .quant _ _ _ _ _ _, .quant _ _ _ _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
    | .ite _ _ _ _, .ite _ _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩
    | .eq _ _ _, .eq _ _ _, _ => simp only [getLFuncCall.go]; exact ⟨h_eM, h_acc⟩

-- getLFuncCall is eraseMetadata-invariant (wrapper around go)
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem getLFuncCall_eraseMetadata_congr
    (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    (getLFuncCall e₁).fst.eraseMetadata = (getLFuncCall e₂).fst.eraseMetadata ∧
    (getLFuncCall e₁).snd.map LExpr.eraseMetadata = (getLFuncCall e₂).snd.map LExpr.eraseMetadata := by
  unfold getLFuncCall
  exact getLFuncCall_go_eraseMetadata_congr e₁ e₂ [] [] h_eM rfl

-- callOfLFunc is eraseMetadata-invariant
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem callOfLFunc_eraseMetadata_congr
    (F : @Factory Tbase) (e₁ e₂ : LExpr Tbase.mono) (aPA : Bool)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    match F.callOfLFunc e₁ (allowPartialApp := aPA), F.callOfLFunc e₂ (allowPartialApp := aPA) with
    | some (op₁, args₁, f₁), some (op₂, args₂, f₂) =>
        f₁ = f₂ ∧ args₁.map LExpr.eraseMetadata = args₂.map LExpr.eraseMetadata
        ∧ op₁.eraseMetadata = op₂.eraseMetadata
    | none, none => True
    | _, _ => False := by
  have ⟨h_op, h_args⟩ := getLFuncCall_eraseMetadata_congr e₁ e₂ h_eM
  simp only [Factory.callOfLFunc]
  cases h_glfc₁ : getLFuncCall e₁ with | mk op₁ args₁ =>
  cases h_glfc₂ : getLFuncCall e₂ with | mk op₂ args₂ =>
  rw [h_glfc₁, h_glfc₂] at h_op h_args
  simp at h_op h_args
  -- Now case split on op₁, op₂
  match op₁, op₂, h_op with
  | .op m₁ name₁ ty₁, .op m₂ name₂ ty₂, h_op =>
    -- Extract name and type equality from eraseMetadata equality of .op nodes
    have hv_op := EMEquiv.of_eraseMetadata_eq _ _ h_op
    -- EMEquiv.op unifies name₁=name₂ and ty₁=ty₂
    match hv_op with
    | .op =>
      simp only []
      -- Same factory lookup (name₁ = name₂ now)
      cases F[name₁.name]? with
      | none => trivial
      | some func =>
        simp only
        -- Same arity check since args have same length (from same eraseMetadata map)
        have h_len : args₁.length = args₂.length := by
          have h_len_eq := congrArg List.length h_args; simp [List.length_map] at h_len_eq; exact h_len_eq
        -- The arity check uses h_len to show both sides get the same matchesArg
        simp only [h_len]
        -- Now both sides compute the same matchesArg value
        -- Case split on the actual boolean check result
        cases aPA
        · -- aPA = false: check is args₂.length == func.inputs.length
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases h_check : (args₂.length == func.inputs.length) <;> simp_all
        · -- aPA = true: check is Nat.ble args₂.length func.inputs.length
          simp only [↓reduceIte]
          cases h_check : (Nat.ble args₂.length func.inputs.length) <;> simp_all
  | .const _ _, .const _ _, _ => simp
  | .bvar _ _, .bvar _ _, _ => simp
  | .fvar _ _ _, .fvar _ _ _, _ => simp
  | .abs _ _ _ _, .abs _ _ _ _, _ => simp
  | .quant _ _ _ _ _ _, .quant _ _ _ _ _ _, _ => simp
  | .ite _ _ _ _, .ite _ _ _ _, _ => simp
  | .eq _ _ _, .eq _ _ _, _ => simp
  | .app _ _ _, .app _ _ _, _ => simp

-- Corollary: if callOfLFunc on e₁ returns none, so does callOfLFunc on e₂ (same eM)
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem callOfLFunc_none_of_eraseMetadata_eq
    (F : @Factory Tbase) (e₁ e₂ : LExpr Tbase.mono) (aPA : Bool)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (h_none : F.callOfLFunc e₁ (allowPartialApp := aPA) = none) :
    F.callOfLFunc e₂ (allowPartialApp := aPA) = none := by
  have h := callOfLFunc_eraseMetadata_congr F e₁ e₂ aPA h_eM
  rw [h_none] at h
  cases h₂ : F.callOfLFunc e₂ (allowPartialApp := aPA) with
  | none => rfl
  | some v => rw [h₂] at h; exact absurd h (by simp)

-- Corollary: if callOfLFunc on e₁ returns some, so does callOfLFunc on e₂ (same eM),
-- with the same function, args with the same eraseMetadata, and ops with the same eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem callOfLFunc_some_of_eraseMetadata_eq
    (F : @Factory Tbase) (e₁ e₂ : LExpr Tbase.mono) (aPA : Bool)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (op₁ : LExpr Tbase.mono) (args₁ : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (h_some : F.callOfLFunc e₁ (allowPartialApp := aPA) = some (op₁, args₁, f)) :
    ∃ op₂ args₂, F.callOfLFunc e₂ (allowPartialApp := aPA) = some (op₂, args₂, f) ∧
      args₁.map LExpr.eraseMetadata = args₂.map LExpr.eraseMetadata ∧
      op₁.eraseMetadata = op₂.eraseMetadata := by
  have h := callOfLFunc_eraseMetadata_congr F e₁ e₂ aPA h_eM
  rw [h_some] at h
  cases h₂ : F.callOfLFunc e₂ (allowPartialApp := aPA) with
  | none => rw [h₂] at h; exact absurd h (by simp)
  | some v =>
    obtain ⟨op₂, args₂, f₂⟩ := v
    rw [h₂] at h
    obtain ⟨h_f, h_args, h_op_eM⟩ := h
    subst h_f
    exact ⟨op₂, args₂, rfl, h_args, h_op_eM⟩

-- Generalized version: works with any folding function, not just eql-specific.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
-- Corollary for attach.zip (specialized to LExpr)
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem foldl_attach_zip_eq_eql
    (F : @Factory Tbase)
    (init : Option Bool)
    (l₁ : List (LExpr Tbase.mono)) (l₂ : List (LExpr Tbase.mono)) :
    List.foldl (fun acc (x : { x // x ∈ l₁ } × LExpr Tbase.mono) =>
      LExpr.eqlCombine acc (LExpr.eql F x.1.val x.snd)) init (l₁.attach.zip l₂) =
    List.foldl (fun acc (x : LExpr Tbase.mono × LExpr Tbase.mono) =>
      LExpr.eqlCombine acc (LExpr.eql F x.1 x.2)) init (l₁.zip l₂) := by
  rw [List.foldl_subtype_zip_val (· ∈ l₁) (fun acc a b => LExpr.eqlCombine acc (LExpr.eql F a b)) init l₁.attach l₂,
      List.attach_map_subtype_val]

-- foldl over plain zip is congruent when the function produces equal results on corresponding elements.
-- Specialized version of List.foldl_zip_congr for eql
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem foldl_zip_eql_congr
    (F : @Factory Tbase)
    (args₁ args₁' args₂ args₂' : List (LExpr Tbase.mono))
    (h_eM₁ : args₁.map LExpr.eraseMetadata = args₁'.map LExpr.eraseMetadata)
    (h_eM₂ : args₂.map LExpr.eraseMetadata = args₂'.map LExpr.eraseMetadata)
    (ih : ∀ a1, a1 ∈ args₁ → ∀ a2 e₁' e₂',
        a1.eraseMetadata = e₁'.eraseMetadata → a2.eraseMetadata = e₂'.eraseMetadata →
        LExpr.eql F a1 a2 = LExpr.eql F e₁' e₂')
    (init : Option Bool) :
    List.foldl (fun acc (x : LExpr Tbase.mono × LExpr Tbase.mono) =>
      LExpr.eqlCombine acc (LExpr.eql F x.fst x.snd)) init (args₁.zip args₂) =
    List.foldl (fun acc (x : LExpr Tbase.mono × LExpr Tbase.mono) =>
      LExpr.eqlCombine acc (LExpr.eql F x.fst x.snd)) init (args₁'.zip args₂') := by
  -- Derive length equalities from map equalities
  have h_len₁ : args₁.length = args₁'.length := by
    have h_len_eq := congrArg List.length h_eM₁; simp at h_len_eq; exact h_len_eq
  have h_len₂ : args₂.length = args₂'.length := by
    have h_len_eq := congrArg List.length h_eM₂; simp at h_len_eq; exact h_len_eq
  -- Use generic foldl_zip_congr
  apply List.foldl_zip_congr (fun acc a b => LExpr.eqlCombine acc (LExpr.eql F a b)) _ _ _ _ h_len₁ h_len₂
  · intro i hi₁ hi₂ acc
    -- Get elements at index i
    have hi₁' : i < args₁'.length := h_len₁ ▸ hi₁
    have hi₂' : i < args₂'.length := h_len₂ ▸ hi₂
    have h_eM_a : (args₁[i]).eraseMetadata = (args₁'[i]'hi₁').eraseMetadata := by
      have h1 := congrArg (·[i]?) h_eM₁
      simp [hi₁, hi₁'] at h1
      exact h1
    have h_eM_b : (args₂[i]).eraseMetadata = (args₂'[i]'hi₂').eraseMetadata := by
      have h1 := congrArg (·[i]?) h_eM₂
      simp [hi₂, hi₂'] at h1
      exact h1
    -- Apply ih with membership proof
    have h_mem : args₁[i] ∈ args₁ := by
      apply List.getElem_mem
    rw [ih (args₁[i]) h_mem (args₂[i]) (args₁'[i]'hi₁') (args₂'[i]'hi₂') h_eM_a h_eM_b]

---------------------------------------------------------------------
-- eql depends only on eraseMetadata: if two pairs of expressions have the
-- same eraseMetadata, eql returns the same result.

-- eqModuloMeta depends only on eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [Inhabited Tbase.IDMeta] in
private theorem eqModuloMeta_eraseMetadata_eq
    {a b a' b' : LExpr Tbase.mono}
    (ha : a.eraseMetadata = a'.eraseMetadata)
    (hb : b.eraseMetadata = b'.eraseMetadata) :
    LExpr.eqModuloMeta a b = LExpr.eqModuloMeta a' b' := by
  unfold LExpr.eqModuloMeta; rw [ha, hb]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem eql_eraseMetadata_eq
    {Tbase : LExprParams}
    [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
    (F : @Factory Tbase)
    (e₁ e₂ e₁' e₂' : LExpr Tbase.mono)
    (h₁ : e₁.eraseMetadata = e₁'.eraseMetadata)
    (h₂ : e₂.eraseMetadata = e₂'.eraseMetadata) :
    LExpr.eql F e₁ e₂ = LExpr.eql F e₁' e₂' := by
  -- Revert e₁'/e₂'/h₁/h₂ so fun_induction produces a universally quantified IH
  revert e₁' e₂' h₁ h₂
  fun_induction LExpr.eql F e₁ e₂ <;> intro e₁' e₂' h₁ h₂
  -- Case 1: eqModuloMeta true
  · rename_i h_eqmod
    rw [eqModuloMeta_eraseMetadata_eq h₁ h₂] at h_eqmod
    unfold LExpr.eql; simp [h_eqmod]
  -- Cases 2-8: For each, use EMEquiv to decompose e₁'/e₂', then show same eql branch fires.
  -- The key trick: rewrite h_not_eqmod BEFORE cases to keep it in a usable form.
  -- Case 2: const/const, realConst/realConst
  · rename_i h_not_eqmod _ _
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm']
  -- Case 3: const/const, non-real
  · rename_i h_not_eqmod _ _
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂
    -- Goal: some (c1 == c2) = eql F (.const m' c1) (.const m₂' c2)
    -- Unfold eql: eqModuloMeta false → match const/const → match on c1/c2
    -- The hyp x✝ says c1/c2 can't both be realConst, so same non-real branch fires.
    unfold LExpr.eql; simp only [h_nm']
    -- Now need to handle the match on c1, c2
    split <;> simp_all
  -- Case 4: abs/abs ty mismatch
  · rename_i h_not_eqmod h_ty_ne _
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm', h_ty_ne]
  -- Case 5: abs/abs closed → recursive eql on varOpen
  · -- With revert/intro, ih is now universally quantified over e₁'/e₂'.
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁ with
    | abs hv_body₁ =>
      cases hv₂ with
      | abs hv_body₂ =>
        have h_fv₁ := LExpr.freeVars_of_eraseMetadata_eq _ _ hv_body₁.eraseMetadata_eq
        have h_fv₂ := LExpr.freeVars_of_eraseMetadata_eq _ _ hv_body₂.eraseMetadata_eq
        rename_i _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
        -- Apply ih to get LHS = eql on varOpen'd primed bodies
        rw [ih _ _ (LExpr.varOpen_eraseMetadata_congr hv_body₁.eraseMetadata_eq)
                   (LExpr.varOpen_eraseMetadata_congr hv_body₂.eraseMetadata_eq)]
        -- Now goal: eql F (varOpen body₁') (varOpen body₂') = eql F (.abs ..) (.abs ..)
        -- Unfold RHS: for the abs/abs case, eql returns the recursive call on varOpen
        simp only [LExpr.eql, h_nm', LExpr.closed] at *
        simp_all
  -- Case 6: abs/abs not closed
  · have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁ with
    | abs hv_body₁ =>
      cases hv₂ with
      | abs hv_body₂ =>
        have h_fv₁ := LExpr.freeVars_of_eraseMetadata_eq _ _ hv_body₁.eraseMetadata_eq
        have h_fv₂ := LExpr.freeVars_of_eraseMetadata_eq _ _ hv_body₂.eraseMetadata_eq
        simp only [LExpr.eql, h_nm', LExpr.closed, Bool.and_eq_true_iff] at *
        simp_all
  -- Case 7: const/abs
  · rename_i h_not_eqmod
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm']
  -- Case 8: abs/const
  · rename_i h_not_eqmod
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm']
  -- Cases 9-13: callOfLFunc catch-all (nested match)
  · -- case 9: callOfLFunc some/some, not both constructors → none
    rename_i _ _ _ _ h_ne _ _ _ _ _ _ h_call₁ h_call₂ h_nc h_not_cc h_not_aa h_not_ca h_not_ac
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne

    rw [h_call₁, h_call₂]; simp only [h_nc, ↓reduceIte]
    obtain ⟨_, _, h_call₁', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁ _ _ _ h_call₁
    obtain ⟨_, _, h_call₂', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂ _ _ _ h_call₂
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    symm; unfold LExpr.eql; rw [h_ef, if_neg (by decide)]
    split <;>
    first
    | (rw [h_call₁', h_call₂']; simp only [h_nc, ↓reduceIte])
    | (exfalso
       have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
       have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
       cases hv₁; cases hv₂
       first
       | exact h_not_cc _ _ _ _ rfl rfl
       | exact h_not_aa _ _ _ _ _ _ _ _ rfl rfl
       | exact h_not_ca _ _ _ _ _ _ rfl rfl
       | exact h_not_ac _ _ _ _ _ _ rfl rfl)
  · -- case 10: callOfLFunc some/some, both constructors, different names → some false
    rename_i _ _ _ _ h_ne _ _ _ _ _ _ h_call₁ h_call₂ h_nc h_nd h_not_cc h_not_aa h_not_ca h_not_ac
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne
    rw [h_call₁, h_call₂]; simp only [h_nc, h_nd, ↓reduceIte]
    obtain ⟨_, _, h_call₁', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁ _ _ _ h_call₁
    obtain ⟨_, _, h_call₂', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂ _ _ _ h_call₂
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    symm; unfold LExpr.eql; rw [h_ef, if_neg (by decide)]
    split <;>
    first
    | (rw [h_call₁', h_call₂']; simp only [h_nc, h_nd, ↓reduceIte])
    | (exfalso
       have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
       have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
       cases hv₁; cases hv₂
       first
       | exact h_not_cc _ _ _ _ rfl rfl
       | exact h_not_aa _ _ _ _ _ _ _ _ rfl rfl
       | exact h_not_ca _ _ _ _ _ _ rfl rfl
       | exact h_not_ac _ _ _ _ _ _ rfl rfl)
  · -- case 11: callOfLFunc some/some, both constructors, same name → foldl eqlCombine
    rename_i _ _ _ h_ne _ _ _ _ _ _ h_call₁ h_call₂ h_nc h_nd h_not_cc h_not_aa h_not_ca h_not_ac ih
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne
    rw [h_call₁, h_call₂]; simp only [h_nc, h_nd]
    obtain ⟨_, _, h_call₁', h_eM_args₁, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁ _ _ _ h_call₁
    obtain ⟨_, _, h_call₂', h_eM_args₂, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂ _ _ _ h_call₂
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    -- Use eq_6 to unfold only the top-level eql (preserving inner eql calls in foldl)
    symm
    rw [Lambda.LExpr.eql.eq_6 F e₁' e₂' (by
        intro m c1 m₁ c2 he₁ he₂; subst he₁; subst he₂
        have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
        have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
        cases hv₁; cases hv₂; exact h_not_cc _ _ _ _ rfl rfl)
      (by intro m n ty b m₁ n₁ ty₁ b₁ he₁ he₂; subst he₁; subst he₂
          have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
          have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
          cases hv₁; cases hv₂; exact h_not_aa _ _ _ _ _ _ _ _ rfl rfl)
      (by intro m c m₁ n ty b he₁ he₂; subst he₁; subst he₂
          have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
          have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
          cases hv₁; cases hv₂; exact h_not_ca _ _ _ _ _ _ rfl rfl)
      (by intro m n ty b m₁ c he₁ he₂; subst he₁; subst he₂
          have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
          have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
          cases hv₁; cases hv₂; exact h_not_ac _ _ _ _ _ _ rfl rfl)]
    rw [h_ef, if_neg (by decide), h_call₁', h_call₂']
    simp only [h_nc, h_nd]
    -- Clear remaining if false = true wrappers
    simp only [if_neg (by decide : ¬(false = true))]
    -- Convert both foldls from attach.zip to plain zip using the helper
    simp only [foldl_attach_zip_eq_eql F]
    -- Apply the zip congruence helper
    exact (foldl_zip_eql_congr F _ _ _ _ h_eM_args₁ h_eM_args₂ ih _).symm
  · -- case 12: callOfLFunc catch-all (simultaneous match not both some) → none
    rename_i h_ne h_not_cc h_not_aa h_not_ca h_not_ac h_not_both_some
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    -- LHS: the simultaneous match must hit catch-all since some/some is impossible
    -- Split on the goal's match to resolve it to none
    split
    · -- some/some for e1/e2: contradicts h_not_both_some
      rename_i fst args1 f1 fst_1 args2 f2 h1 h2
      exact absurd h2 (fun h2 => h_not_both_some fst args1 f1 fst_1 args2 f2 h1 h2)
    · -- catch-all for e1/e2: LHS = none, now show RHS eql F e₁' e₂' = none
      symm; unfold LExpr.eql; rw [h_ef, if_neg (by decide)]
      split <;>
      first
      | (-- Reach the simultaneous match for e₁'/e₂'; split again
         simp only []
         split
         · -- some/some for e₁'/e₂': transfer back to e1/e2 → contradiction
           rename_i op₁' args₁' f₁' op₂' args₂' f₂' h_call₁' h_call₂'
           obtain ⟨op₁, args₁, h_call₁, _, _⟩ :=
             callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁.symm _ _ _ h_call₁'
           obtain ⟨op₂, args₂, h_call₂, _, _⟩ :=
             callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂.symm _ _ _ h_call₂'
           exact absurd h_call₂ (fun h2 => h_not_both_some op₁ args₁ _ op₂ args₂ _ h_call₁ h2)
         · rfl)
      | (exfalso
         have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
         have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
         cases hv₁; cases hv₂
         first
         | exact h_not_cc _ _ _ _ rfl rfl
         | exact h_not_aa _ _ _ _ _ _ _ _ rfl rfl
         | exact h_not_ca _ _ _ _ _ _ rfl rfl
         | exact h_not_ac _ _ _ _ _ _ rfl rfl)

---------------------------------------------------------------------

-- Helper: if IH gives e →* e' with EMEquiv (subst e') (subst (.const m c)),
-- then e can step to an actual .const (through e' + possible fvar expansion).
-- This is key for ite/eq reduction cases where we need the condition/result
-- to be syntactically a .const for the Step rule to fire.

private theorem step_to_const_via_IH
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase)
    (e e' : LExpr Tbase.mono) (mc : Tbase.Metadata) (c : LConst)
    (hstep : StepStar σ.config.factory (Scopes.toEnv σ.state) e e')
    (h_eM : e'.eraseMetadata = (LExpr.const mc c).eraseMetadata) :
    ∃ mc', StepStar σ.config.factory (Scopes.toEnv σ.state) e (.const mc' c) := by
  -- e'.eraseMetadata = (.const mc c).eraseMetadata means e' must be a .const (by inspection).
  simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM
  cases e' <;> simp [LExpr.replaceMetadata] at h_eM <;> try contradiction
  rename_i mc' c'; subst c'
  exact ⟨_, hstep⟩

---------------------------------------------------------------------

-- Helper lemma: substFvars is identity on closed terms (no free variables)
private theorem substFvars_closed_identity
    {Tbase : LExprParams}
    [DecidableEq Tbase.IDMeta]
    (e : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (h_closed : LExpr.freeVars e = []) :
    LExpr.substFvars e sm = e := by
  simp only [LExpr.substFvars, Map.isEmpty]
  split
  · -- sm is empty: trivially returns e
    rfl
  · -- sm is nonempty, but e has no free vars
    -- Need to show substFvarsAux e sm = e
    induction e with
    | const => simp [LExpr.substFvars.substFvarsAux]
    | op => simp [LExpr.substFvars.substFvarsAux]
    | bvar => simp [LExpr.substFvars.substFvarsAux]
    | fvar => simp [LExpr.freeVars] at h_closed
    | abs _ _ _ _ ih =>
      simp [LExpr.substFvars.substFvarsAux]
      simp [LExpr.freeVars] at h_closed
      exact ih h_closed
    | app _ _ _ ih1 ih2 =>
      simp [LExpr.substFvars.substFvarsAux]
      simp [LExpr.freeVars, List.append_eq_nil_iff] at h_closed
      exact ⟨ih1 h_closed.1, ih2 h_closed.2⟩
    | eq _ _ _ ih1 ih2 =>
      simp [LExpr.substFvars.substFvarsAux]
      simp [LExpr.freeVars, List.append_eq_nil_iff] at h_closed
      exact ⟨ih1 h_closed.1, ih2 h_closed.2⟩
    | quant _ _ _ _ _ _ ih1 ih2 =>
      simp [LExpr.substFvars.substFvarsAux]
      simp [LExpr.freeVars, List.append_eq_nil_iff] at h_closed
      exact ⟨ih1 h_closed.1, ih2 h_closed.2⟩
    | ite _ c t e ih1 ih2 ih3 =>
      simp [LExpr.substFvars.substFvarsAux]
      have h_fv_all : LExpr.freeVars c ++ LExpr.freeVars t ++ LExpr.freeVars e = [] := h_closed
      have h_app1 : LExpr.freeVars c ++ LExpr.freeVars t = [] ∧ LExpr.freeVars e = [] :=
        List.append_eq_nil_iff.mp h_fv_all
      have h_c_t : LExpr.freeVars c = [] ∧ LExpr.freeVars t = [] :=
        List.append_eq_nil_iff.mp h_app1.1
      exact ⟨ih1 h_c_t.1, ih2 h_c_t.2, ih3 h_app1.2⟩

private theorem StepStar_to_substFvarsFromState_abs
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (m : Tbase.Metadata) (name : String) (ty : Option LMonoTy)
    (body : LExpr Tbase.mono) :
    StepStar σ.config.factory (Scopes.toEnv σ.state)
      (.abs m name ty body) (LExpr.substFvarsFromState σ (.abs m name ty body)) := by
  simp only [LExpr.substFvarsFromState, LExpr.substFvars_abs]
  cases h_fv : (LExpr.freeVars body) with
  | nil =>
    have h_subst_id : LExpr.substFvars body (σ.state.toSingleMap.map (fun (k : _ × _ × _) => (k.1, k.2.2))) = body :=
      substFvars_closed_identity body _ h_fv
    rw [h_subst_id]; exact ReflTrans.refl _
  | cons p ps =>
    have h_mem : p.fst ∈ (LExpr.freeVars body).map Prod.fst := by
      rw [h_fv]; simp [List.map]
    exact ReflTrans.step _ _ _
      (Step.abs_subst_fvars (m' := m) body σ p.fst h_mem rfl)
      (ReflTrans.refl _)

private theorem StepStar_to_substFvarsFromState_quant
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (m : Tbase.Metadata) (qk : QuantifierKind)
    (name : String) (ty : Option LMonoTy)
    (tr body : LExpr Tbase.mono) :
    StepStar σ.config.factory (Scopes.toEnv σ.state)
      (.quant m qk name ty tr body) (LExpr.substFvarsFromState σ (.quant m qk name ty tr body)) := by
  simp only [LExpr.substFvarsFromState, LExpr.substFvars_quant]
  cases h_fv_body : (LExpr.freeVars body) with
  | nil =>
    cases h_fv_tr : (LExpr.freeVars tr) with
    | nil =>
      rw [substFvars_closed_identity body _ h_fv_body, substFvars_closed_identity tr _ h_fv_tr]
      exact ReflTrans.refl _
    | cons p ps =>
      rw [substFvars_closed_identity body _ h_fv_body]
      have h_mem : p.fst ∈ (LExpr.freeVars tr).map Prod.fst := by rw [h_fv_tr]; simp [List.map]
      exact ReflTrans.step _ _ _
        (Step.quant_subst_fvars_trigger (m' := m) tr body σ p.fst h_mem rfl) (ReflTrans.refl _)
  | cons p ps =>
    cases h_fv_tr : (LExpr.freeVars tr) with
    | nil =>
      rw [substFvars_closed_identity tr _ h_fv_tr]
      have h_mem : p.fst ∈ (LExpr.freeVars body).map Prod.fst := by rw [h_fv_body]; simp [List.map]
      exact ReflTrans.step _ _ _
        (Step.quant_subst_fvars_body (m' := m) tr body σ p.fst h_mem rfl) (ReflTrans.refl _)
    | cons p2 ps2 =>
      have h_mem_body : p.fst ∈ (LExpr.freeVars body).map Prod.fst := by rw [h_fv_body]; simp [List.map]
      have h_mem_tr : p2.fst ∈ (LExpr.freeVars tr).map Prod.fst := by rw [h_fv_tr]; simp [List.map]
      exact ReflTrans_Transitive _ _ _ _
        (ReflTrans.step _ _ _
          (Step.quant_subst_fvars_body (m' := m) tr body σ p.fst h_mem_body rfl) (ReflTrans.refl _))
        (ReflTrans.step _ _ _
          (Step.quant_subst_fvars_trigger (m' := m) tr (LExpr.substFvarsFromState σ body) σ p2.fst h_mem_tr rfl) (ReflTrans.refl _))

---------------------------------------------------------------------

-- isCanonicalValue depends only on eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem isCanonicalValue_eraseMetadata_eq
    {Tbase : LExprParams}
    [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
    (F : @Factory Tbase)
    (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.isCanonicalValue F e₁ = LExpr.isCanonicalValue F e₂ := by
  -- Use strong induction on e₁.sizeOf
  suffices h : ∀ (sz : Nat) (e₁ e₂ : LExpr Tbase.mono),
      e₁.sizeOf ≤ sz → e₁.eraseMetadata = e₂.eraseMetadata →
      LExpr.isCanonicalValue F e₁ = LExpr.isCanonicalValue F e₂ from
    h e₁.sizeOf e₁ e₂ (Nat.le_refl _) h_eM
  intro sz; induction sz with
  | zero =>
    intro e₁ e₂ hsz heM
    -- sizeOf is always positive, so this is vacuous
    exact absurd hsz (by have := LExpr.sizeOf_pos e₁; omega)
  | succ sz ih =>
    intro e₁ e₂ hsz heM
    -- Case split on e₁ constructor, then use heM to recover e₂'s constructor
    cases e₁ with
    | const m c =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isCanonicalValue]
    | abs m nm ty body =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | abs _ => simp only [LExpr.isCanonicalValue]; unfold LExpr.closed; rw [LExpr.freeVars_of_eraseMetadata_eq _ _ heM]
    | quant m qk nm ty tr body =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | quant _ _ => simp only [LExpr.isCanonicalValue]; unfold LExpr.closed; rw [LExpr.freeVars_of_eraseMetadata_eq _ _ heM]
    | op m nm ty =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | op =>
        simp only [LExpr.isCanonicalValue]
        cases h1 : F.callOfLFunc (.op m nm ty : LExpr Tbase.mono) (allowPartialApp := true) with
        | none =>
          rw [callOfLFunc_none_of_eraseMetadata_eq F _ _ true heM h1]
        | some v1 =>
          obtain ⟨op₂, args₂, h2, h_args_eM, _⟩ :=
            callOfLFunc_some_of_eraseMetadata_eq F _ _ true heM v1.1 v1.2.1 v1.2.2 h1
          rw [h2]; simp only
          have h_args_nil : v1.snd.fst = [] := by
            have h1' := h1
            unfold Factory.callOfLFunc at h1'
            simp only [getLFuncCall, getLFuncCall.go] at h1'
            split at h1' <;> simp at h1'
            split at h1' <;> simp at h1'
            rw [← h1']
          have h_len : v1.snd.fst.length = args₂.length := by
            have h_len_eq := congrArg List.length h_args_eM; simp [List.length_map] at h_len_eq; exact h_len_eq
          have h_args₂_nil : args₂ = [] := by
            rw [h_args_nil] at h_len; simp at h_len
            exact List.eq_nil_of_length_eq_zero h_len.symm
          rw [h_args_nil, h_args₂_nil]
    | bvar m i =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
    | fvar m x ty =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
    | app m fn arg =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | app hfn harg =>
        simp only [LExpr.isCanonicalValue]
        cases h1 : F.callOfLFunc (.app m fn arg : LExpr Tbase.mono) (allowPartialApp := true) with
        | none =>
          rw [callOfLFunc_none_of_eraseMetadata_eq F _ _ true heM h1]
        | some v1 =>
          obtain ⟨op₁, args₁, f₁⟩ := v1
          obtain ⟨op₂, args₂, h2, h_args_eM, _⟩ :=
            callOfLFunc_some_of_eraseMetadata_eq F _ _ true heM op₁ args₁ f₁ h1
          rw [h2]; simp only
          have h_len : args₁.length = args₂.length := by
            have h_len_eq := congrArg List.length h_args_eM; simp [List.length_map] at h_len_eq; exact h_len_eq
          simp only [h_len]
          -- The first part of && is the same; need to show all-canonical is the same
          congr 1
          -- Extract getLFuncCall from h1 to prove args are smaller
          have h_gl : getLFuncCall (.app m fn arg : LExpr Tbase.mono) = (op₁, args₁) := by
            simp [Factory.callOfLFunc] at h1
            cases h_lfc : getLFuncCall (.app m fn arg : LExpr Tbase.mono) with | mk op' args' =>
            simp only [h_lfc] at h1
            cases op' <;> simp at h1
            rename_i name_op _ _
            split at h1
            · simp at h1
            · split at h1 <;> simp at h1
              obtain ⟨rfl, rfl, _⟩ := h1; exact rfl
          have h_smaller := getLFuncCall_smaller h_gl
          -- Prove the two mapped-attach lists are equal by list induction
          suffices h_map : args₁.attach.map (fun x => LExpr.isCanonicalValue F x.val) =
              args₂.attach.map (fun x => LExpr.isCanonicalValue F x.val) by
            rw [h_map]
          apply List.ext_getElem
          · simp [h_len]
          · intro i hi₁ hi₂
            simp only [List.getElem_map, List.getElem_attach]
            have hi₁' : i < args₁.length := by simpa [List.length_attach] using hi₁
            have hi₂' : i < args₂.length := by simpa [List.length_attach] using hi₂
            apply ih
            · have := h_smaller (args₁[i]) (List.getElem_mem hi₁')
              omega
            · have h_eM_i := congrArg (fun l => l[i]?) h_args_eM
              simp [hi₁', hi₂'] at h_eM_i
              exact h_eM_i
    | eq m l r =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
    | ite m c t f =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isCanonicalValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

-- isConstrApp depends only on eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem isConstrApp_eraseMetadata_eq
    (F : @Factory Tbase)
    (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.isConstrApp F e₁ = LExpr.isConstrApp F e₂ := by
  simp only [LExpr.isConstrApp]
  have h := callOfLFunc_eraseMetadata_congr F e₁ e₂ true h_eM
  cases h₁ : F.callOfLFunc e₁ (allowPartialApp := true) with
  | none =>
    cases h₂ : F.callOfLFunc e₂ (allowPartialApp := true) with
    | none => rfl
    | some v => rw [h₁, h₂] at h; exact absurd h (by simp)
  | some v =>
    obtain ⟨op₁, args₁, f₁⟩ := v
    cases h₂ : F.callOfLFunc e₂ (allowPartialApp := true) with
    | none => rw [h₁, h₂] at h; exact absurd h (by simp)
    | some v₂ =>
      obtain ⟨op₂, args₂, f₂⟩ := v₂
      rw [h₁, h₂] at h
      simp at h
      rw [h.1]

---------------------------------------------------------------------
-- Helper lemmas for eval_eraseMetadata_invariant

-- evalIte preserves eraseMetadata given IH for eval
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem evalIte_eraseMetadata_congr
    [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (n' : Nat) (σ : LState Tbase)
    (m₁ m₂ : Tbase.Metadata) (c₁ c₂ t₁ t₂ f₁ f₂ : LExpr Tbase.mono)
    (hc : c₁.eraseMetadata = c₂.eraseMetadata)
    (ht : t₁.eraseMetadata = t₂.eraseMetadata)
    (hf : f₁.eraseMetadata = f₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' σ e₁).eraseMetadata = (LExpr.eval n' σ e₂).eraseMetadata) :
    (LExpr.evalIte n' σ m₁ c₁ t₁ f₁).eraseMetadata =
    (LExpr.evalIte n' σ m₂ c₂ t₂ f₂).eraseMetadata := by
  simp only [LExpr.evalIte]
  have hc' := ih c₁ c₂ hc
  generalize LExpr.eval n' σ c₁ = c₁' at hc' ⊢
  generalize LExpr.eval n' σ c₂ = c₂' at hc' ⊢
  have hv := EMEquiv.of_eraseMetadata_eq _ _ hc'
  cases hv with
  | const =>
    split <;> split <;>
    first
    | exact ih t₁ t₂ ht  -- true branch
    | exact ih f₁ f₂ hf  -- false branch
    | exact eraseMetadata_ite_congr hc' (ih t₁ t₂ ht) (ih f₁ f₂ hf)  -- default
    | (exfalso; simp_all [LExpr.eraseMetadata, LExpr.replaceMetadata])  -- mismatch: impossible
  | _ => exact eraseMetadata_ite_congr hc' (ih t₁ t₂ ht) (ih f₁ f₂ hf)

-- evalEq preserves eraseMetadata given IH for eval
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem evalEq_eraseMetadata_congr
    [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (n' : Nat) (σ : LState Tbase)
    (m₁ m₂ : Tbase.Metadata) (l₁ l₂ r₁ r₂ : LExpr Tbase.mono)
    (hl : l₁.eraseMetadata = l₂.eraseMetadata)
    (hr : r₁.eraseMetadata = r₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' σ e₁).eraseMetadata = (LExpr.eval n' σ e₂).eraseMetadata) :
    (LExpr.evalEq n' σ m₁ l₁ r₁).eraseMetadata =
    (LExpr.evalEq n' σ m₂ l₂ r₂).eraseMetadata := by
  simp only [LExpr.evalEq]
  have hl' := ih l₁ l₂ hl
  have hr' := ih r₁ r₂ hr
  -- eql depends only on eraseMetadata
  rw [eql_eraseMetadata_eq σ.config.factory _ _ _ _ hl' hr']
  -- Generalize eql result for clean split
  generalize LExpr.eql σ.config.factory (LExpr.eval n' σ l₂) (LExpr.eval n' σ r₂) = eql_res
  cases eql_res with
  | some b => simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]
  | none => exact eraseMetadata_eq_congr hl' hr'

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [Inhabited Tbase.IDMeta] in
private theorem substFvarsLifting_zip_eraseMetadata_congr
    (e : LExpr Tbase.mono)
    (keys : List Tbase.Identifier)
    (vals₁ vals₂ : List (LExpr Tbase.mono))
    (h_vals : vals₁.map LExpr.eraseMetadata = vals₂.map LExpr.eraseMetadata) :
    (LExpr.substFvarsLifting e (keys.zip vals₁)).eraseMetadata =
    (LExpr.substFvarsLifting e (keys.zip vals₂)).eraseMetadata := by
  have h_vals_len : vals₁.length = vals₂.length := by
    have h_len_eq := congrArg List.length h_vals; simp at h_len_eq; exact h_len_eq
  have find_congr : ∀ (x : Tbase.Identifier),
      (Map.find? (keys.zip vals₁) x).map LExpr.eraseMetadata =
      (Map.find? (keys.zip vals₂) x).map LExpr.eraseMetadata := by
    intro x
    induction keys generalizing vals₁ vals₂ with
    | nil => simp [List.zip_nil_left, Map.find?]
    | cons k ks ih =>
      cases vals₁ with
      | nil => cases vals₂ <;> simp_all [Map.find?]
      | cons v₁ vs₁ =>
        cases vals₂ with
        | nil => simp at h_vals
        | cons v₂ vs₂ =>
          simp only [List.zip_cons_cons, Map.find?]
          simp only [List.map_cons, List.cons.injEq] at h_vals
          split
          · simp [h_vals.1]
          · exact ih vs₁ vs₂ h_vals.2 (by simp at h_vals_len; exact h_vals_len)
  cases keys with
  | nil => simp [LExpr.substFvarsLifting, Map.isEmpty]
  | cons k ks =>
    cases vals₁ with
    | nil =>
      cases vals₂ with
      | nil => rfl
      | cons _ _ => simp at h_vals
    | cons v₁ vs₁ =>
      cases vals₂ with
      | nil => simp at h_vals
      | cons v₂ vs₂ =>
      simp only [List.zip_cons_cons, LExpr.substFvarsLifting, Map.isEmpty]
      simp only [List.map_cons, List.cons.injEq] at h_vals
      -- Both sides use go. Prove go gives same eM by induction on e with generalized depth.
      suffices hsuff : ∀ (e : LExpr Tbase.mono) (depth : Nat),
          (LExpr.substFvarsLifting.go ((k, v₁) :: ks.zip vs₁) e depth).eraseMetadata =
          (LExpr.substFvarsLifting.go ((k, v₂) :: ks.zip vs₂) e depth).eraseMetadata by
        exact hsuff e 0
      intro e depth
      induction e generalizing depth with
      | const m c => simp [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
      | op m n t => simp [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
      | bvar m i => simp [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
      | fvar m x ty =>
        simp only [LExpr.substFvarsLifting.go]
        have hfc := find_congr x
        simp only [List.zip_cons_cons] at hfc
        cases h1 : Map.find? ((k, v₁) :: ks.zip vs₁) x with
        | none =>
          cases h2 : Map.find? ((k, v₂) :: ks.zip vs₂) x with
          | none => simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
          | some w₂ => simp [h1, h2] at hfc
        | some w₁ =>
          cases h2 : Map.find? ((k, v₂) :: ks.zip vs₂) x with
          | none => simp [h1, h2] at hfc
          | some w₂ =>
            simp [h1, h2] at hfc
            exact LExpr.liftBVars_eraseMetadata_congr depth w₁ w₂ 0 hfc
      | abs m n t b ih =>
        simp only [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
        exact congrArg _ (ih (depth + 1))
      | app m f a ihf iha =>
        simp only [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
        exact congr (congrArg _ (ihf depth)) (iha depth)
      | eq m l r ihl ihr =>
        simp only [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
        exact congr (congrArg _ (ihl depth)) (ihr depth)
      | quant m qk n ty tr b iht ihb =>
        simp only [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
        exact congr (congrArg _ (iht (depth + 1))) (ihb (depth + 1))
      | ite m c t f ihc iht ihf =>
        simp only [LExpr.substFvarsLifting.go, LExpr.eraseMetadata, LExpr.replaceMetadata]
        exact congr (congr (congrArg _ (ihc depth)) (iht depth)) (ihf depth)

-- evalApp preserves eraseMetadata given IH for eval
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem evalApp_eraseMetadata_congr
    [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (n' : Nat) (σ : LState Tbase)
    (e₁ e₂ a₁ a₂ b₁ b₂ : LExpr Tbase.mono)
    (he : e₁.eraseMetadata = e₂.eraseMetadata)
    (ha : a₁.eraseMetadata = a₂.eraseMetadata)
    (hb : b₁.eraseMetadata = b₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' σ e₁).eraseMetadata = (LExpr.eval n' σ e₂).eraseMetadata) :
    (LExpr.evalApp n' σ e₁ a₁ b₁).eraseMetadata =
    (LExpr.evalApp n' σ e₂ a₂ b₂).eraseMetadata := by
  simp only [LExpr.evalApp]
  have ha' := ih a₁ a₂ ha
  have hb' := ih b₁ b₂ hb
  -- Generalize eval results for pattern matching
  generalize hg₁ : LExpr.eval n' σ a₁ = a₁' at ha' ⊢
  generalize hg₂ : LExpr.eval n' σ a₂ = a₂' at ha' ⊢
  generalize hg₃ : LExpr.eval n' σ b₁ = b₁' at hb' ⊢
  generalize hg₄ : LExpr.eval n' σ b₂ = b₂' at hb' ⊢
  -- Match on eval'd function
  have hv := EMEquiv.of_eraseMetadata_eq _ _ ha'
  cases hv with
  | abs hv_body =>
    -- Reduce the match on .abs
    dsimp only
    generalize hs₁ : (LExpr.subst _ _) = s₁
    generalize hs₂ : (LExpr.subst _ _) = s₂
    have h_subst_eM : s₁.eraseMetadata = s₂.eraseMetadata := by
      subst hs₁; subst hs₂
      apply substK_eraseMetadata_congr₂ _ _ 0 _ _ hv_body.eraseMetadata_eq
      intro m₁ m₂
      -- (replaceMetadata1 m e).eraseMetadata = e.eraseMetadata
      have h_rp1 : ∀ m' (e' : LExpr Tbase.mono),
          (LExpr.replaceMetadata1 m' e').eraseMetadata = e'.eraseMetadata :=
        fun m' e' => by cases e' <;> simp [LExpr.replaceMetadata1, LExpr.eraseMetadata, LExpr.replaceMetadata]
      rw [h_rp1, h_rp1]; exact hb'
    -- eqModuloMeta depends on eraseMetadata
    have h_eqmod : LExpr.eqModuloMeta e₁ s₁ = LExpr.eqModuloMeta e₂ s₂ := by
      simp only [LExpr.eqModuloMeta, BEq.beq]
      rw [he, h_subst_eM]
    rw [h_eqmod]
    split
    · exact he
    · exact ih _ _ h_subst_eM
  | const | op | bvar | fvar | quant _ _ | app _ _ | ite _ _ _ | eq _ _ =>
    dsimp only
    generalize ha₁_app : (LExpr.app _ _ _) = app₁
    generalize ha₂_app : (LExpr.app _ _ _) = app₂
    have h_app_eM : app₁.eraseMetadata = app₂.eraseMetadata := by
      subst ha₁_app; subst ha₂_app
      simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact congr (congrArg _ ha') hb'
    have h_eqmod : LExpr.eqModuloMeta e₁ app₁ = LExpr.eqModuloMeta e₂ app₂ := by
      simp only [LExpr.eqModuloMeta, BEq.beq]
      rw [he, h_app_eM]
    rw [h_eqmod]
    split
    · exact he
    · exact ih _ _ h_app_eM

-- evalCore preserves eraseMetadata given IH for eval
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem evalCore_eraseMetadata_congr
    [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (n' : Nat) (σ : LState Tbase) (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' σ e₁).eraseMetadata = (LExpr.eval n' σ e₂).eraseMetadata) :
    (LExpr.evalCore n' σ e₁).eraseMetadata =
    (LExpr.evalCore n' σ e₂).eraseMetadata := by
  -- Both have the same constructor via eraseMetadata
  generalize hg₁ : e₁ = e₁_v
  generalize hg₂ : e₂ = e₂_v
  rw [hg₁, hg₂] at h_eM
  have hv := EMEquiv.of_eraseMetadata_eq _ _ h_eM
  subst hg₁; subst hg₂
  cases hv with
  | const => simp [LExpr.evalCore, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | op => simp [LExpr.evalCore, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | bvar => simp [LExpr.evalCore, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | fvar =>
    simp only [LExpr.evalCore]
    -- Both look up same key x. Case split on find?:
    cases h_find : Maps.find? σ.state _ with
    | none =>
      rw [Maps.findD_find?_none _ _ _ h_find, Maps.findD_find?_none _ _ _ h_find]
      simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
    | some v =>
      rw [Maps.findD_find?_some _ _ _ _ h_find, Maps.findD_find?_some _ _ _ _ h_find]
  | abs hv_body =>
    simp only [LExpr.evalCore]
    exact LExpr.substFvarsFromState_eraseMetadata_congr σ _ _
      (eraseMetadata_abs_congr hv_body.eraseMetadata_eq)
  | quant hv_tr hv_body =>
    simp only [LExpr.evalCore]
    exact LExpr.substFvarsFromState_eraseMetadata_congr σ _ _
      (eraseMetadata_quant_congr hv_tr.eraseMetadata_eq hv_body.eraseMetadata_eq)
  | app hv_fn hv_arg =>
    simp only [LExpr.evalCore]
    exact evalApp_eraseMetadata_congr n' σ _ _ _ _ _ _
      h_eM hv_fn.eraseMetadata_eq hv_arg.eraseMetadata_eq ih
  | eq hv_l hv_r =>
    simp only [LExpr.evalCore]
    exact evalEq_eraseMetadata_congr n' σ _ _ _ _ _ _
      hv_l.eraseMetadata_eq hv_r.eraseMetadata_eq ih
  | ite hv_c hv_t hv_e =>
    simp only [LExpr.evalCore]
    exact evalIte_eraseMetadata_congr n' σ _ _ _ _ _ _ _ _
      hv_c.eraseMetadata_eq hv_t.eraseMetadata_eq hv_e.eraseMetadata_eq ih


---------------------------------------------------------------------

-- typeOf ignores metadata: erasing metadata preserves typeOf.
private theorem typeOf_eraseMetadata {T : LExprParams}
    (e : LExpr T.mono) : e.eraseMetadata.typeOf = e.typeOf := by
  induction e with
  | const => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
  | op => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
  | bvar => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
  | fvar => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
  | abs m name ty body ih =>
    cases ty with
    | none => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
    | some t =>
      simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
      rw [show (body.replaceMetadata fun _ => ()).typeOf = body.eraseMetadata.typeOf from rfl, ih]
  | quant => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
  | app m fn arg ih_fn _ =>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
    rw [show (fn.replaceMetadata fun _ => ()).typeOf = fn.eraseMetadata.typeOf from rfl, ih_fn]
  | ite m c t f _ ih_t _ =>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]
    rw [show (t.replaceMetadata fun _ => ()).typeOf = t.eraseMetadata.typeOf from rfl, ih_t]
  | eq => simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.typeOf]

-- If two expressions have the same eraseMetadata, they have the same typeOf.
private theorem typeOf_of_eraseMetadata_eq {T : LExprParams}
    (e₁ e₂ : LExpr T.mono) (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    e₁.typeOf = e₂.typeOf := by
  have h1 := typeOf_eraseMetadata e₁
  have h2 := typeOf_eraseMetadata e₂
  rw [h] at h1; rw [← h1, h2]

-- computeTypeSubst is metadata-invariant: if callee and args have the same
-- eraseMetadata, computeTypeSubst produces the same result.
-- computeTypeSubst depends on callee only through its .op type annotation
-- (preserved by eraseMetadata) and on args only through typeOf (also preserved).
private theorem computeTypeSubst_eraseMetadata_congr {T : LExprParams}
    (fn : LFunc T) (op₁ op₂ : LExpr T.mono)
    (args₁ args₂ : List (LExpr T.mono))
    (h_op : op₁.eraseMetadata = op₂.eraseMetadata)
    (h_args : args₁.map LExpr.eraseMetadata = args₂.map LExpr.eraseMetadata) :
    LFunc.computeTypeSubst fn op₁ args₁ = LFunc.computeTypeSubst fn op₂ args₂ := by

  -- For the args part:
  have h_argC : ((args₁.zip fn.inputs.values).filterMap
      (fun (arg, formal) => arg.typeOf.map (·, formal))) =
    ((args₂.zip fn.inputs.values).filterMap
      (fun (arg, formal) => arg.typeOf.map (·, formal))) := by
    -- Prove by auxiliary induction on args and formals simultaneously
    suffices h_suff : ∀ (l₁ l₂ : List (LExpr T.mono)) (vs : List LMonoTy),
        l₁.map LExpr.eraseMetadata = l₂.map LExpr.eraseMetadata →
        (l₁.zip vs).filterMap (fun (arg, formal) => arg.typeOf.map (·, formal)) =
        (l₂.zip vs).filterMap (fun (arg, formal) => arg.typeOf.map (·, formal)) from
      h_suff args₁ args₂ fn.inputs.values h_args
    intro l₁ l₂ vs h_eM
    induction l₁ generalizing l₂ vs with
    | nil =>
      have h_l₂_nil : l₂ = [] := by cases l₂ with | nil => rfl | cons => simp at h_eM
      subst h_l₂_nil; rfl
    | cons hd₁ tl₁ ih =>
      match l₂, vs with
      | hd₂ :: tl₂, v :: vs' =>
        simp only [List.zip_cons_cons, List.filterMap_cons]
        have h_hd : hd₁.eraseMetadata = hd₂.eraseMetadata := by
          have h_head_eq := congrArg List.head? h_eM; simp at h_head_eq; exact h_head_eq
        have h_tl : tl₁.map LExpr.eraseMetadata = tl₂.map LExpr.eraseMetadata := by
          have h_tail_eq := congrArg List.tail h_eM; simp at h_tail_eq; exact h_tail_eq
        rw [typeOf_of_eraseMetadata_eq _ _ h_hd, ih tl₂ vs' h_tl]
      | hd₂ :: tl₂, [] => simp [List.zip]
      | [], _ => simp at h_eM

  let opTyField (e : LExpr T.mono) : Option LMonoTy :=
    match e with | .op _ _ ty => ty | _ => none

  have h_opTyField : opTyField op₁ = opTyField op₂ := by
    simp only [opTyField]
    cases op₁ <;> cases op₂ <;>
      simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_op ⊢ <;>
      exact h_op.2

  have h_opFactor : ∀ (e : LExpr T.mono),
    (match e with
      | .op _ _ (some instTy) => [(instTy, LMonoTy.mkArrow' fn.output fn.inputs.values)]
      | _ => ([] : List (LMonoTy × LMonoTy))) =
    (match opTyField e with
      | some instTy => [(instTy, LMonoTy.mkArrow' fn.output fn.inputs.values)]
      | none => []) := by
    intro e; cases e with
    | op m o ty => cases ty <;> simp [opTyField]
    | _ => simp [opTyField]

  let computePure (opTy : Option LMonoTy)
      (argCs : List (LMonoTy × LMonoTy)) : Option Subst :=
    if fn.typeArgs.isEmpty then some Subst.empty
    else
      let opCs := match opTy with
        | some instTy => [(instTy, LMonoTy.mkArrow' fn.output fn.inputs.values)]
        | none => []
      let allCs := opCs ++ argCs
      if allCs.isEmpty then none
      else match Constraints.unify allCs SubstInfo.empty with
        | .ok s => some s.subst
        | .error _ => none
  -- opTypeSubst only depends on the type annotation of the callee
  have h_opTS : fn.opTypeSubst op₁ = fn.opTypeSubst op₂ := by
    simp only [LFunc.opTypeSubst]
    cases op₁ <;> cases op₂ <;>
      simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_op ⊢
    rename_i ty
    cases ty <;> grind
  simp only [LFunc.computeTypeSubst, h_opTS, h_argC]

---------------------------------------------------------------------

-- Helper for the factory-function branch of `eval_eraseMetadata_invariant`.
-- When `callOfLFunc` succeeds on `e₁` (returning factory function `f₁`),
-- this theorem shows that the post-match eval body (inline / concreteEval /
-- terminal) produces `eraseMetadata`-equal results for `e₁` and any `e₂`
-- with the same `eraseMetadata`. It handles the three-way split:
--   1. Inline: `computeTypeSubst` + `applySubst` + `substFvarsLifting` + recursive eval
--   2. ConcreteEval: `concreteEval` on evaluated args
--   3. Terminal: `mkApp` with evaluated args
-- and shows each branch is metadata-invariant, given that args evaluate to
-- `eraseMetadata`-equal results (by the IH from `eval_eraseMetadata_invariant`).
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem eval_factory_post_eraseMetadata_invariant
    {Tbase : LExprParams}
    [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
    [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (n' : Nat)
    (hWF : FactoryWF σ.config.factory)
    (f₁ : LFunc Tbase)
    (e₁ e₂ : LExpr Tbase.mono)
    (op₁ op₂ : LExpr Tbase.mono)
    (args₁ args₂ : List (LExpr Tbase.mono))
    (h_call₁ : σ.config.factory.callOfLFunc e₁ = some (op₁, args₁, f₁))
    (h_eval_args_eM : (args₁.map (LExpr.eval n' σ)).map LExpr.eraseMetadata =
        (args₂.map (LExpr.eval n' σ)).map LExpr.eraseMetadata)
    (_h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (h_op_eM : op₁.eraseMetadata = op₂.eraseMetadata)
    (h_constrArgAt_eq : ∀ idx : Option Nat,
        (match idx with
        | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isConstrApp σ.config.factory)).getD false
        | none => false) =
        (match idx with
        | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isConstrApp σ.config.factory)).getD false
        | none => false))
    (h_canonicalArgAt_eq : ∀ idx : Option Nat,
        (match idx with
        | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isCanonicalValue σ.config.factory)).getD false
        | none => false) =
        (match idx with
        | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isCanonicalValue σ.config.factory)).getD false
        | none => false))
    (h_all_canonical :
        (args₁.map (fun a => LExpr.eval n' σ a)).all (LExpr.isCanonicalValue σ.config.factory) =
        (args₂.map (fun a => LExpr.eval n' σ a)).all (LExpr.isCanonicalValue σ.config.factory))
    (ih : ∀ (a b : LExpr Tbase.mono), a.eraseMetadata = b.eraseMetadata →
        (LExpr.eval n' σ a).eraseMetadata = (LExpr.eval n' σ b).eraseMetadata) :
    -- The eval body after `some (op, args, lfunc)` match (using `fun a => eval n' σ a` for args)
    (let args' := args₁.map (fun a => LExpr.eval n' σ a)
     let cA := fun (idx : Option Nat) => match idx with
       | some i => (args'[i]? |>.map (LExpr.isConstrApp σ.config.factory)).getD false
       | none => false
     let cV := fun (idx : Option Nat) => match idx with
       | some i => (args'[i]? |>.map (LExpr.isCanonicalValue σ.config.factory)).getD false
       | none => false
     if _h: f₁.body.isSome && (f₁.attr.contains Strata.DL.Util.FuncAttr.inline ||
         cA (Strata.DL.Util.FuncAttr.findInlineIfConstr f₁.attr)) then
       match LFunc.computeTypeSubst f₁ op₁ args' with
       | some tySubst =>
         LExpr.eval n' σ (LExpr.substFvarsLifting ((f₁.body.get (by
           have h_and := Bool.and_eq_true_iff.mp _h; exact h_and.1)).applySubst tySubst)
           (f₁.inputs.keys.zip args'))
       | none => e₁
     else
       let new_e := @LExpr.mkApp Tbase.mono e₁.metadata op₁ args'
       if args'.all (LExpr.isCanonicalValue σ.config.factory) ||
           cA (Strata.DL.Util.FuncAttr.findEvalIfConstr f₁.attr) ||
           cV (Strata.DL.Util.FuncAttr.findEvalIfCanonical f₁.attr) then
         match f₁.concreteEval with
         | none => new_e
         | some ceval => match ceval new_e.metadata args' with
           | some e' => LExpr.eval n' σ e'
           | none => new_e
       else new_e).eraseMetadata =
    (let args' := args₂.map (fun a => LExpr.eval n' σ a)
     let cA := fun (idx : Option Nat) => match idx with
       | some i => (args'[i]? |>.map (LExpr.isConstrApp σ.config.factory)).getD false
       | none => false
     let cV := fun (idx : Option Nat) => match idx with
       | some i => (args'[i]? |>.map (LExpr.isCanonicalValue σ.config.factory)).getD false
       | none => false
     if _h: f₁.body.isSome && (f₁.attr.contains Strata.DL.Util.FuncAttr.inline ||
         cA (Strata.DL.Util.FuncAttr.findInlineIfConstr f₁.attr)) then
       match LFunc.computeTypeSubst f₁ op₂ args' with
       | some tySubst =>
         LExpr.eval n' σ (LExpr.substFvarsLifting ((f₁.body.get (by
           have h_and := Bool.and_eq_true_iff.mp _h; exact h_and.1)).applySubst tySubst)
           (f₁.inputs.keys.zip args'))
       | none => e₂
     else
       let new_e := @LExpr.mkApp Tbase.mono e₂.metadata op₂ args'
       if args'.all (LExpr.isCanonicalValue σ.config.factory) ||
           cA (Strata.DL.Util.FuncAttr.findEvalIfConstr f₁.attr) ||
           cV (Strata.DL.Util.FuncAttr.findEvalIfCanonical f₁.attr) then
         match f₁.concreteEval with
         | none => new_e
         | some ceval => match ceval new_e.metadata args' with
           | some e' => LExpr.eval n' σ e'
           | none => new_e
       else new_e).eraseMetadata := by
  -- Step 1: show inline condition is the same for both sides
  have h_inline_cond_eq :
      (f₁.body.isSome && (f₁.attr.contains Strata.DL.Util.FuncAttr.inline ||
        (match Strata.DL.Util.FuncAttr.findInlineIfConstr f₁.attr with
        | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isConstrApp σ.config.factory)).getD false
        | none => false))) =
      (f₁.body.isSome && (f₁.attr.contains Strata.DL.Util.FuncAttr.inline ||
        (match Strata.DL.Util.FuncAttr.findInlineIfConstr f₁.attr with
        | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isConstrApp σ.config.factory)).getD false
        | none => false))) := by
    congr 1; congr 1
    exact h_constrArgAt_eq _
  -- Step 2: show canonical/evalIfConstr/evalIfCanonical condition is the same
  have h_can_cond_eq :
      ((args₁.map (fun a => LExpr.eval n' σ a)).all (LExpr.isCanonicalValue σ.config.factory) ||
        (match Strata.DL.Util.FuncAttr.findEvalIfConstr f₁.attr with
        | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isConstrApp σ.config.factory)).getD false
        | none => false) ||
        (match Strata.DL.Util.FuncAttr.findEvalIfCanonical f₁.attr with
        | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isCanonicalValue σ.config.factory)).getD false
        | none => false)) =
      ((args₂.map (fun a => LExpr.eval n' σ a)).all (LExpr.isCanonicalValue σ.config.factory) ||
        (match Strata.DL.Util.FuncAttr.findEvalIfConstr f₁.attr with
        | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isConstrApp σ.config.factory)).getD false
        | none => false) ||
        (match Strata.DL.Util.FuncAttr.findEvalIfCanonical f₁.attr with
        | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
            (LExpr.isCanonicalValue σ.config.factory)).getD false
        | none => false)) := by
    rw [h_all_canonical, h_constrArgAt_eq, h_canonicalArgAt_eq]
  -- Step 3: unfold and case split
  simp only []
  split
  · -- LHS inline
    rename_i h_il₁
    -- Show RHS also inline
    have h_il₂ := h_il₁; rw [h_inline_cond_eq] at h_il₂
    simp only [dif_pos h_il₂]
    -- Show computeTypeSubst produces the same result on both sides
    have h_tySubst_eq : LFunc.computeTypeSubst f₁ op₁
        (args₁.map (fun a => LExpr.eval n' σ a)) =
      LFunc.computeTypeSubst f₁ op₂
        (args₂.map (fun a => LExpr.eval n' σ a)) :=
      computeTypeSubst_eraseMetadata_congr f₁ op₁ op₂ _ _ h_op_eM h_eval_args_eM
    rw [h_tySubst_eq]
    -- Now both sides have the same match on computeTypeSubst
    split
    · -- some tySubst: both sides eval the substituted body
      apply ih
      exact substFvarsLifting_zip_eraseMetadata_congr _ _ _ _ h_eval_args_eM
    · -- none: both sides return e₁/e₂
      exact _h_eM
  · -- LHS not inline
    rename_i h_nil₁
    have h_nil₂ := h_nil₁; rw [h_inline_cond_eq] at h_nil₂
    simp only [dif_neg h_nil₂]
    -- Now split on canonical/evalIfConstr/evalIfCanonical (LHS is a regular if, not dite)
    split
    · -- LHS canonical
      rename_i h_can₁
      have h_can₂ := h_can_cond_eq ▸ h_can₁
      simp only [if_pos h_can₂]
      cases h_ce : f₁.concreteEval with
      | none =>
        simp only []
        rw [LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp, h_op_eM, h_eval_args_eM]
      | some ceval =>
        simp only []
        -- Use `match` on the ceval results directly
        have h_lfunc_mem := callOfLFunc_func_mem σ.config.factory _ _ _ f₁ false h_call₁
        have h_wf_fn := hWF.lfuncs_wf f₁ h_lfunc_mem
        match h_cv₁ : ceval (LExpr.mkApp e₁.metadata op₁
            (List.map (fun a => LExpr.eval n' σ a) args₁)).metadata
            (List.map (fun a => LExpr.eval n' σ a) args₁),
          h_cv₂ : ceval (LExpr.mkApp e₂.metadata op₂
            (List.map (fun a => LExpr.eval n' σ a) args₂)).metadata
            (List.map (fun a => LExpr.eval n' σ a) args₂) with
        | some e'₁, some e'₂ =>
          simp
          obtain ⟨e'₂', h_cv₂', h_res_eM⟩ :=
            h_wf_fn.concreteEval_eraseMetadata ceval h_ce _ _ _ _ e'₁ h_eval_args_eM h_cv₁
          rw [h_cv₂'] at h_cv₂; cases h_cv₂
          exact ih _ _ h_res_eM
        | some e'₁, none =>
          obtain ⟨e'₂, h_cv₂', _⟩ :=
            h_wf_fn.concreteEval_eraseMetadata ceval h_ce _ _ _ _ e'₁ h_eval_args_eM h_cv₁
          exact absurd (h_cv₂.symm.trans h_cv₂') (by simp)
        | none, some e'₂ =>
          obtain ⟨e'₁, h_cv₁', _⟩ :=
            h_wf_fn.concreteEval_eraseMetadata ceval h_ce _ _ _ _ e'₂ h_eval_args_eM.symm h_cv₂
          exact absurd (h_cv₁.symm.trans h_cv₁') (by simp)
        | none, none =>
          rw [LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp, h_op_eM, h_eval_args_eM]
    · -- LHS not canonical
      rename_i h_ncan₁
      have h_ncan₂ := h_can_cond_eq ▸ h_ncan₁
      simp only [if_neg h_ncan₂]
      rw [LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp, h_op_eM, h_eval_args_eM]

---------------------------------------------------------------------

-- eval is eraseMetadata-invariant: if two expressions have the same eraseMetadata,
-- their eval results also have the same eraseMetadata.
-- This is a key structural property of eval: metadata is only used for provenance
-- tracking and does not affect the computation.
theorem eval_eraseMetadata_invariant
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e₁ e₂ : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.eval n σ e₁).eraseMetadata = (LExpr.eval n σ e₂).eraseMetadata := by
  induction n generalizing e₁ e₂ with
  | zero =>
    -- eval 0 σ e = e
    simp [LExpr.eval]
    exact h_eM
  | succ n' ih =>
    simp only [LExpr.eval]
    -- First check: isCanonicalValue
    rw [isCanonicalValue_eraseMetadata_eq σ.config.factory e₁ e₂ h_eM]
    split
    · -- Both canonical → eval returns the expression unchanged
      exact h_eM
    · -- Not canonical → match on callOfLFunc.
      -- Use callOfLFunc_eraseMetadata_congr to relate the two sides
      have h_congr := callOfLFunc_eraseMetadata_congr σ.config.factory e₁ e₂ false h_eM
      -- Split on callOfLFunc e₁
      split
      · -- callOfLFunc e₁ = some (op₁, args₁, f₁)
        rename_i op₁ args₁ f₁ h_call₁
        -- Transfer to e₂
        have ⟨op₂, args₂, h_call₂, h_args_eM, h_op_eM⟩ :=
          callOfLFunc_some_of_eraseMetadata_eq σ.config.factory _ _ false h_eM _ _ _ h_call₁
        rw [h_call₂]
        -- args.map (eval n' σ) has same eraseMetadata for both sides
        have h_eval_args_eM : (args₁.map (LExpr.eval n' σ)).map LExpr.eraseMetadata =
            (args₂.map (LExpr.eval n' σ)).map LExpr.eraseMetadata := by
          have h_len : args₁.length = args₂.length := by
            have h_len_eq := congrArg List.length h_args_eM; simp at h_len_eq; exact h_len_eq
          apply List.ext_getElem (by simp [h_len])
          intro i h₁ h₂
          simp only [List.getElem_map]
          exact ih _ _ (by
            have h_getElem_eq := congrArg (fun l => l[i]?) h_args_eM
            simp [List.getElem?_map] at h_getElem_eq
            have hi₁ : i < args₁.length := by simp at h₁; exact h₁
            have hi₂ : i < args₂.length := by omega
            simp [hi₁, hi₂] at h_getElem_eq
            exact h_getElem_eq)
        have h_len : args₁.length = args₂.length := by
          have h_len_eq := congrArg List.length h_args_eM; simp at h_len_eq; exact h_len_eq
        have h_eval_getElem_eM : ∀ i (hi₁ : i < args₁.length) (hi₂ : i < args₂.length),
            (LExpr.eval n' σ (args₁.get ⟨i, hi₁⟩)).eraseMetadata =
            (LExpr.eval n' σ (args₂.get ⟨i, hi₂⟩)).eraseMetadata := by
          intro i hi₁ hi₂
          have h_getElem_eq := congrArg (fun l => l[i]?) h_eval_args_eM
          simp [hi₁, hi₂] at h_getElem_eq
          exact h_getElem_eq
        have h_isConstrApp_eq : ∀ i (hi₁ : i < args₁.length) (hi₂ : i < args₂.length),
            LExpr.isConstrApp σ.config.factory (LExpr.eval n' σ (args₁.get ⟨i, hi₁⟩)) =
            LExpr.isConstrApp σ.config.factory (LExpr.eval n' σ (args₂.get ⟨i, hi₂⟩)) :=
          fun i hi₁ hi₂ => isConstrApp_eraseMetadata_eq _ _ _ (h_eval_getElem_eM i hi₁ hi₂)
        have h_constrArgAt_eq : ∀ idx : Option Nat,
            (match idx with
            | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
                (LExpr.isConstrApp σ.config.factory)).getD false
            | none => false) =
            (match idx with
            | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
                (LExpr.isConstrApp σ.config.factory)).getD false
            | none => false) := by
          intro idx
          match idx with
          | none => rfl
          | some i =>
            simp only [List.getElem?_map]
            by_cases hi₁ : i < args₁.length
            · have hi₂ : i < args₂.length := by omega
              simp [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
              exact h_isConstrApp_eq i hi₁ hi₂
            · have hi₂ : ¬(i < args₂.length) := by omega
              simp [List.getElem?_eq_none_iff.mpr (by omega : args₁.length ≤ i)]
              simp [List.getElem?_eq_none_iff.mpr (by omega : args₂.length ≤ i)]
        have h_isCanonicalValue_eq : ∀ i (hi₁ : i < args₁.length) (hi₂ : i < args₂.length),
            LExpr.isCanonicalValue σ.config.factory (LExpr.eval n' σ (args₁.get ⟨i, hi₁⟩)) =
            LExpr.isCanonicalValue σ.config.factory (LExpr.eval n' σ (args₂.get ⟨i, hi₂⟩)) :=
          fun i hi₁ hi₂ => isCanonicalValue_eraseMetadata_eq _ _ _ (h_eval_getElem_eM i hi₁ hi₂)
        have h_canonicalArgAt_eq : ∀ idx : Option Nat,
            (match idx with
            | some i => ((args₁.map (fun a => LExpr.eval n' σ a))[i]? |>.map
                (LExpr.isCanonicalValue σ.config.factory)).getD false
            | none => false) =
            (match idx with
            | some i => ((args₂.map (fun a => LExpr.eval n' σ a))[i]? |>.map
                (LExpr.isCanonicalValue σ.config.factory)).getD false
            | none => false) := by
          intro idx
          match idx with
          | none => rfl
          | some i =>
            simp only [List.getElem?_map]
            by_cases hi₁ : i < args₁.length
            · have hi₂ : i < args₂.length := by omega
              simp [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
              exact h_isCanonicalValue_eq i hi₁ hi₂
            · have hi₂ : ¬(i < args₂.length) := by omega
              simp [List.getElem?_eq_none_iff.mpr (by omega : args₁.length ≤ i)]
              simp [List.getElem?_eq_none_iff.mpr (by omega : args₂.length ≤ i)]
        -- Helper: all canonical
        have h_all_canonical :
            (args₁.map (fun a => LExpr.eval n' σ a)).all (LExpr.isCanonicalValue σ.config.factory) =
            (args₂.map (fun a => LExpr.eval n' σ a)).all (LExpr.isCanonicalValue σ.config.factory) := by
          -- Both lists have the same length and pointwise same isCanonicalValue
          have h_pw : (args₁.map (fun a => LExpr.eval n' σ a)).map
              (LExpr.isCanonicalValue σ.config.factory) =
              (args₂.map (fun a => LExpr.eval n' σ a)).map
              (LExpr.isCanonicalValue σ.config.factory) := by
            apply List.ext_getElem (by simp [h_len])
            intro i h₁ h₂
            simp only [List.getElem_map]
            have hi₁ : i < args₁.length := by simp at h₁; exact h₁
            have hi₂ : i < args₂.length := by omega
            exact isCanonicalValue_eraseMetadata_eq _ _ _ (h_eval_getElem_eM i hi₁ hi₂)
          have h_all_map_eq : ∀ (l : List (LExpr Tbase.mono)),
              l.all (LExpr.isCanonicalValue σ.config.factory) =
              (l.map (LExpr.isCanonicalValue σ.config.factory)).all (fun b => b) := by
            intro l; induction l with
            | nil => simp [List.all]
            | cons hd tl ihtl => simp [List.all, List.map, ihtl]
          rw [h_all_map_eq, h_all_map_eq, h_pw]
        have h_args_eq_eM := h_eval_args_eM
        exact eval_factory_post_eraseMetadata_invariant σ n' hWF f₁
          e₁ e₂ op₁ op₂ args₁ args₂ h_call₁ h_eval_args_eM h_eM h_op_eM
          h_constrArgAt_eq h_canonicalArgAt_eq h_all_canonical ih
      · -- callOfLFunc e₁ = none → evalCore path
        rename_i h_none₁
        have h_none₂ := callOfLFunc_none_of_eraseMetadata_eq σ.config.factory _ _ false h_eM h_none₁
        rw [h_none₂]
        exact evalCore_eraseMetadata_congr n' σ e₁ e₂ h_eM ih

---------------------------------------------------------------------
-- Helper lemma: for the concreteEval factory case. When concreteEval
-- succeeds on evaluated args, we relate the result to original args
-- via the Step relation using eval_fn + concreteEval_eraseMetadata.

private theorem eval_StepStar_factory_ceval
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
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
      ∃ (e' : LExpr Tbase.mono),
        StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
        e'.eraseMetadata = (LExpr.eval n σ e).eraseMetadata) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
      e'.eraseMetadata = (LExpr.eval n σ e'_ceval).eraseMetadata := by
  obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall_op h_call

  let stepped_args := args.map (fun a => (ih a).choose)
  have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
  have h_per_step : ∀ i (hi : i < args.length),
      StepStar σ.config.factory (Scopes.toEnv σ.state)
        (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
  have h_per_eM : ∀ i (hi : i < args.length),
      (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩).eraseMetadata =
        (LExpr.eval n σ (args.get ⟨i, hi⟩)).eraseMetadata := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.2

  obtain ⟨e_stepped, h_step_e, h_eM_stepped⟩ :=
    StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step

  have h_args_eM : stepped_args.map LExpr.eraseMetadata =
      (args.map (LExpr.eval n σ)).map LExpr.eraseMetadata := by
    apply List.ext_getElem (by simp [stepped_args])
    intro i hi1 hi2
    simp only [List.getElem_map]
    have hi_args : i < args.length := by simp [stepped_args] at hi1; exact hi1
    exact h_per_eM i hi_args

  have h_eM_eq : e_stepped.eraseMetadata =
      (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ))).eraseMetadata := by
    rw [h_eM_stepped, LExpr.eraseMetadata_mkApp, h_args_eM]

  have h_call_mkApp : σ.config.factory.callOfLFunc
      (LExpr.mkApp e.metadata op_expr args) = some (op_expr, args, lfunc) := by
    subst h_op_eq
    simp only [Factory.callOfLFunc, getLFuncCall_mkApp_op] at h_call ⊢
    simp only [h_get] at h_call
    exact h_call

  have h_call_eval : σ.config.factory.callOfLFunc
      (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ))) =
      some (op_expr, args.map (LExpr.eval n σ), lfunc) :=
    callOfLFunc_mkApp_op σ.config.factory e.metadata op_expr args
      (args.map (LExpr.eval n σ)) lfunc ⟨m_op, name_op, ty_op, h_op_eq⟩
      h_call_mkApp (by simp)

  obtain ⟨op_s, args_s, h_call_s, h_args_s_eM, _⟩ :=
    callOfLFunc_some_of_eraseMetadata_eq σ.config.factory
      (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ)))
      e_stepped false h_eM_eq.symm op_expr (args.map (LExpr.eval n σ)) lfunc
      h_call_eval

  have h_lfunc_mem := callOfLFunc_func_mem σ.config.factory _ _ _ lfunc false h_call
  have h_wf_fn := hWF.lfuncs_wf lfunc h_lfunc_mem
  obtain ⟨res_s, h_ceval_s, h_res_eM⟩ :=
    h_wf_fn.concreteEval_eraseMetadata ceval h_ceval
      (LExpr.mkApp e.metadata op_expr (args.map (LExpr.eval n σ))).metadata
      e.metadata
      (args.map (LExpr.eval n σ)) args_s e'_ceval
      h_args_s_eM h_ceval_succ

  have h_step_eval : Step σ.config.factory (Scopes.toEnv σ.state) e_stepped res_s :=
    Step.eval_fn e_stepped op_s res_s args_s lfunc ceval h_call_s h_ceval h_ceval_s.symm

  obtain ⟨e_final, h_step_final, h_eM_final⟩ := ih res_s
  refine ⟨e_final, ReflTrans_Transitive _ _ _ _ h_step_e (ReflTrans.step _ _ _ h_step_eval h_step_final), ?_⟩
  rw [h_eM_final]
  exact eval_eraseMetadata_invariant σ res_s e'_ceval n hWF h_res_eM.symm


---------------------------------------------------------------------
-- Main theorem

theorem eval_StepStar
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (e2 : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
    (hEval : e2 = LExpr.eval n σ e) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
      e'.eraseMetadata = e2.eraseMetadata := by
  subst hEval
  unfold StepStar
  induction n generalizing e with
  | zero =>
    exact ⟨e, ReflTrans.refl e, by simp [LExpr.eval]⟩
  | succ n ih =>
    simp only [LExpr.eval]
    split
    · -- Canonical: eval returns e
      rename_i h_canonical
      have h_eval_n : LExpr.eval n σ e = e := by
        cases n with
        | zero => simp [LExpr.eval]
        | succ n' => simp [LExpr.eval, h_canonical]
      obtain ⟨e', hstep, hve⟩ := ih e
      rw [h_eval_n] at hve
      exact ⟨e', hstep, hve⟩
    · rename_i h_not_canonical
      split
      · -- Factory case
        rename_i op_expr args lfunc h_call
        split
        · -- Inline: step args, fire expand_fn, use eval_eraseMetadata_invariant to bridge
          rename_i h_inline
          have h_body_some : lfunc.body.isSome = true := by
            have h_and := Bool.and_eq_true_iff.mp h_inline; exact h_and.1
          obtain ⟨body, h_body_eq⟩ := Option.isSome_iff_exists.mp h_body_some
          -- Split on computeTypeSubst in the eval result
          split
          · -- computeTypeSubst = some tySubst
            rename_i tySubst h_tySubst
            obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall_op h_call
            let stepped_args := args.map (fun a => (ih a).choose)
            have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
            have h_per_step : ∀ i (hi : i < args.length),
                StepStar σ.config.factory (Scopes.toEnv σ.state)
                  (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
              intro i hi; simp [stepped_args]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
            obtain ⟨e_stepped, h_step_e, h_estepped_eM⟩ :=
              StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step
            have h_ref_call : σ.config.factory.callOfLFunc (LExpr.mkApp e.metadata op_expr stepped_args) =
                some (op_expr, stepped_args, lfunc) := by
              apply callOfLFunc_mkApp_op σ.config.factory e.metadata op_expr args stepped_args lfunc
                ⟨m_op, name_op, ty_op, h_op_eq⟩ _ h_stepped_len.symm
              subst h_op_eq
              simp only [Factory.callOfLFunc, getLFuncCall_mkApp_op] at h_call ⊢
              simp only [h_get] at h_call
              exact h_call
            have h_ref_eM : e_stepped.eraseMetadata =
                (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata := by
              rw [h_estepped_eM, LExpr.eraseMetadata_mkApp]
            obtain ⟨op', stepped_args', h_call_stepped, h_args_eM, h_op'_eM⟩ :=
              callOfLFunc_some_of_eraseMetadata_eq σ.config.factory
                (LExpr.mkApp e.metadata op_expr stepped_args) e_stepped false
                h_ref_eM.symm op_expr stepped_args lfunc h_ref_call
            -- Derive computeTypeSubst for stepped_args' via eraseMetadata-congr
            have h_per_eM : ∀ i (hi : i < args.length),
                (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩).eraseMetadata =
                  (LExpr.eval n σ (args.get ⟨i, hi⟩)).eraseMetadata := by
              intro i hi; simp [stepped_args]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.2
            have h_vals_eM : stepped_args'.map LExpr.eraseMetadata =
                (args.map (LExpr.eval n σ)).map LExpr.eraseMetadata := by
              rw [← h_args_eM]
              apply List.ext_getElem (by simp [stepped_args])
              intro i hi1 hi2
              simp only [List.getElem_map]
              have hi_args : i < args.length := by simp [stepped_args] at hi1; exact hi1
              exact h_per_eM i hi_args
            have h_tySubst_stepped :
                LFunc.computeTypeSubst lfunc op' stepped_args' = some tySubst := by
              rw [← h_tySubst]
              exact computeTypeSubst_eraseMetadata_congr lfunc op' op_expr _ _
                h_op'_eM.symm h_vals_eM
            have h_expand : Step σ.config.factory (Scopes.toEnv σ.state) e_stepped
                (LExpr.substFvarsLifting (body.applySubst tySubst)
                  (lfunc.inputs.keys.zip stepped_args')) :=
              Step.expand_fn e_stepped op' body _ stepped_args' lfunc tySubst
                h_call_stepped h_body_eq h_tySubst_stepped rfl
            obtain ⟨e'_s, h_step_s, h_ve_s⟩ :=
              ih (LExpr.substFvarsLifting (body.applySubst tySubst)
                (lfunc.inputs.keys.zip stepped_args'))
            refine ⟨e'_s, ReflTrans_Transitive _ _ _ _ h_step_e
              (ReflTrans.step _ _ _ h_expand h_step_s), ?_⟩
            have h_subst_eM :
                (LExpr.substFvarsLifting (body.applySubst tySubst)
                  (lfunc.inputs.keys.zip stepped_args')).eraseMetadata =
                (LExpr.substFvarsLifting (body.applySubst tySubst)
                  (lfunc.inputs.keys.zip (args.map (LExpr.eval n σ)))).eraseMetadata :=
              substFvarsLifting_zip_eraseMetadata_congr _ _ _ _ h_vals_eM
            have h_body_get : lfunc.body.get (by simp [h_body_eq]) = body := by
              simp [h_body_eq]
            show _ = (LExpr.eval n σ _).eraseMetadata
            rw [h_body_get, show (fun a => LExpr.eval n σ a) = LExpr.eval n σ from rfl]
            exact h_ve_s.trans (eval_eraseMetadata_invariant σ _ _ n hWF h_subst_eM)
          · -- computeTypeSubst = none: eval returns e unchanged
            exact ⟨e, ReflTrans.refl e, rfl⟩
        · -- Non-inline
          rename_i h_not_inline
          split
          · rename_i h_canonical_args
            split
            · -- No ceval: terminal
              rename_i h_no_ceval
              exact eval_StepStar_factory_terminal σ e n op_expr args lfunc h_call ih
            · -- ceval exists
              rename_i ceval h_ceval
              split
              · -- ceval succeeds: eval = eval n σ e'_ceval
                rename_i e'_ceval h_ceval_succ
                exact eval_StepStar_factory_ceval σ e n hWF
                  op_expr args lfunc h_call ceval h_ceval e'_ceval h_ceval_succ ih
              · -- ceval fails: terminal
                rename_i h_ceval_fail
                exact eval_StepStar_factory_terminal σ e n op_expr args lfunc h_call ih
          · -- Symbolic args: terminal
            rename_i h_symbolic
            exact eval_StepStar_factory_terminal σ e n op_expr args lfunc h_call ih
      · -- evalCore case: case analysis on e
        rename_i h_no_call
        match e, h_not_canonical, h_no_call with
        | .const m c, h_nc, _ =>
          exact absurd (by simp [LExpr.isCanonicalValue] :
            LExpr.isCanonicalValue σ.config.factory (.const m c) = true) h_nc
        | .op m fn ty, _, _ =>
          refine ⟨_, ReflTrans.refl _, ?_⟩
          simp only [LExpr.evalCore]
        | .bvar m i, _, _ =>
          refine ⟨_, ReflTrans.refl _, ?_⟩
          simp only [LExpr.evalCore]
        | .fvar m x ty, _, _ =>
          simp only [LExpr.evalCore]
          cases h_find : Maps.find? σ.state x with
          | none =>
            have h_findD : Maps.findD σ.state x (ty, LExpr.fvar m x ty) = (ty, LExpr.fvar m x ty) :=
              Maps.findD_find?_none σ.state x _ h_find
            rw [h_findD]
            exact ⟨_, ReflTrans.refl _, rfl⟩
          | some p =>
            have h_findD : Maps.findD σ.state x (ty, LExpr.fvar m x ty) = p :=
              Maps.findD_find?_some σ.state x _ p h_find
            rw [h_findD]
            have h_toEnv : Scopes.toEnv σ.state x = some p.snd := by
              simp [Scopes.toEnv, h_find]
            have h_step : Step σ.config.factory (Scopes.toEnv σ.state) (.fvar m x ty) p.snd :=
              Step.expand_fvar x p.snd h_toEnv
            exact ⟨p.snd, ReflTrans.step _ p.snd _ h_step (ReflTrans.refl _), rfl⟩
        | .abs m name ty body, _, _ =>
          -- evalCore (.abs) = substFvarsFromState σ (.abs). Step abs to its subst form.
          simp only [LExpr.evalCore]
          exact ⟨LExpr.substFvarsFromState σ (.abs m name ty body),
            StepStar_to_substFvarsFromState_abs σ m name ty body, rfl⟩
        | .quant m qk name ty tr body, _, _ =>
          simp only [LExpr.evalCore]
          exact ⟨LExpr.substFvarsFromState σ (.quant m qk name ty tr body),
            StepStar_to_substFvarsFromState_quant σ m qk name ty tr body, rfl⟩
        | .app m e1 e2, _, _ =>
          obtain ⟨s1, hs1, hv1⟩ := ih e1
          obtain ⟨s2, hs2, hv2⟩ := ih e2
          have h_step_app : StepStar σ.config.factory (Scopes.toEnv σ.state)
              (.app m e1 e2) (.app m s1 s2) :=
            ReflTrans_Transitive _ _ _ _ (StepStar_app_fn _ _ e1 s1 e2 m hs1)
              (StepStar_app_arg _ _ s1 e2 s2 m hs2)
          simp only [LExpr.evalCore, LExpr.evalApp]
          split
          · -- Beta case: eval n σ e1 = .abs mAbs name ty body_e1'
            -- EMEquiv s1 (.abs ...) → s1 IS an abs → fire beta
            rename_i mAbs name ty body_e1' h_eval_abs
            -- Extract abs structure from hv1 before the split complicates things
            -- hv1 : s1.eraseMetadata = (eval n σ e1).eraseMetadata, and h_eval_abs : eval n σ e1 = .abs ...
            -- So hv1 : s1.eraseMetadata = (.abs mAbs name ty body_e1').eraseMetadata
            -- s1 must be .abs m2 name ty body_s1
            have h_s1_abs : ∃ m2 body_s1,
                s1 = .abs m2 name ty body_s1 ∧ body_s1.eraseMetadata = body_e1'.eraseMetadata := by
              rw [h_eval_abs] at hv1
              simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at hv1
              cases s1 <;> simp [LExpr.replaceMetadata] at hv1 <;> try contradiction
              rename_i m2 name2 ty2 body2
              have ⟨hn, hty, hb⟩ := hv1; subst hn hty
              exact ⟨_, _, rfl, hb⟩
            obtain ⟨m2, body_s1, h_s1_eq, h_eM_body⟩ := h_s1_abs
            subst h_s1_eq
            -- Fire beta
            have h_beta : Step σ.config.factory (Scopes.toEnv σ.state)
                (.app m (.abs m2 name ty body_s1) s2)
                (LExpr.subst (fun _ => s2) body_s1) :=
              Step.beta body_s1 s2 _ rfl
            have h_steps_to_beta := ReflTrans_Transitive _ _ _ _ h_step_app
              (ReflTrans.step _ _ _ h_beta (ReflTrans.refl _))
            -- The evalApp with .abs: splits on eqModuloMeta
            split
            · exact ⟨.app m e1 e2, ReflTrans.refl _, rfl⟩
            · rename_i h_not_eqmod e'_eval h_not_eqmod_bool
              obtain ⟨e'', hstep'', hve''⟩ := ih (LExpr.subst (fun _ => s2) body_s1)
              refine ⟨e'', ReflTrans_Transitive _ _ _ _ h_steps_to_beta hstep'', ?_⟩
              have h_subst_eM : (LExpr.subst (fun _ => s2) body_s1).eraseMetadata =
                  (LExpr.subst (fun m₂ =>
                    LExpr.replaceMetadata1 (LExpr.mergeMetadataForSubst mAbs (LExpr.eval n σ e2).metadata m₂)
                      (LExpr.eval n σ e2)) body_e1').eraseMetadata := by
                simp only [LExpr.subst]
                exact substK_eraseMetadata_congr₂ body_s1 body_e1' 0 _ _
                  h_eM_body
                  (fun m₁ m₂ => by
                    have h_rp1 : ∀ (m' : Tbase.Metadata) (e' : LExpr Tbase.mono),
                        (LExpr.replaceMetadata1 m' e').eraseMetadata = e'.eraseMetadata := by
                      intro m' e'; cases e' <;> simp [LExpr.replaceMetadata1, LExpr.eraseMetadata, LExpr.replaceMetadata]
                    rw [h_rp1]
                    exact hv2)
              have h_eval_eM := eval_eraseMetadata_invariant σ
                (LExpr.subst (fun _ => s2) body_s1)
                (LExpr.subst (fun m₂ =>
                    LExpr.replaceMetadata1 (LExpr.mergeMetadataForSubst mAbs (LExpr.eval n σ e2).metadata m₂)
                      (LExpr.eval n σ e2)) body_e1')
                n hWF h_subst_eM
              exact hve''.trans h_eval_eM
          · rename_i h_not_abs
            split
            · exact ⟨.app m e1 e2, ReflTrans.refl _, rfl⟩
            · rename_i h_not_eqmod e'_app
              obtain ⟨e'', hstep'', hve''⟩ := ih (.app m s1 s2)
              refine ⟨e'', ReflTrans_Transitive _ _ _ _ h_step_app hstep'', ?_⟩
              have h_app_eM : (LExpr.app m s1 s2).eraseMetadata =
                  (LExpr.app (LExpr.app m e1 e2 : LExpr Tbase.mono).metadata (LExpr.eval n σ e1) (LExpr.eval n σ e2)).eraseMetadata := by
                simp [LExpr.eraseMetadata]
                exact eraseMetadata_app_congr hv1 hv2
              have h_eval_eM := eval_eraseMetadata_invariant σ
                (LExpr.app m s1 s2)
                (LExpr.app (LExpr.app m e1 e2 : LExpr Tbase.mono).metadata (LExpr.eval n σ e1) (LExpr.eval n σ e2))
                n hWF h_app_eM
              exact hve''.trans h_eval_eM
        | .eq m e1 e2, _, _ =>
          obtain ⟨s1, hs1, hv1⟩ := ih e1
          obtain ⟨s2, hs2, hv2⟩ := ih e2
          simp only [LExpr.evalCore, LExpr.evalEq]
          split
          · -- eql resolves to some b
            rename_i b h_eql_some
            have h_eql_s : LExpr.eql σ.config.factory s1 s2 = some b := by
              rw [eql_eraseMetadata_eq σ.config.factory s1 s2
                (LExpr.eval n σ e1) (LExpr.eval n σ e2)
                hv1 hv2]
              exact h_eql_some
            have h_step_eq := ReflTrans_Transitive _ _ _ _
              (StepStar_eq_lhs_pres _ _ e1 s1 e2 m hs1)
              (StepStar_eq_rhs_pres _ _ s1 e2 s2 m hs2)
            cases b with
            | true =>
              exact ⟨.const m (.boolConst true),
                ReflTrans_Transitive _ _ _ _ h_step_eq
                  (ReflTrans.step _ _ _ (Step.eq_reduce_true s1 s2 h_eql_s) (ReflTrans.refl _)),
                rfl⟩
            | false =>
              exact ⟨.const m (.boolConst false),
                ReflTrans_Transitive _ _ _ _ h_step_eq
                  (ReflTrans.step _ _ _ (Step.eq_reduce_false s1 s2 h_eql_s) (ReflTrans.refl _)),
                rfl⟩
          · -- eql returns none → .eq m (eval e1) (eval e2)
            rename_i h_eql_none
            exact ⟨.eq m s1 s2,
              ReflTrans_Transitive _ _ _ _ (StepStar_eq_lhs_pres _ _ e1 s1 e2 m hs1)
                (StepStar_eq_rhs_pres _ _ s1 e2 s2 m hs2),
              by simp [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact ⟨hv1, hv2⟩⟩
        | .ite m c t f, _, _ =>
          obtain ⟨sc, hsc, hvc⟩ := ih c
          simp only [LExpr.evalCore, LExpr.evalIte]
          split
          · -- condition resolves to true → eval t
            rename_i mc_true h_eval_c_true
            rw [h_eval_c_true] at hvc
            obtain ⟨mc', h_step_to_true⟩ :=
              step_to_const_via_IH σ c sc mc_true (.boolConst true) hsc hvc
            obtain ⟨st, hst_step, hvt⟩ := ih t
            refine ⟨st, ?_, hvt⟩
            exact ReflTrans_Transitive _ _ _ _
              (StepStar_ite_cond_pres _ _ c (.const mc' (.boolConst true)) t f m h_step_to_true)
              (ReflTrans.step _ t _ (Step.ite_reduce_then (m := m) (mc := mc') t f) hst_step)
          · -- condition resolves to false → eval f
            rename_i mc_false h_eval_c_false
            rw [h_eval_c_false] at hvc
            obtain ⟨mc', h_step_to_false⟩ :=
              step_to_const_via_IH σ c sc mc_false (.boolConst false) hsc hvc
            obtain ⟨sf, hsf_step, hvf⟩ := ih f
            refine ⟨sf, ?_, hvf⟩
            exact ReflTrans_Transitive _ _ _ _
              (StepStar_ite_cond_pres _ _ c (.const mc' (.boolConst false)) t f m h_step_to_false)
              (ReflTrans.step _ f _ (Step.ite_reduce_else (m := m) (mc := mc') t f) hsf_step)
          · -- condition unresolved → .ite m (eval c) (eval t) (eval f)
            rename_i h_not_true h_not_false
            obtain ⟨st, hst, hvt⟩ := ih t
            obtain ⟨sf, hsf, hvf⟩ := ih f
            refine ⟨.ite m sc st sf,
              ReflTrans_Transitive _ _ _ _ (StepStar_ite_cond_pres _ _ c sc t f m hsc)
                (ReflTrans_Transitive _ _ _ _ (StepStar_ite_then_pres _ _ sc t st f m hst)
                  (StepStar_ite_else_pres _ _ sc st f sf m hsf)), ?_⟩
            show (LExpr.ite m sc st sf).eraseMetadata = (LExpr.ite m (LExpr.eval n σ c) (LExpr.eval n σ t) (LExpr.eval n σ f)).eraseMetadata
            simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]
            exact congr (congr (congr rfl hvc) hvt) hvf

end -- public section
end Lambda
