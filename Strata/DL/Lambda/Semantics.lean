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

-- Canonical values are normal forms: no Step rule can fire on them.
-- Key insight: `isCanonicalValue` uses `callOfLFunc F e true` (allowing partial
-- application), while `Step.expand_fn`/`eval_fn` use `callOfLFunc F e` (requiring
-- full arity). A canonical partial application has `args.length < inputs.length`,
-- so full-arity `callOfLFunc` returns `none`.
-- For `reduce_1`/`reduce_2`: all args of a canonical value are themselves
-- canonical, so by induction they don't step.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem canonical_value_not_step
    (F : @Factory Tbase) (rf : Env Tbase)
    (e : LExpr Tbase.mono)
    (hc : LExpr.isCanonicalValue F e = true) :
    ∀ e', ¬ Step F rf e e' := by
  -- Proof sketch: by well-founded induction on e.sizeOf, case split on Step.
  -- - fvar/ite/eq: isCanonicalValue returns false → contradiction
  -- - beta: head is abs not .op → callOfLFunc returns none → contradiction
  -- - reduce_1/reduce_2: sub-expression is canonical (recursive check) → by IH doesn't step
  -- - expand_fn/eval_fn: callOfLFunc F e (false) requires full arity,
  --   but isCanonicalValue uses callOfLFunc F e true with partial arity.
  --   Canonical means isConstr || args.length < inputs.length,
  --   so full-arity callOfLFunc returns none → contradiction.
  sorry

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
@[expose] def StepStar (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop :=
  ReflTrans (Step F rf)

/--
Value equivalence for eval/step correspondence. Two expressions are
`ValEquiv` when they have the same structure modulo metadata, except that
abs/quant bodies only need to be *joinable* under `StepStar` — i.e.,
both bodies can step to a common expression.

This handles the "frozen internals" problem: bounded-fuel eval may freeze
partially-reduced values inside canonical abs/quant, while StepStar may
freeze a different partial evaluation. Joinability captures the fact that
both are on the same reduction path.
-/
inductive ValEquiv (F : @Factory Tbase) (rf : Env Tbase)
    : LExpr Tbase.mono → LExpr Tbase.mono → Prop where
| const : ValEquiv F rf (.const m₁ c) (.const m₂ c)
| op : ValEquiv F rf (.op m₁ n t) (.op m₂ n t)
| bvar : ValEquiv F rf (.bvar m₁ i) (.bvar m₂ i)
| fvar : ValEquiv F rf (.fvar m₁ x t) (.fvar m₂ x t)
| app : ValEquiv F rf f₁ f₂ → ValEquiv F rf a₁ a₂ →
    ValEquiv F rf (.app m₁ f₁ a₁) (.app m₂ f₂ a₂)
| abs : (∃ e, ReflTrans (Step F rf) b₁ e ∧ ReflTrans (Step F rf) b₂ e) →
    ValEquiv F rf (.abs m₁ n t b₁) (.abs m₂ n t b₂)
| quant :
    (∃ et, ReflTrans (Step F rf) t₁ et ∧ ReflTrans (Step F rf) t₂ et) →
    (∃ eb, ReflTrans (Step F rf) b₁ eb ∧ ReflTrans (Step F rf) b₂ eb) →
    ValEquiv F rf (.quant m₁ qk n ty t₁ b₁) (.quant m₂ qk n ty t₂ b₂)
| ite : ValEquiv F rf c₁ c₂ → ValEquiv F rf t₁ t₂ → ValEquiv F rf f₁ f₂ →
    ValEquiv F rf (.ite m₁ c₁ t₁ f₁) (.ite m₂ c₂ t₂ f₂)
| eq : ValEquiv F rf l₁ l₂ → ValEquiv F rf r₁ r₂ →
    ValEquiv F rf (.eq m₁ l₁ r₁) (.eq m₂ l₂ r₂)

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem ValEquiv.refl (F : @Factory Tbase) (rf : Env Tbase) (e : LExpr Tbase.mono) :
    ValEquiv F rf e e := by
  induction e with
  | const => exact .const
  | op => exact .op
  | bvar => exact .bvar
  | fvar => exact .fvar
  | app _ _ _ ih1 ih2 => exact .app ih1 ih2
  | abs _ _ _ _ ih => exact .abs ⟨_, ReflTrans.refl _, ReflTrans.refl _⟩
  | quant _ _ _ _ _ _ ih1 ih2 =>
    exact .quant ⟨_, ReflTrans.refl _, ReflTrans.refl _⟩ ⟨_, ReflTrans.refl _, ReflTrans.refl _⟩
  | ite _ _ _ _ ih1 ih2 ih3 => exact .ite ih1 ih2 ih3
  | eq _ _ _ ih1 ih2 => exact .eq ih1 ih2

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

---------------------------------------------------------------------
-- StepStar congruence through substFvar/substFvars.
-- If a →* a', then substFvar body x a →* substFvar body x a'.
-- Provable by induction on body using Step's congruence rules
-- (reduce_1/2, ite_reduce_*, eq_reduce_*). The abs/quant cases
-- require a Step rule for stepping inside binders (which doesn't
-- exist), so those cases are left as sorry.

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_substFvar (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono) (fr : Tbase.Identifier)
    (a a' : LExpr Tbase.mono)
    (h : ReflTrans (Step F rf) a a') :
    ReflTrans (Step F rf) (LExpr.substFvar body fr a) (LExpr.substFvar body fr a') := by
  sorry

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem StepStar_substFvars (F : @Factory Tbase) (rf : Env Tbase)
    (body : LExpr Tbase.mono)
    (sm sm' : Map Tbase.Identifier (LExpr Tbase.mono))
    (h_keys : sm.map Prod.fst = sm'.map Prod.fst)
    (h_vals : ∀ k v v', List.Mem (k, v) sm → List.Mem (k, v') sm' →
      ReflTrans (Step F rf) v v') :
    ReflTrans (Step F rf) (LExpr.substFvars body sm) (LExpr.substFvars body sm') := by
  sorry

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
    exact ⟨e, ReflTrans.refl e, by simp [LExpr.eval]; exact ValEquiv.refl _ _ _⟩
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
            sorry -- keys of zip are the same when value lists have equal length
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
        · -- const/op/bvar: e' = e, both sides are the same
          exact ⟨_, ReflTrans.refl _, ValEquiv.refl _ _ _⟩
        · exact ⟨_, ReflTrans.refl _, ValEquiv.refl _ _ _⟩
        · exact ⟨_, ReflTrans.refl _, ValEquiv.refl _ _ _⟩
        · -- fvar m x ty
          rename_i m x ty
          cases hfind : σ.state.find? x with
          | none =>
            have hD := Maps_findD_find?_none σ.state x (ty, LExpr.fvar m x ty) hfind
            exact ⟨.fvar m x ty, ReflTrans.refl _, by rw [hD]; exact ValEquiv.refl _ _ _⟩
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
        · -- abs: eval returns substFvarsFromState σ (abs ...).
          -- Need ValEquiv of substFvarsFromState σ (abs ...) with
          -- substFvarsFromState σ (substFvarsFromState σ (abs ...)).
          -- By ValEquiv.abs, need joinability of bodies. Both bodies are
          -- reachable from the original via fvar expansion (StepStar).
          sorry
        · -- quant: same as abs
          sorry
        · sorry -- app: requires nested induction on expression structure
        · sorry -- eq: requires nested induction on expression structure
        · sorry -- ite: requires nested induction on expression structure

end -- public section
end Lambda
