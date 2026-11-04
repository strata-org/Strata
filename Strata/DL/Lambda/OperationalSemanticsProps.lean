/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Lambda.OperationalSemantics
import all Strata.DL.Lambda.OperationalSemantics

import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprProps
import all Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.FactoryProps

/-!
# Properties of Lambda operational semantics

This module contains normal-form, closure-lifting, substitution, factory-call,
and metadata-insensitivity lemmas used to reason about `Step` and `StepStar`.
Evaluator-specific top-level theorems live in `LExprEvalProps` and
`LExprEvalSound`.
-/

namespace Lambda

open Std (ToFormat Format format)

public section

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]

open Lambda

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
/-- Beta-reduction behavior of `have`-bindings: `mkHave m name ty value body`
    steps to `body` with the bound variable substituted by `value`. -/
theorem LExpr.mkHave_beta (F : @Factory Tbase) (rf : Env Tbase)
    (m : Tbase.Metadata) (name : String) (ty : Option LMonoTy)
    (value body : LExpr Tbase.mono) :
    Step F rf (LExpr.mkHave m name ty value body) (LExpr.subst (fun _ => value) body) := by
  unfold LExpr.mkHave
  exact Step.beta body value _ rfl

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem step_const_stuck:
  ∀ (F:@Factory Tbase) r x e,
  ¬ Step F r (.const m x) e := by
  intros
  intro H
  contradiction

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem ReflTrans_stuck {e e' : LExpr Tbase.mono}
    (h : ReflTrans (Step F rf) e e')
    (h_stuck : ∀ e'', ¬ Step F rf e e'') :
    e = e' := by
  cases h with
  | refl => rfl
  | step _ b _ hab _ => exact absurd hab (h_stuck b)

-- value_not_step is proved after the helper lemmas below.

---------------------------------------------------------------------

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_app_fn (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf e1 e1') :
    StepStar F rf (.app m e1 e2) (.app m e1' e2) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.app m y e2) _
      (Step.reduce_1 (m' := m) x y e2 hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
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

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_ite_cond_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c c' t f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf c c') :
    StepStar F rf (.ite m c t f) (.ite m c' t f) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m y t f) _
      (Step.ite_reduce_cond (m' := m) x y t f hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_ite_then_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c t t' f : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf t t') :
    StepStar F rf (.ite m c t f) (.ite m c t' f) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m c y f) _
      (Step.ite_reduce_then_branch (m' := m) c x y f hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_ite_else_pres (F : @Factory Tbase) (rf : Env Tbase)
    (c t f f' : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf f f') :
    StepStar F rf (.ite m c t f) (.ite m c t f') := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.ite m c t y) _
      (Step.ite_reduce_else_branch (m' := m) c t x y hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_eq_lhs_pres (F : @Factory Tbase) (rf : Env Tbase)
    (e1 e1' e2 : LExpr Tbase.mono) (m : Tbase.Metadata)
    (h : StepStar F rf e1 e1') :
    StepStar F rf (.eq m e1 e2) (.eq m e1' e2) := by
  unfold StepStar at *; induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih =>
    exact ReflTrans.step _ (.eq m y e2) _
      (Step.eq_reduce_lhs (m' := m) x y e2 hxy) ih

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_eq_rhs_pres (F : @Factory Tbase) (rf : Env Tbase)
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
theorem getLFuncCall_go_eraseMetadata
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
theorem getLFuncCall_mkApp_op
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
theorem callOfLFunc_mkApp_op
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
theorem getLFuncCall_go_substFvars
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
theorem callOfLFunc_getLFuncCall_op
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
-- Helpers for value_not_step

-- Helper: if callOfLFunc with partial app returns (op, args, f) with the
-- value condition (isConstr || blt), and callOfLFunc with full arity
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

-- Helper: if `.app m e1 e2` is a value, then `e1` is also a value.
-- Needed for the `reduce_1` case: stepping the function part of a value app.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem isValue_app_left
    (F : @Factory Tbase) (m : Tbase.Metadata)
    (e1 e2 : LExpr Tbase.mono)
    (hc : LExpr.isValue F (.app m e1 e2) = true) :
    LExpr.isValue F e1 = true := by
  -- The .app case of isValue goes to the callOfLFunc branch.
  -- Extract the callOfLFunc result from hc.
  unfold LExpr.isValue at hc
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
          -- isValue F (.op m2 fn2 ty2)
          -- callOfLFunc F (.op ..) true uses same factory function, arity 0 ≤ inputs.length
          -- For .op, isValue goes to callOfLFunc branch with 0 args
          -- callOfLFunc F (.op ..) true: getLFuncCall returns (.op .., [])
          -- then getFactoryLFunc succeeds (h_gf), ble 0 inputs.length = true
          -- Result: (isConstr || blt 0 inputs.length) && [].all .. which simplifies
          have h_cv : Factory.callOfLFunc F (.op m_op name_op ty_op) (allowPartialApp := true)
              = some (.op m_op name_op ty_op, [], func) := by
            simp only [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go, h_gf]
            have h_ble : Nat.ble 0 func.inputs.length = true := by simp [Nat.ble_eq]
            simp [h_ble]
          unfold LExpr.isValue
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
          unfold LExpr.isValue
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
              have h_all' : (inner ++ [e1'', e2]).all (LExpr.isValue F) = true := by
                rw [show (inner ++ [e1'', e2]).all (LExpr.isValue F) =
                    ((inner ++ [e1'', e2]).attach.map (fun ⟨x, _⟩ => LExpr.isValue F x)).all id
                  from by simp [List.all_map]]
                exact h_all
              -- Now derive the goal
              suffices h_suff : (inner ++ [e1'']).all (LExpr.isValue F) = true by
                rw [show (inner ++ [e1'']).all (LExpr.isValue F) =
                    ((inner ++ [e1'']).attach.map (fun ⟨x, _⟩ => LExpr.isValue F x)).all id
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

-- Helper: extract `isValue F x = true` for `x ∈ args` from the
-- `all` condition in `isValue`.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
private theorem isValue_args_all
    (F : @Factory Tbase) (args : List (LExpr Tbase.mono))
    (h_all : args.all (LExpr.isValue F) = true)
    (x : LExpr Tbase.mono) (hx : x ∈ args) :
    LExpr.isValue F x = true := by
  rw [List.all_eq_true] at h_all
  exact h_all x hx


omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
/-- Values have no free variables. -/
theorem isValue_getVars_nil
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (hc : LExpr.isValue F e = true) :
    LExpr.LExpr.getVars e = [] := by
  suffices h : ∀ (sz : Nat) (e : LExpr Tbase.mono),
      e.sizeOf ≤ sz → LExpr.isValue F e = true →
      LExpr.LExpr.getVars e = [] from
    h e.sizeOf e (Nat.le_refl _) hc
  intro sz; induction sz with
  | zero =>
    intro e hsz _
    exact absurd hsz (by have h_pos := LExpr.sizeOf_pos e; omega)
  | succ sz ih =>
    intro e hsz hc
    cases e with
    | const => rfl
    | bvar => rfl
    | op => rfl
    | fvar =>
      simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
    | abs m n ty body =>
      simp [LExpr.LExpr.getVars]
      have h_closed : LExpr.closed (.abs m n ty body) = true := by
        simp [LExpr.isValue] at hc; exact hc
      have h_body_closed : LExpr.closed body = true := by
        simp [LExpr.closed, LExpr.freeVars] at h_closed ⊢; exact h_closed
      exact closed_implies_getVars_nil body h_body_closed
    | quant m qk n ty tr body =>
      have h_closed : LExpr.closed (.quant m qk n ty tr body) = true := by
        simp [LExpr.isValue] at hc; exact hc
      exact closed_implies_getVars_nil (.quant m qk n ty tr body) h_closed
    | app m e1 e2 =>
      simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff]
      have hc_app := hc
      simp [LExpr.isValue] at hc
      split at hc
      · rename_i op args f h_call
        simp only [Bool.and_eq_true] at hc
        obtain ⟨h_cond, h_all⟩ := hc
        have h_e1_can : LExpr.isValue F e1 = true :=
          isValue_app_left F m e1 e2 hc_app
        have h_mem : e2 ∈ args := callOfLFunc_app_arg_mem F e1 e2 m op args f _ h_call
        have h_e2_can : LExpr.isValue F e2 = true :=
          isValue_args_all F args h_all e2 h_mem
        have h_sz_e1 : e1.sizeOf < (LExpr.app m e1 e2).sizeOf := by
          simp [LExpr.sizeOf]; omega
        have h_sz_e2 : e2.sizeOf < (LExpr.app m e1 e2).sizeOf := by
          simp [LExpr.sizeOf]; omega
        constructor
        · exact ih e1 (by omega) h_e1_can
        · exact ih e2 (by omega) h_e2_can
      · simp at hc
    | ite =>
      simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
    | eq =>
      simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc

-- Values are normal forms: no Step rule can fire on them.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem value_not_step
    (F : @Factory Tbase) (rf : Env Tbase)
    (e : LExpr Tbase.mono)
    (hWF : FactoryWF F)
    (hc : LExpr.isValue F e = true) :
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
    simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | ite =>
    intro e' hstep
    simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | eq =>
    intro e' hstep
    simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
  | abs _ _ _ body ih_body =>
    intro e' hstep
    -- An abstraction that is a value is closed → freeVars body = []
    simp [LExpr.isValue] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | abs_subst_fvars _ _ h_fv =>
      have h_fvs : LExpr.freeVars body = [] := by
        simp [LExpr.closed, List.isEmpty_iff] at hc; exact hc
      simp [h_fvs] at h_fv
  | quant _ _ _ _ tr body ih_tr ih_body =>
    intro e' hstep
    simp [LExpr.isValue] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | quant_subst_fvars_body _ _ _ h_fv =>
      simp [LExpr.closed, LExpr.freeVars, List.isEmpty_iff] at hc
      simp [hc.2] at h_fv
    | quant_subst_fvars_trigger _ _ _ h_fv =>
      simp [LExpr.closed, LExpr.freeVars, List.isEmpty_iff] at hc
      simp [hc.1] at h_fv
  | op =>
    intro e' hstep
    simp [LExpr.isValue] at hc
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
    simp [LExpr.isValue] at hc
    cases hstep with
    | beta _ _ _ =>
      simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at hc
    | reduce_2 _ _ e2' h_step_e2 =>
      split at hc
      · rename_i op args f h_call
        simp only [Bool.and_eq_true] at hc
        have h_mem := callOfLFunc_app_arg_mem F e1 e2 m_app op args f _ h_call
        have h_e2_can := isValue_args_all F args hc.2 e2 h_mem
        exact ih2 h_e2_can e2' h_step_e2
      · simp at hc
    | reduce_1 _ e1' _ h_step_e1 =>
      have h_e1_can : LExpr.isValue F e1 = true := by
        apply isValue_app_left F m_app e1 e2
        simp [LExpr.isValue]
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
theorem eraseMetadata_app_congr
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
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem StepStar_getLFuncCall_args
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
      grind
    obtain ⟨e_inner', h_step_inner, h_eq_inner⟩ :=
      StepStar_getLFuncCall_args e_inner op inner_args (args'.take inner_args.length)
        h_get_inner h_ia'_len h_inner_steps
    -- Step a1 and a2
    have h_args_len : args.length = inner_args.length + 2 := by rw [h_split]; simp
    have h_step_a1 : StepStar F rf a1 a1' := by
      have h1 := h_steps inner_args.length (by omega)
      grind
    have h_step_a2 : StepStar F rf a2 a2' := by
      have h1 := h_steps (inner_args.length + 1) (by omega)
      grind
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
-- getLFuncCall.go is eraseMetadata-invariant: if e₁.eM = e₂.eM and acc₁.map eM = acc₂.map eM,
-- then getLFuncCall.go e₁ acc₁ and getLFuncCall.go e₂ acc₂ produce results with the same eM.
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
theorem getLFuncCall_eraseMetadata_congr
    (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    (getLFuncCall e₁).fst.eraseMetadata = (getLFuncCall e₂).fst.eraseMetadata ∧
    (getLFuncCall e₁).snd.map LExpr.eraseMetadata = (getLFuncCall e₂).snd.map LExpr.eraseMetadata := by
  unfold getLFuncCall
  exact getLFuncCall_go_eraseMetadata_congr e₁ e₂ [] [] h_eM rfl

-- callOfLFunc is eraseMetadata-invariant
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
theorem callOfLFunc_eraseMetadata_congr
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
theorem callOfLFunc_none_of_eraseMetadata_eq
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
theorem callOfLFunc_some_of_eraseMetadata_eq
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
theorem eql_eraseMetadata_eq
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
  -- Cases 2-7: For each, use EMEquiv to decompose e₁'/e₂', then show the same eql branch fires.
  -- The key trick: rewrite h_not_eqmod BEFORE cases to keep it in a usable form.
  -- Case 2: const/const
  · rename_i h_not_eqmod _ _
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm']
  -- Case 3: abs/abs ty mismatch
  · rename_i h_not_eqmod h_ty_ne _
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm', h_ty_ne]
  -- Case 4: abs/abs closed → recursive eql on varOpen
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
  -- Case 5: abs/abs not closed
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
  -- Case 6: const/abs
  · rename_i h_not_eqmod
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm']
  -- Case 7: abs/const
  · rename_i h_not_eqmod
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; assumption
    have hv₁ := EMEquiv.of_eraseMetadata_eq _ _ h₁
    have hv₂ := EMEquiv.of_eraseMetadata_eq _ _ h₂
    cases hv₁; cases hv₂; simp [LExpr.eql, h_nm']
  -- Cases 8-11: callOfLFunc catch-all (nested match)
  · -- case 8: callOfLFunc some/some, not both constructors → none
    rename_i _ _ _ _ h_ne _ _ _ _ _ _ h_call₁ h_call₂ h_nc h_not_cc h_not_aa h_not_ca h_not_ac
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne

    rw [h_call₁, h_call₂]; simp only [h_nc, ↓reduceIte]
    obtain ⟨_, _, h_call₁', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁ _ _ _ h_call₁
    obtain ⟨_, _, h_call₂', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂ _ _ _ h_call₂
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    symm; unfold LExpr.eql; rw [h_ef, ite_eq_right (by decide)]
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
  · -- case 9: callOfLFunc some/some, both constructors, different names → some false
    rename_i _ _ _ _ h_ne _ _ _ _ _ _ h_call₁ h_call₂ h_nc h_nd h_not_cc h_not_aa h_not_ca h_not_ac
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne
    rw [h_call₁, h_call₂]; simp only [h_nc, h_nd, ↓reduceIte]
    obtain ⟨_, _, h_call₁', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁ _ _ _ h_call₁
    obtain ⟨_, _, h_call₂', _, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂ _ _ _ h_call₂
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    symm; unfold LExpr.eql; rw [h_ef, ite_eq_right (by decide)]
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
  · -- case 10: callOfLFunc some/some, both constructors, same name → foldl eqlCombine
    rename_i _ _ _ h_ne _ _ _ _ _ _ h_call₁ h_call₂ h_nc h_nd h_not_cc h_not_aa h_not_ca h_not_ac ih
    have h_nm' : ¬LExpr.eqModuloMeta e₁' e₂' = true := by rw [← eqModuloMeta_eraseMetadata_eq h₁ h₂]; exact h_ne
    rw [h_call₁, h_call₂]; simp only [h_nc, h_nd]
    obtain ⟨_, _, h_call₁', h_eM_args₁, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₁ _ _ _ h_call₁
    obtain ⟨_, _, h_call₂', h_eM_args₂, _⟩ := callOfLFunc_some_of_eraseMetadata_eq F _ _ false h₂ _ _ _ h_call₂
    have h_ef : LExpr.eqModuloMeta e₁' e₂' = false := by
      revert h_nm'; cases LExpr.eqModuloMeta e₁' e₂' <;> simp
    -- Unfold only the top-level eql (preserving inner eql calls in foldl)
    symm
    rw [Lambda.LExpr.eql.eq_5 F e₁' e₂' (by
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
    rw [h_ef, ite_eq_right (by decide), h_call₁', h_call₂']
    simp only [h_nc, h_nd]
    -- Clear remaining if false = true wrappers
    simp only [ite_eq_right (by decide : ¬(false = true))]
    -- Convert both foldls from attach.zip to plain zip using the helper
    simp only [foldl_attach_zip_eq_eql F]
    -- Apply the zip congruence helper
    exact (foldl_zip_eql_congr F _ _ _ _ h_eM_args₁ h_eM_args₂ ih _).symm
  · -- case 11: callOfLFunc catch-all (simultaneous match not both some) → none
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
      symm; unfold LExpr.eql; rw [h_ef, ite_eq_right (by decide)]
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

theorem step_to_const_via_IH
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase)
    (e e' : LExpr Tbase.mono) (mc : Tbase.Metadata) (c : LConst)
    (hstep : StepStar F env e e')
    (h_eM : e'.eraseMetadata = (LExpr.const mc c).eraseMetadata) :
    ∃ mc', StepStar F env e (.const mc' c) := by
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



theorem StepStar_to_substFvarsFromEnv_abs
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (m : Tbase.Metadata) (name : String) (ty : Option LMonoTy)
    (body : LExpr Tbase.mono) :
    StepStar F env
      (.abs m name ty body) (LExpr.substFvarsFromEnv env (.abs m name ty body)) := by
  simp only [LExpr.substFvarsFromEnv]
  cases h_fv : (LExpr.freeVars body) with
  | nil =>
    rw [LExpr.substFvarsFromEnv_closed_identity env body h_fv]; exact ReflTrans.refl _
  | cons p ps =>
    have h_mem : p.fst ∈ (LExpr.freeVars body).map Prod.fst := by
      rw [h_fv]; simp [List.map]
    exact ReflTrans.step _ _ _
      (Step.abs_subst_fvars (m' := m) body p.fst h_mem)
      (ReflTrans.refl _)

theorem StepStar_to_substFvarsFromEnv_quant
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (m : Tbase.Metadata) (qk : QuantifierKind)
    (name : String) (ty : Option LMonoTy)
    (tr body : LExpr Tbase.mono) :
    StepStar F env
      (.quant m qk name ty tr body) (LExpr.substFvarsFromEnv env (.quant m qk name ty tr body)) := by
  simp only [LExpr.substFvarsFromEnv]
  cases h_fv_body : (LExpr.freeVars body) with
  | nil =>
    rw [LExpr.substFvarsFromEnv_closed_identity env body h_fv_body]
    cases h_fv_tr : (LExpr.freeVars tr) with
    | nil =>
      rw [LExpr.substFvarsFromEnv_closed_identity env tr h_fv_tr]; exact ReflTrans.refl _
    | cons p ps =>
      have h_mem : p.fst ∈ (LExpr.freeVars tr).map Prod.fst := by rw [h_fv_tr]; simp [List.map]
      exact ReflTrans.step _ _ _
        (Step.quant_subst_fvars_trigger (m' := m) tr body p.fst h_mem) (ReflTrans.refl _)
  | cons p ps =>
    cases h_fv_tr : (LExpr.freeVars tr) with
    | nil =>
      rw [LExpr.substFvarsFromEnv_closed_identity env tr h_fv_tr]
      have h_mem : p.fst ∈ (LExpr.freeVars body).map Prod.fst := by rw [h_fv_body]; simp [List.map]
      exact ReflTrans.step _ _ _
        (Step.quant_subst_fvars_body (m' := m) tr body p.fst h_mem) (ReflTrans.refl _)
    | cons p2 ps2 =>
      have h_mem_body : p.fst ∈ (LExpr.freeVars body).map Prod.fst := by rw [h_fv_body]; simp [List.map]
      have h_mem_tr : p2.fst ∈ (LExpr.freeVars tr).map Prod.fst := by rw [h_fv_tr]; simp [List.map]
      exact ReflTrans_Transitive _ _ _ _
        (ReflTrans.step _ _ _
          (Step.quant_subst_fvars_body (m' := m) tr body p.fst h_mem_body) (ReflTrans.refl _))
        (ReflTrans.step _ _ _
          (Step.quant_subst_fvars_trigger (m' := m) tr (LExpr.substFvarsFromEnv env body) p2.fst h_mem_tr) (ReflTrans.refl _))

---------------------------------------------------------------------

-- isValue depends only on eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
theorem isValue_eraseMetadata_eq
    {Tbase : LExprParams}
    [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
    (F : @Factory Tbase)
    (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.isValue F e₁ = LExpr.isValue F e₂ := by
  -- Use strong induction on e₁.sizeOf
  suffices h : ∀ (sz : Nat) (e₁ e₂ : LExpr Tbase.mono),
      e₁.sizeOf ≤ sz → e₁.eraseMetadata = e₂.eraseMetadata →
      LExpr.isValue F e₁ = LExpr.isValue F e₂ from
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
      cases hv; simp [LExpr.isValue]
    | abs m nm ty body =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | abs _ => simp only [LExpr.isValue]; unfold LExpr.closed; rw [LExpr.freeVars_of_eraseMetadata_eq _ _ heM]
    | quant m qk nm ty tr body =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | quant _ _ => simp only [LExpr.isValue]; unfold LExpr.closed; rw [LExpr.freeVars_of_eraseMetadata_eq _ _ heM]
    | op m nm ty =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | op =>
        simp only [LExpr.isValue]
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
      cases hv; simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
    | fvar m x ty =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
    | app m fn arg =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv with
      | app hfn harg =>
        simp only [LExpr.isValue]
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
          -- The first part of `&&` is the same; show that all arguments are values on both sides.
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
          suffices h_map : args₁.attach.map (fun x => LExpr.isValue F x.val) =
              args₂.attach.map (fun x => LExpr.isValue F x.val) by
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
      cases hv; simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
    | ite m c t f =>
      have hv := EMEquiv.of_eraseMetadata_eq _ e₂ heM
      cases hv; simp [LExpr.isValue, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

-- isConstrApp depends only on eraseMetadata.
omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
theorem isConstrApp_eraseMetadata_eq
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
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m₁ m₂ : Tbase.Metadata) (c₁ c₂ t₁ t₂ f₁ f₂ : LExpr Tbase.mono)
    (hc : c₁.eraseMetadata = c₂.eraseMetadata)
    (ht : t₁.eraseMetadata = t₂.eraseMetadata)
    (hf : f₁.eraseMetadata = f₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' F env e₁).fst.eraseMetadata = (LExpr.eval n' F env e₂).fst.eraseMetadata) :
    (LExpr.evalIte n' F env m₁ c₁ t₁ f₁).fst.eraseMetadata =
    (LExpr.evalIte n' F env m₂ c₂ t₂ f₂).fst.eraseMetadata := by
  simp only [LExpr.evalIte]
  have hc' := ih c₁ c₂ hc
  generalize hg₁ : (LExpr.eval n' F env c₁).fst = c₁' at hc' ⊢
  generalize hg₂ : (LExpr.eval n' F env c₂).fst = c₂' at hc' ⊢
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
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m₁ m₂ : Tbase.Metadata) (l₁ l₂ r₁ r₂ : LExpr Tbase.mono)
    (hl : l₁.eraseMetadata = l₂.eraseMetadata)
    (hr : r₁.eraseMetadata = r₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' F env e₁).fst.eraseMetadata = (LExpr.eval n' F env e₂).fst.eraseMetadata) :
    (LExpr.evalEq n' F env m₁ l₁ r₁).fst.eraseMetadata =
    (LExpr.evalEq n' F env m₂ l₂ r₂).fst.eraseMetadata := by
  simp only [LExpr.evalEq]
  have hl' := ih l₁ l₂ hl
  have hr' := ih r₁ r₂ hr
  rw [eql_eraseMetadata_eq F _ _ _ _ hl' hr']
  generalize LExpr.eql F (LExpr.eval n' F env l₂).fst (LExpr.eval n' F env r₂).fst = eql_res
  cases eql_res with
  | some b => simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]
  | none => exact eraseMetadata_eq_congr hl' hr'

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [Inhabited Tbase.IDMeta] in
theorem substFvarsLifting_zip_eraseMetadata_congr
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
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e₁ e₂ a₁ a₂ b₁ b₂ : LExpr Tbase.mono)
    (he : e₁.eraseMetadata = e₂.eraseMetadata)
    (ha : a₁.eraseMetadata = a₂.eraseMetadata)
    (hb : b₁.eraseMetadata = b₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' F env e₁).fst.eraseMetadata = (LExpr.eval n' F env e₂).fst.eraseMetadata) :
    (LExpr.evalApp n' F env e₁ a₁ b₁).fst.eraseMetadata =
    (LExpr.evalApp n' F env e₂ a₂ b₂).fst.eraseMetadata := by
  simp only [LExpr.evalApp]
  have ha' := ih a₁ a₂ ha
  have hb' := ih b₁ b₂ hb
  generalize hg₁ : (LExpr.eval n' F env a₁).fst = a₁' at ha' ⊢
  generalize hg₂ : (LExpr.eval n' F env a₂).fst = a₂' at ha' ⊢
  generalize hg₃ : (LExpr.eval n' F env b₁).fst = b₁' at hb' ⊢
  generalize hg₄ : (LExpr.eval n' F env b₂).fst = b₂' at hb' ⊢
  have hv := EMEquiv.of_eraseMetadata_eq _ _ ha'
  cases hv with
  | abs hv_body =>
    dsimp only
    generalize hs₁ : (LExpr.subst _ _) = s₁
    generalize hs₂ : (LExpr.subst _ _) = s₂
    have h_subst_eM : s₁.eraseMetadata = s₂.eraseMetadata := by
      subst hs₁; subst hs₂
      apply substK_eraseMetadata_congr₂ _ _ 0 _ _ hv_body.eraseMetadata_eq
      intro m₁ m₂
      have h_rp1 : ∀ m' (e' : LExpr Tbase.mono),
          (LExpr.replaceMetadata1 m' e').eraseMetadata = e'.eraseMetadata :=
        fun m' e' => by cases e' <;> simp [LExpr.replaceMetadata1, LExpr.eraseMetadata, LExpr.replaceMetadata]
      rw [h_rp1, h_rp1]; exact hb'
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
theorem evalCore_eraseMetadata_congr
    [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata)
    (ih : ∀ e₁ e₂, e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' F env e₁).fst.eraseMetadata = (LExpr.eval n' F env e₂).fst.eraseMetadata) :
    (LExpr.evalCore n' F env e₁).fst.eraseMetadata =
    (LExpr.evalCore n' F env e₂).fst.eraseMetadata := by
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
    cases env _ with
    | some v => rfl
    | none => simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
  | abs hv_body =>
    simp only [LExpr.evalCore]
    exact LExpr.substFvarsFromEnv_eraseMetadata_congr env _ _
      (eraseMetadata_abs_congr hv_body.eraseMetadata_eq)
  | quant hv_tr hv_body =>
    simp only [LExpr.evalCore]
    exact LExpr.substFvarsFromEnv_eraseMetadata_congr env _ _
      (eraseMetadata_quant_congr hv_tr.eraseMetadata_eq hv_body.eraseMetadata_eq)
  | app hv_fn hv_arg =>
    simp only [LExpr.evalCore]
    exact evalApp_eraseMetadata_congr n' F env _ _ _ _ _ _
      h_eM hv_fn.eraseMetadata_eq hv_arg.eraseMetadata_eq ih
  | eq hv_l hv_r =>
    simp only [LExpr.evalCore]
    exact evalEq_eraseMetadata_congr n' F env _ _ _ _ _ _
      hv_l.eraseMetadata_eq hv_r.eraseMetadata_eq ih
  | ite hv_c hv_t hv_e =>
    simp only [LExpr.evalCore]
    exact evalIte_eraseMetadata_congr n' F env _ _ _ _ _ _ _ _
      hv_c.eraseMetadata_eq hv_t.eraseMetadata_eq hv_e.eraseMetadata_eq ih


---------------------------------------------------------------------

/-- Replacing an expression's metadata does not change its type-check result. -/
private theorem typeCheck_replaceMetadata {T : LExprParams} {NewMetadata : Type}
    (e : LExpr T.mono) (ctx : List LMonoTy) (f : T.Metadata → NewMetadata) :
    LExpr.typeCheck ctx e = LExpr.typeCheck ctx (e.replaceMetadata f) := by
  induction e generalizing ctx <;>
    simp [LExpr.replaceMetadata, LExpr.typeCheck] <;> try grind
  case op m o ty => cases ty <;> simp [LExpr.typeCheck]
  case fvar m name ty => cases ty <;> simp [LExpr.typeCheck]
  case abs m name ty body ih =>
    cases ty <;> simp [LExpr.typeCheck, ih]
  case quant m k name ty tr body ihtr ih =>
    cases ty <;> simp [LExpr.typeCheck, ih, ihtr]

/-- Erasing all metadata from an expression does not change its type-check result. -/
private theorem typeCheck_eraseMetadata {T : LExprParams}
    (e : LExpr T.mono) (ctx : List LMonoTy) :
    LExpr.typeCheck ctx e.eraseMetadata = LExpr.typeCheck ctx e := by
  simpa [LExpr.eraseMetadata] using
    (typeCheck_replaceMetadata e ctx (fun _ => ())).symm

/-- Expressions with the same metadata-free form type-check identically. -/
private theorem typeCheck_of_eraseMetadata_eq {T : LExprParams}
    (e₁ e₂ : LExpr T.mono) (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.typeCheck [] e₁ = LExpr.typeCheck [] e₂ := by
  have h1 := typeCheck_eraseMetadata e₁ []
  have h2 := typeCheck_eraseMetadata e₂ []
  rw [h] at h1; rw [← h1, h2]

-- computeTypeSubst is metadata-invariant: if callee and args have the same
-- eraseMetadata, computeTypeSubst produces the same result.
-- computeTypeSubst depends on callee only through its .op type annotation
-- (preserved by eraseMetadata) and on args only through typeCheck (also preserved).
theorem computeTypeSubst_eraseMetadata_congr {T : LExprParams}
    (fn : LFunc T) (op₁ op₂ : LExpr T.mono)
    (args₁ args₂ : List (LExpr T.mono))
    (h_op : op₁.eraseMetadata = op₂.eraseMetadata)
    (h_args : args₁.map LExpr.eraseMetadata = args₂.map LExpr.eraseMetadata) :
    LFunc.computeTypeSubst fn op₁ args₁ = LFunc.computeTypeSubst fn op₂ args₂ := by

  -- For the args part:
  have h_argC : ((args₁.zip fn.inputs.values).filterMap
      (fun (arg, formal) => (LExpr.typeCheck [] arg).map (·, formal))) =
    ((args₂.zip fn.inputs.values).filterMap
      (fun (arg, formal) => (LExpr.typeCheck [] arg).map (·, formal))) := by
    -- Prove by auxiliary induction on args and formals simultaneously
    suffices h_suff : ∀ (l₁ l₂ : List (LExpr T.mono)) (vs : List LMonoTy),
        l₁.map LExpr.eraseMetadata = l₂.map LExpr.eraseMetadata →
        (l₁.zip vs).filterMap
            (fun (arg, formal) => (LExpr.typeCheck [] arg).map (·, formal)) =
        (l₂.zip vs).filterMap
            (fun (arg, formal) => (LExpr.typeCheck [] arg).map (·, formal)) from
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
        rw [typeCheck_of_eraseMetadata_eq _ _ h_hd, ih tl₂ vs' h_tl]
      | hd₂ :: tl₂, [] => simp [List.zip]
      | [], _ => simp at h_eM
  -- opTypeSubst only depends on the type annotation of the callee
  have h_opTS : fn.opTypeSubst op₁ = fn.opTypeSubst op₂ := by
    simp only [LFunc.opTypeSubst]
    cases op₁ <;> cases op₂ <;>
      simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_op ⊢
    rename_i ty
    cases ty <;> grind
  simp only [LFunc.computeTypeSubst, h_opTS, h_argC]
end -- public section
end Lambda
