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
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
import Strata.Util.ListMapProps

/-!
# Properties of Lambda operational semantics

This module contains normal-form, closure-lifting, substitution, factory-call,
and metadata-insensitivity lemmas used to reason about `Step` and `StepStar`.
Evaluator-specific top-level theorems live in `LExprEvalProps` and
`LExprEvalSound`. A reduction introduces no free variable beyond those of the source and
of the environment's values (`Step.namesIn`, `StepStar.namesIn`, stated with
`LExpr.NamesIn`), and, under a factory that brings in only its own operators
(`Factory.OpsClosed`), no operator beyond those of the source, of the environment's values
and of the factory (`Step.opsIn`, `StepStar.opsIn`, stated with `LExpr.OpsIn`).
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
  simp only [List.append_nil] at h; exact h

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
    · simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h_call; obtain ⟨rfl, rfl⟩ := h_call
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
  cases op' <;> simp only [↓reduceIte, Bool.false_eq_true, reduceCtorEq] at h_partial h_full_some ⊢
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h_partial
  | some func' =>
    simp only [h_gf] at h_partial h_full_some ⊢
    split at h_full_some <;> simp at h_full_some
    split at h_partial <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h_partial
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
  cases op' <;> simp only [↓reduceIte, reduceCtorEq] at h_partial
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h_partial
  | some func' =>
    simp only [h_gf] at h_partial
    split at h_partial <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h_partial
    obtain ⟨_, _, rfl⟩ := h_partial
    rename_i h_ble
    -- From h_same (full arity), args.length = f.inputs.length
    simp only [Factory.callOfLFunc, h_lfc, h_gf] at h_same
    split at h_same <;> simp at h_same
    rename_i h_eq; simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at h_eq
    simp only [Bool.or_eq_true] at h_cond
    cases h_cond with
    | inl h => exact h
    | inr h => simp only [Nat.blt, Nat.succ_eq_add_one, Nat.ble_eq] at h; rw [← h_eq, h_ble] at h; omega

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
/-- If `callOfLFunc` (with either `allowPartialApp`) recognizes `.app m e1 e2` as a call, its
    argument `e2` is among the call's arguments (the last one). -/
theorem callOfLFunc_app_arg_mem
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
        simp only [Option.some.injEq, Prod.mk.injEq] at h
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

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] in
/-- The function part `e1` of an application `.app m e1 e2` that is a value is a value. -/
theorem isValue_app_left
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
        split at h_call <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h_call
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
                simp only [Nat.blt, Nat.succ_eq_add_one, Nat.ble_eq, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add] at h ⊢
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
      simp only [LExpr.LExpr.getVars]
      have h_closed : LExpr.closed (.abs m n ty body) = true := by
        simp only [LExpr.isValue, LExpr.closed_abs] at hc; exact hc
      have h_body_closed : LExpr.closed body = true := by
        simp only [LExpr.closed, LExpr.freeVars, List.isEmpty_iff] at h_closed ⊢; exact h_closed
      exact closed_implies_getVars_nil body h_body_closed
    | quant => simp [LExpr.isValue] at hc
    | app m e1 e2 =>
      simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff]
      have hc_app := hc
      simp only [LExpr.isValue, List.map_subtype, List.unattach_attach, List.all_map, Function.id_comp] at hc
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
    simp only [LExpr.isValue, LExpr.closed_abs] at hc
    cases hstep with
    | expand_fn _ _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | eval_fn _ _ _ _ _ _ h_call => simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h_call
    | abs_subst_fvars _ _ h_fv =>
      have h_fvs : LExpr.freeVars body = [] := by
        simp only [LExpr.closed, List.isEmpty_iff] at hc; exact hc
      simp [h_fvs] at h_fv
  | quant => simp [LExpr.isValue] at hc
  | op =>
    intro e' hstep
    simp only [LExpr.isValue, List.map_subtype, List.unattach_attach, List.all_map, Function.id_comp] at hc
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
    simp only [LExpr.isValue, List.map_subtype, List.unattach_attach, List.all_map, Function.id_comp] at hc
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
        simp only [LExpr.isValue, List.map_subtype, List.unattach_attach, List.all_map, Function.id_comp]
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
    simp only [List.append_nil] at h_get_inner
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
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
    Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero] at h_a
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
  simp only at h_op h_args
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
          have h_len_eq := congrArg List.length h_args; simp only [List.length_map] at h_len_eq; exact h_len_eq
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
    have h_len_eq := congrArg List.length h_eM₁; simp only [List.length_map] at h_len_eq; exact h_len_eq
  have h_len₂ : args₂.length = args₂'.length := by
    have h_len_eq := congrArg List.length h_eM₂; simp only [List.length_map] at h_len_eq; exact h_len_eq
  -- Use generic foldl_zip_congr
  apply List.foldl_zip_congr (fun acc a b => LExpr.eqlCombine acc (LExpr.eql F a b)) _ _ _ _ h_len₁ h_len₂
  · intro i hi₁ hi₂ acc
    -- Get elements at index i
    have hi₁' : i < args₁'.length := h_len₁ ▸ hi₁
    have hi₂' : i < args₂'.length := h_len₂ ▸ hi₂
    have h_eM_a : (args₁[i]).eraseMetadata = (args₁'[i]'hi₁').eraseMetadata := by
      have h1 := congrArg (·[i]?) h_eM₁
      simp only [List.length_map, hi₁, getElem?_pos, List.getElem_map, hi₁', Option.some.injEq] at h1
      exact h1
    have h_eM_b : (args₂[i]).eraseMetadata = (args₂'[i]'hi₂').eraseMetadata := by
      have h1 := congrArg (·[i]?) h_eM₂
      simp only [List.length_map, hi₂, getElem?_pos, List.getElem_map, hi₂', Option.some.injEq] at h1
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
  simp only [LExpr.eraseMetadata, LExpr.replaceMetadata] at h_eM
  cases e' <;> simp only [LExpr.replaceMetadata, LExpr.const.injEq, true_and] at h_eM <;> try contradiction
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
      simp only [Bool.false_eq_true, ↓reduceIte, LExpr.substFvars.substFvarsAux, LExpr.abs.injEq, true_and]
      simp only [LExpr.freeVars] at h_closed
      exact ih h_closed
    | app _ _ _ ih1 ih2 =>
      simp only [Bool.false_eq_true, ↓reduceIte, LExpr.substFvars.substFvarsAux, LExpr.app.injEq, true_and]
      simp only [LExpr.freeVars, List.append_eq_nil_iff] at h_closed
      exact ⟨ih1 h_closed.1, ih2 h_closed.2⟩
    | eq _ _ _ ih1 ih2 =>
      simp only [Bool.false_eq_true, ↓reduceIte, LExpr.substFvars.substFvarsAux, LExpr.eq.injEq, true_and]
      simp only [LExpr.freeVars, List.append_eq_nil_iff] at h_closed
      exact ⟨ih1 h_closed.1, ih2 h_closed.2⟩
    | quant _ _ _ _ _ _ ih1 ih2 =>
      simp only [Bool.false_eq_true, ↓reduceIte, LExpr.substFvars.substFvarsAux, LExpr.quant.injEq, true_and]
      simp only [LExpr.freeVars, List.append_eq_nil_iff] at h_closed
      exact ⟨ih1 h_closed.1, ih2 h_closed.2⟩
    | ite _ c t e ih1 ih2 ih3 =>
      simp only [Bool.false_eq_true, ↓reduceIte, LExpr.substFvars.substFvarsAux, LExpr.ite.injEq, true_and]
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

/-- Every expression steps to its free-variable substitution from the environment. -/
theorem StepStar_to_substFvarsFromEnv
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) :
    StepStar F env e (LExpr.substFvarsFromEnv env e) := by
  induction e with
  | const | bvar | op => exact ReflTrans.refl _
  | fvar m x ty =>
    simp only [LExpr.substFvarsFromEnv]
    split
    · rename_i v hv; exact ReflTrans.step _ _ _ (Step.expand_fvar x v hv) (ReflTrans.refl _)
    · exact ReflTrans.refl _
  | abs m name ty body => exact StepStar_to_substFvarsFromEnv_abs F env m name ty body
  | quant m qk name ty tr body =>
    exact StepStar_to_substFvarsFromEnv_quant F env m qk name ty tr body
  | app m fn a ih1 ih2 =>
    exact ReflTrans_Transitive _ _ _ _ (StepStar_app_fn F env _ _ _ m ih1)
      (StepStar_app_arg F env _ _ _ m ih2)
  | ite m c t f ihc iht ihf =>
    exact ReflTrans_Transitive _ _ _ _ (StepStar_ite_cond_pres F env _ _ _ _ m ihc)
      (ReflTrans_Transitive _ _ _ _ (StepStar_ite_then_pres F env _ _ _ _ m iht)
        (StepStar_ite_else_pres F env _ _ _ _ m ihf))
  | eq m e1 e2 ih1 ih2 =>
    exact ReflTrans_Transitive _ _ _ _ (StepStar_eq_lhs_pres F env _ _ _ m ih1)
      (StepStar_eq_rhs_pres F env _ _ _ m ih2)

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
      | quant _ _ => simp only [LExpr.isValue]
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
            split at h1' <;> simp only [↓reduceIte, List.length_nil, reduceCtorEq] at h1'
            split at h1' <;> simp only [Option.some.injEq, reduceCtorEq] at h1'
            rw [← h1']
          have h_len : v1.snd.fst.length = args₂.length := by
            have h_len_eq := congrArg List.length h_args_eM; simp only [List.length_map] at h_len_eq; exact h_len_eq
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
            have h_len_eq := congrArg List.length h_args_eM; simp only [List.length_map] at h_len_eq; exact h_len_eq
          simp only [h_len]
          -- The first part of `&&` is the same; show that all arguments are values on both sides.
          congr 1
          -- Extract getLFuncCall from h1 to prove args are smaller
          have h_gl : getLFuncCall (.app m fn arg : LExpr Tbase.mono) = (op₁, args₁) := by
            simp only [Factory.callOfLFunc, ↓reduceIte] at h1
            cases h_lfc : getLFuncCall (.app m fn arg : LExpr Tbase.mono) with | mk op' args' =>
            simp only [h_lfc] at h1
            cases op' <;> simp only [reduceCtorEq] at h1
            rename_i name_op _ _
            split at h1
            · simp at h1
            · split at h1 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h1
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
              simp only [List.length_map, hi₁', getElem?_pos, List.getElem_map, hi₂', Option.some.injEq] at h_eM_i
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
      simp only at h
      rw [h.1]

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]
  [Inhabited Tbase.IDMeta] in
/-- Whether an expression is an `inlineIfAllValues` unfolding argument (`isInlineArg`)
depends only on the expression with its metadata erased. -/
theorem isInlineArg_eraseMetadata_eq
    (F : @Factory Tbase)
    (e₁ e₂ : LExpr Tbase.mono)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    LExpr.isInlineArg F e₁ = LExpr.isInlineArg F e₂ := by
  induction e₁ using LExpr.isInlineArg.induct (T := Tbase.mono) F generalizing e₂ with
  | case4 e hc ha hq op args f h ih =>
    obtain ⟨op₂, args₂, h2, hA, -⟩ :=
      callOfLFunc_some_of_eraseMetadata_eq F _ _ true h_eM _ _ _ h
    have hL : args.length = args₂.length := by simpa using congrArg List.length hA
    have hAll : args.all (LExpr.isInlineArg F) = args₂.all (LExpr.isInlineArg F) := by
      clear h h2
      induction args generalizing args₂ <;> cases args₂ <;> grind
    rw [LExpr.isInlineArg.eq_4 F e hc ha hq, LExpr.isInlineArg.eq_4 F e₂]
    · split <;> split <;> simp_all [List.all_map]
    all_goals
      intros; subst_vars
      cases EMEquiv.of_eraseMetadata_eq _ _ h_eM
      first | exact hc _ _ rfl | exact ha _ _ _ _ rfl | exact hq _ _ _ _ _ _ rfl
  | case5 e hc ha hq h =>
    have h2 := callOfLFunc_none_of_eraseMetadata_eq F _ _ true h_eM h
    rw [LExpr.isInlineArg.eq_4 F e hc ha hq, LExpr.isInlineArg.eq_4 F e₂]
    · split <;> split <;> simp_all
    all_goals
      intros; subst_vars
      cases EMEquiv.of_eraseMetadata_eq _ _ h_eM
      first | exact hc _ _ rfl | exact ha _ _ _ _ rfl | exact hq _ _ _ _ _ _ rfl
  | _ =>
    cases EMEquiv.of_eraseMetadata_eq _ _ h_eM <;>
      simp only [LExpr.isInlineArg, LExpr.closed, LExpr.freeVars_of_eraseMetadata_eq _ _ h_eM]


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
    have h_len_eq := congrArg List.length h_vals; simp only [List.length_map] at h_len_eq; exact h_len_eq
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
          · exact ih vs₁ vs₂ h_vals.2 (by simp only [List.length_cons, Nat.add_right_cancel_iff] at h_vals_len; exact h_vals_len)
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
            simp only [h1, Option.map_some, h2, Option.some.injEq] at hfc
            simp only [LExpr.eraseMetadata_replaceMetadata1]
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
    | some v => simp only [LExpr.eraseMetadata_replaceMetadata1]
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
  have h_tys : args₁.map (LExpr.typeCheck []) = args₂.map (LExpr.typeCheck []) := by
    have h_erased := congrArg (List.map (LExpr.typeCheck [])) h_args
    have h_comp : (LExpr.typeCheck [] ∘ LExpr.eraseMetadata : LExpr T.mono → _) =
        LExpr.typeCheck [] := funext fun e => typeCheck_eraseMetadata e []
    simp only [List.map_map, h_comp] at h_erased
    exact h_erased
  simp only [LFunc.computeTypeSubst, LFuncDefined.callInstance?_congr fn.toFunc h_op h_tys]

/-! ## Reduction introduces no free variable

A reduction step under a well-formed factory keeps the free variables of an expression
within any set of names that contains them and the free variables of the environment's
values: a function body mentions only its parameters, which expansion replaces by the
arguments, and a concrete evaluator returns only free variables of its arguments
(`Step.namesIn`, `StepStar.namesIn`). -/

section NamesIn

variable {T : LExprParams}

namespace LExpr.NamesIn

variable {S : T.Identifier → Prop}

/-- An expression with no free variable satisfies every predicate on its names. -/
private theorem of_freeVars_nil {e : LExpr T.mono} (h : LExpr.freeVars e = []) : e.NamesIn S := by
  intro x ty hx; rw [h] at hx; cases hx

/-- A constant has no free variable. -/
@[simp] theorem const {m c} : (LExpr.const m c : LExpr T.mono).NamesIn S := by
  intro x ty hx; simp [LExpr.freeVars] at hx

/-- An operator has no free variable. -/
@[simp] theorem op {m o ty} : (LExpr.op m o ty : LExpr T.mono).NamesIn S := by
  intro x ty hx; simp [LExpr.freeVars] at hx

/-- A bound variable has no free variable. -/
@[simp] theorem bvar {m i} : (LExpr.bvar m i : LExpr T.mono).NamesIn S := by
  intro x ty hx; simp [LExpr.freeVars] at hx

/-- A free variable satisfies `S` exactly when its name does. -/
@[simp] theorem fvar {m x ty} : (LExpr.fvar m x ty : LExpr T.mono).NamesIn S ↔ S x := by
  simp [LExpr.NamesIn, LExpr.freeVars]

/-- Replacing the root metadata keeps the free variables. -/
@[simp] theorem replaceMetadata1 {m} {e : LExpr T.mono} :
    (LExpr.replaceMetadata1 m e).NamesIn S ↔ e.NamesIn S := by
  simp only [LExpr.NamesIn, LExpr.freeVars_replaceMetadata1]

/-- An abstraction has the free variables of its body. -/
@[simp] theorem abs {m n ty} {b : LExpr T.mono} : (LExpr.abs m n ty b).NamesIn S ↔ b.NamesIn S := by
  simp [LExpr.NamesIn, LExpr.freeVars]

/-- A quantifier has the free variables of its trigger and its body. -/
@[simp] theorem quant {m qk n ty} {tr b : LExpr T.mono} :
    (LExpr.quant m qk n ty tr b).NamesIn S ↔ tr.NamesIn S ∧ b.NamesIn S := by
  simp only [LExpr.NamesIn, LExpr.freeVars, List.mem_append]
  exact ⟨fun h => ⟨fun x ty hx => h x ty (.inl hx), fun x ty hx => h x ty (.inr hx)⟩,
    fun ⟨h₁, h₂⟩ x ty hx => hx.elim (h₁ x ty) (h₂ x ty)⟩

/-- An application has the free variables of its function and its argument. -/
@[simp] theorem app {m} {f a : LExpr T.mono} :
    (LExpr.app m f a).NamesIn S ↔ f.NamesIn S ∧ a.NamesIn S := by
  simp only [LExpr.NamesIn, LExpr.freeVars, List.mem_append]
  exact ⟨fun h => ⟨fun x ty hx => h x ty (.inl hx), fun x ty hx => h x ty (.inr hx)⟩,
    fun ⟨h₁, h₂⟩ x ty hx => hx.elim (h₁ x ty) (h₂ x ty)⟩

/-- An equality has the free variables of its two sides. -/
@[simp] theorem eq {m} {a b : LExpr T.mono} :
    (LExpr.eq m a b).NamesIn S ↔ a.NamesIn S ∧ b.NamesIn S := by
  simp only [LExpr.NamesIn, LExpr.freeVars, List.mem_append]
  exact ⟨fun h => ⟨fun x ty hx => h x ty (.inl hx), fun x ty hx => h x ty (.inr hx)⟩,
    fun ⟨h₁, h₂⟩ x ty hx => hx.elim (h₁ x ty) (h₂ x ty)⟩

/-- A conditional has the free variables of its condition and its two branches. -/
@[simp] theorem ite {m} {c t f : LExpr T.mono} :
    (LExpr.ite m c t f).NamesIn S ↔ c.NamesIn S ∧ t.NamesIn S ∧ f.NamesIn S := by
  simp only [LExpr.NamesIn, LExpr.freeVars, List.mem_append]
  exact ⟨fun h => ⟨fun x ty hx => h x ty (.inl (.inl hx)), fun x ty hx => h x ty (.inl (.inr hx)),
      fun x ty hx => h x ty (.inr hx)⟩,
    fun ⟨h₁, h₂, h₃⟩ x ty hx => hx.elim (fun hx => hx.elim (h₁ x ty) (h₂ x ty)) (h₃ x ty)⟩

/-- Substituting for a bound variable an expression whose free variables satisfy `S` keeps them in
    `S`. -/
theorem substK {s : T.Metadata → LExpr T.mono} (hs : ∀ m, (s m).NamesIn S) :
    ∀ {k : Nat} {e : LExpr T.mono}, e.NamesIn S → (LExpr.substK k s e).NamesIn S := by
  intro k e
  induction e generalizing k with
  | bvar m i =>
    intro _
    simp only [LExpr.substK]
    split
    · exact hs m
    · exact bvar
  | const | op | fvar => intro he; simpa only [LExpr.substK] using he
  | abs _ _ _ _ ih => simp only [LExpr.substK, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    simp only [LExpr.substK, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    simp only [LExpr.substK, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    simp only [LExpr.substK, ite]; exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    simp only [LExpr.substK, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

/-- A predicate that the free variables satisfy can be weakened. -/
theorem mono {S' : T.Identifier → Prop} (h : ∀ x, S x → S' x) {e : LExpr T.mono}
    (he : e.NamesIn S) : e.NamesIn S' := fun x ty hx => h x (he x ty hx)

/-- Shifting bound variables keeps the free variables. -/
theorem liftBVars {n : Nat} : ∀ {e : LExpr T.mono} {c : Nat},
    e.NamesIn S → (LExpr.liftBVars n e c).NamesIn S := by
  intro e
  induction e with
  | bvar m i => intro c _; simp only [LExpr.liftBVars]; split <;> exact bvar
  | const | op | fvar => intro c he; simpa only [LExpr.liftBVars] using he
  | abs _ _ _ _ ih => intro c; simp only [LExpr.liftBVars, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    intro c; simp only [LExpr.liftBVars, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    intro c; simp only [LExpr.liftBVars, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    intro c; simp only [LExpr.liftBVars, ite]
    exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    intro c; simp only [LExpr.liftBVars, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

/-- Rewriting type annotations keeps the free variables. -/
theorem replaceUserProvidedType {f : LMonoTy → LMonoTy} : ∀ {e : LExpr T.mono},
    e.NamesIn S → (LExpr.replaceUserProvidedType e f).NamesIn S := by
  intro e
  induction e with
  | const | op | bvar => intro _; simp [LExpr.replaceUserProvidedType]
  | fvar => intro he; simpa only [LExpr.replaceUserProvidedType, fvar] using he
  | abs _ _ _ _ ih => simp only [LExpr.replaceUserProvidedType, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    simp only [LExpr.replaceUserProvidedType, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    simp only [LExpr.replaceUserProvidedType, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    simp only [LExpr.replaceUserProvidedType, ite]
    exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    simp only [LExpr.replaceUserProvidedType, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

/-- Instantiating type variables keeps the free variables. -/
theorem applyTypeSubst {S' : Subst} {e : LExpr T.mono} (he : e.NamesIn S) :
    (e.applyTypeSubst S').NamesIn S := by
  unfold LExpr.applyTypeSubst; split
  · exact he
  · exact replaceUserProvidedType he

/-- Substituting for free variables: a variable that is substituted for leaves only the
free variables of what replaces it. -/
private theorem substFvarsLifting_go [DecidableEq T.IDMeta] {sm : Map T.Identifier (LExpr T.mono)}
    (hsm : ∀ x r, sm.find? x = some r → r.NamesIn S) :
    ∀ {e : LExpr T.mono} {d : Nat}, e.NamesIn (fun x => S x ∨ (sm.find? x).isSome) →
      (LExpr.substFvarsLifting.go sm e d).NamesIn S := by
  intro e
  induction e with
  | const | op | bvar => intro d _; simp [LExpr.substFvarsLifting.go]
  | fvar m x ty =>
    intro d hx
    simp only [LExpr.substFvarsLifting.go]
    split
    · rename_i r hr; exact replaceMetadata1.mpr (liftBVars (hsm x r hr))
    · rename_i hr
      simp only [fvar, hr, Option.isSome_none, Bool.false_eq_true, or_false] at hx ⊢
      exact hx
  | abs _ _ _ _ ih => intro d; simp only [LExpr.substFvarsLifting.go, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    intro d; simp only [LExpr.substFvarsLifting.go, quant]
    exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    intro d; simp only [LExpr.substFvarsLifting.go, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    intro d; simp only [LExpr.substFvarsLifting.go, ite]
    exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    intro d; simp only [LExpr.substFvarsLifting.go, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

/-- Substituting for free variables leaves only the free variables of the expression not substituted
    for and of what replaces them. -/
theorem substFvarsLifting [DecidableEq T.IDMeta] {sm : Map T.Identifier (LExpr T.mono)}
    (hsm : ∀ x r, sm.find? x = some r → r.NamesIn S) {e : LExpr T.mono}
    (he : e.NamesIn (fun x => S x ∨ (sm.find? x).isSome)) :
    (LExpr.substFvarsLifting e sm).NamesIn S := by
  unfold LExpr.substFvarsLifting
  split
  · rename_i hemp
    refine mono (fun x hx => ?_) he
    rcases hx with hx | hx
    · exact hx
    · cases sm with
      | nil => simp [Map.find?] at hx
      | cons _ _ => simp [Map.isEmpty] at hemp
  · exact substFvarsLifting_go hsm he

/-- Substituting the environment's values for free variables leaves only those of the expression not
    bound in the environment and of the values. -/
theorem substFvarsFromEnv {env : Env T} (henv : ∀ x r, env x = some r → r.NamesIn S) :
    ∀ {e : LExpr T.mono}, e.NamesIn (fun x => S x ∨ (env x).isSome) →
      (LExpr.substFvarsFromEnv env e).NamesIn S := by
  intro e
  induction e with
  | const | op | bvar => intro _; simp [LExpr.substFvarsFromEnv]
  | fvar m x ty =>
    intro hx
    simp only [LExpr.substFvarsFromEnv]
    split
    · rename_i r hr; exact replaceMetadata1.mpr (henv x r hr)
    · rename_i hr
      simp only [fvar, hr, Option.isSome_none, Bool.false_eq_true, or_false] at hx ⊢
      exact hx
  | abs _ _ _ _ ih => simp only [LExpr.substFvarsFromEnv, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    simp only [LExpr.substFvarsFromEnv, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    simp only [LExpr.substFvarsFromEnv, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv, ite]
    exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    simp only [LExpr.substFvarsFromEnv, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

end LExpr.NamesIn

/-- The arguments `getLFuncCall` collects satisfy every property of expressions that passes
    from an application to its function and its argument. -/
private theorem getLFuncCall_go_sat {P : LExpr T.mono → Prop}
    (happ : ∀ {m f a}, P (.app m f a) → P f ∧ P a) :
    ∀ (e : LExpr T.mono) (acc : List (LExpr T.mono)), P e → (∀ a ∈ acc, P a) →
      ∀ a ∈ (getLFuncCall.go e acc).2, P a := by
  intro e acc
  fun_induction getLFuncCall.go e acc with
  | case1 _ _ _ _ _ _ ih =>
    intro he hacc
    have h₁ := happ he
    have h₂ := happ h₁.1
    refine ih h₂.1 (fun a ha => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact h₂.2
    · exact h₁.2
    · exact hacc a ha
  | case2 =>
    intro he hacc a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (happ he).2
    · exact hacc a ha
  | case3 => intro _ hacc; exact hacc

/-- The arguments of a call satisfy every property of expressions that holds of the call and
    passes from an application to its function and its argument. -/
private theorem callOfLFunc_args_sat {P : LExpr T.mono → Prop}
    (happ : ∀ {m f a}, P (.app m f a) → P f ∧ P a) {F : @Factory T}
    {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hc : F.callOfLFunc e = some (callee, args, fn)) (he : P e) : ∀ a ∈ args, P a := by
  have hg := callOfLFunc_getLFuncCall hc
  have hargs := getLFuncCall_go_sat happ e [] he (by simp)
  unfold getLFuncCall at hg
  rw [hg] at hargs
  exact hargs

/-- The arguments of a call are subterms of it, so they have no free variable it has not. -/
private theorem callOfLFunc_args_namesIn {S : T.Identifier → Prop} {F : @Factory T}
    {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hc : F.callOfLFunc e = some (callee, args, fn)) (he : e.NamesIn S) :
    ∀ a ∈ args, a.NamesIn S :=
  callOfLFunc_args_sat (fun h => LExpr.NamesIn.app.mp h) hc he

/-- An expansion mentions only free variables of the arguments: the body of a well-formed
function mentions only its parameters, and expansion replaces each by its argument. -/
private theorem expand_namesIn [DecidableEq T.IDMeta] [Subsingleton T.IDMeta]
    {S : T.Identifier → Prop}
    {fn : LFunc T} (hwf : LFuncWF fn) {body : LExpr T.mono} (hb : fn.body = some body)
    (ts : Subst) {args : List (LExpr T.mono)} (hlen : args.length = fn.inputs.length)
    (hargs : ∀ a ∈ args, a.NamesIn S) :
    (LExpr.substFvarsLifting (body.applyTypeSubst ts) (fn.inputs.keys.zip args)).NamesIn S := by
  refine LExpr.NamesIn.substFvarsLifting
    (fun x r hr => hargs r (Map.find?_zip_mem _ _ x r hr)) (LExpr.NamesIn.applyTypeSubst ?_)
  intro x ty hx
  right
  have hname : x.name ∈ fn.inputs.map (·.1.name) :=
    hwf.body_freevars body hb (List.mem_map.mpr ⟨(x, ty), hx, rfl⟩)
  obtain ⟨⟨k, kty⟩, hk, hkx⟩ := List.mem_map.mp hname
  have hkx' : k = x := by
    cases k; cases x
    simp only at hkx
    subst hkx
    congr 1
    exact Subsingleton.elim _ _
  subst hkx'
  apply Map.find?_zip_isSome
  · rw [ListMap.keys_eq_map_fst]
    exact (List.length_map (as := (fn.inputs : List (T.Identifier × LMonoTy))) _).trans hlen.symm
  · rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨_, hk, rfl⟩

/-- **A reduction step introduces no free variable.** Under a well-formed factory, the free
variables of a reduct satisfy every predicate that those of the source and of the
environment's values satisfy. -/
theorem Step.namesIn [DecidableEq T.Metadata] [DecidableEq T.IDMeta] [Inhabited T.IDMeta]
    [Subsingleton T.IDMeta] {F : @Factory T}
    (hF : FactoryWF F) {env : Env T} {S : T.Identifier → Prop}
    (henv : ∀ x r, env x = some r → r.NamesIn S) {e e' : LExpr T.mono}
    (hs : Step F env e e') (he : e.NamesIn S) : e'.NamesIn S := by
  induction hs with
  | expand_fvar x r hx => exact LExpr.NamesIn.replaceMetadata1.mpr (henv x r hx)
  | beta e1 e2 eres h =>
    subst h
    simp only [LExpr.NamesIn.app, LExpr.NamesIn.abs] at he
    exact LExpr.NamesIn.substK (fun _ => he.2) he.1
  | reduce_2 _ _ _ _ ih =>
    simp only [LExpr.NamesIn.app] at he ⊢; exact ⟨he.1, ih he.2⟩
  | reduce_1 _ _ _ _ ih =>
    simp only [LExpr.NamesIn.app] at he ⊢; exact ⟨ih he.1, he.2⟩
  | ite_reduce_then => simp only [LExpr.NamesIn.ite] at he; exact he.2.1
  | ite_reduce_else => simp only [LExpr.NamesIn.ite] at he; exact he.2.2
  | ite_reduce_cond _ _ _ _ _ ih =>
    simp only [LExpr.NamesIn.ite] at he ⊢; exact ⟨ih he.1, he.2⟩
  | ite_reduce_then_branch _ _ _ _ _ ih =>
    simp only [LExpr.NamesIn.ite] at he ⊢; exact ⟨he.1, ih he.2.1, he.2.2⟩
  | ite_reduce_else_branch _ _ _ _ _ ih =>
    simp only [LExpr.NamesIn.ite] at he ⊢; exact ⟨he.1, he.2.1, ih he.2.2⟩
  | eq_reduce_true | eq_reduce_false => exact LExpr.NamesIn.const
  | eq_reduce_lhs _ _ _ _ ih =>
    simp only [LExpr.NamesIn.eq] at he ⊢; exact ⟨ih he.1, he.2⟩
  | eq_reduce_rhs _ _ _ _ ih =>
    simp only [LExpr.NamesIn.eq] at he ⊢; exact ⟨he.1, ih he.2⟩
  | expand_fn e callee body nb args fn ts hc hb _ hnb =>
    subst hnb
    exact expand_namesIn (hF.lfuncs_wf fn (callOfLFunc_func_mem F e callee args fn false hc))
      hb ts (Factory.callOfLFunc_arity hc) (callOfLFunc_args_namesIn hc he)
  | eval_fn e callee e' args fn ceval hc hce hres =>
    intro z ty hz
    have hwf := hF.lfuncs_wf fn (callOfLFunc_func_mem F e callee args fn false hc)
    have hzv : z ∈ LExpr.LExpr.getVars e' := by
      rw [getVars_eq_freeVars_idents]; exact List.mem_map.mpr ⟨_, hz, rfl⟩
    obtain ⟨a, ha, hza⟩ := hwf.concreteEval_freeVars ceval hce _ _ args e' hres.symm z hzv
    rw [getVars_eq_freeVars_idents] at hza
    obtain ⟨⟨_, tya⟩, hmem, rfl⟩ := List.mem_map.mp hza
    exact callOfLFunc_args_namesIn hc he a ha _ tya hmem
  | abs_subst_fvars =>
    simp only [LExpr.NamesIn.abs] at he ⊢
    exact LExpr.NamesIn.substFvarsFromEnv henv (LExpr.NamesIn.mono (fun _ h => .inl h) he)
  | quant_subst_fvars_body =>
    simp only [LExpr.NamesIn.quant] at he ⊢
    exact ⟨he.1,
      LExpr.NamesIn.substFvarsFromEnv henv (LExpr.NamesIn.mono (fun _ h => .inl h) he.2)⟩
  | quant_subst_fvars_trigger =>
    simp only [LExpr.NamesIn.quant] at he ⊢
    exact ⟨LExpr.NamesIn.substFvarsFromEnv henv (LExpr.NamesIn.mono (fun _ h => .inl h) he.1),
      he.2⟩

/-- **A reduction introduces no free variable**: `Step.namesIn`, along a sequence of steps. -/
theorem StepStar.namesIn [DecidableEq T.Metadata] [DecidableEq T.IDMeta] [Inhabited T.IDMeta]
    [Subsingleton T.IDMeta] {F : @Factory T}
    (hF : FactoryWF F) {env : Env T} {S : T.Identifier → Prop}
    (henv : ∀ x r, env x = some r → r.NamesIn S) {e e' : LExpr T.mono}
    (hs : StepStar F env e e') (he : e.NamesIn S) : e'.NamesIn S := by
  induction hs with
  | refl => exact he
  | step _ _ _ h _ ih => exact ih (Step.namesIn hF henv h he)

end NamesIn

/-! ## Reduction brings in only the factory's operators

A reduction step under a factory whose function bodies mention only its own functions, and
whose concrete evaluators return only operators of the factory or of their arguments
(`Factory.OpsClosed`), keeps the operators of an expression within any set of names that
contains them, the operators of the environment's values and the factory's functions
(`Step.opsIn`, `StepStar.opsIn`). -/

section OpsIn

variable {T : LExprParams}

/-- **The factory brings in only its own operators.** Every function body mentions only
    functions of `F`, and every concrete evaluator returns an expression whose operators are
    functions of `F` or operators of its arguments. -/
@[expose] def Factory.OpsClosed (F : @Factory T) : Prop :=
  (∀ fn ∈ F.toArray, ∀ body, fn.body = some body → body.OpsIn (fun o => o.name ∈ F)) ∧
  (∀ fn ∈ F.toArray, ∀ ceval, fn.concreteEval = some ceval → ∀ md opTy args r,
    ceval md opTy args = some r →
      r.OpsIn (fun o => o.name ∈ F ∨ ∃ a ∈ args, o ∈ LExpr.getOps a))

namespace LExpr.OpsIn

variable {S : T.Identifier → Prop}

/-- A constant has no operator. -/
@[simp] theorem const {m c} : (LExpr.const m c : LExpr T.mono).OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps]

/-- A bound variable has no operator. -/
@[simp] theorem bvar {m i} : (LExpr.bvar m i : LExpr T.mono).OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps]

/-- A free variable has no operator. -/
@[simp] theorem fvar {m x ty} : (LExpr.fvar m x ty : LExpr T.mono).OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps]

/-- An operator satisfies `S` exactly when its name does. -/
@[simp] theorem op {m o ty} : (LExpr.op m o ty : LExpr T.mono).OpsIn S ↔ S o := by
  simp [LExpr.OpsIn, LExpr.getOps]

/-- Replacing the root metadata keeps the operators. -/
@[simp] theorem replaceMetadata1 {m} {e : LExpr T.mono} :
    (LExpr.replaceMetadata1 m e).OpsIn S ↔ e.OpsIn S := by
  cases e <;> simp [LExpr.replaceMetadata1, LExpr.OpsIn, LExpr.getOps]

/-- An abstraction has the operators of its body. -/
@[simp] theorem abs {m n ty} {b : LExpr T.mono} : (LExpr.abs m n ty b).OpsIn S ↔ b.OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps]

/-- A quantifier has the operators of its trigger and its body. -/
@[simp] theorem quant {m qk n ty} {tr b : LExpr T.mono} :
    (LExpr.quant m qk n ty tr b).OpsIn S ↔ tr.OpsIn S ∧ b.OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps, or_imp, forall_and]

/-- An application has the operators of its function and its argument. -/
@[simp] theorem app {m} {f a : LExpr T.mono} :
    (LExpr.app m f a).OpsIn S ↔ f.OpsIn S ∧ a.OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps, or_imp, forall_and]

/-- An equality has the operators of its two sides. -/
@[simp] theorem eq {m} {a b : LExpr T.mono} :
    (LExpr.eq m a b).OpsIn S ↔ a.OpsIn S ∧ b.OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps, or_imp, forall_and]

/-- A conditional has the operators of its condition and its two branches. -/
@[simp] theorem ite {m} {c t f : LExpr T.mono} :
    (LExpr.ite m c t f).OpsIn S ↔ c.OpsIn S ∧ t.OpsIn S ∧ f.OpsIn S := by
  simp [LExpr.OpsIn, LExpr.getOps, or_imp, forall_and]

/-- A predicate that the operators satisfy can be weakened. -/
theorem mono {S' : T.Identifier → Prop} (h : ∀ x, S x → S' x) {e : LExpr T.mono}
    (he : e.OpsIn S) : e.OpsIn S' := fun o ho => h o (he o ho)

/-- Substituting for a bound variable an expression whose operators satisfy `S` keeps them in
    `S`. -/
theorem substK {s : T.Metadata → LExpr T.mono} (hs : ∀ m, (s m).OpsIn S) :
    ∀ {k : Nat} {e : LExpr T.mono}, e.OpsIn S → (LExpr.substK k s e).OpsIn S := by
  intro k e
  induction e generalizing k with
  | bvar m i =>
    intro _
    simp only [LExpr.substK]
    split
    · exact hs m
    · exact bvar
  | const | op | fvar => intro he; simpa only [LExpr.substK] using he
  | abs _ _ _ _ ih => simp only [LExpr.substK, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    simp only [LExpr.substK, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    simp only [LExpr.substK, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    simp only [LExpr.substK, ite]; exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    simp only [LExpr.substK, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

/-- Shifting bound variables keeps the operators. -/
theorem liftBVars {n : Nat} : ∀ {e : LExpr T.mono} {c : Nat},
    e.OpsIn S → (LExpr.liftBVars n e c).OpsIn S := by
  intro e
  induction e with
  | bvar m i => intro c _; simp only [LExpr.liftBVars]; split <;> exact bvar
  | const | op | fvar => intro c he; simpa only [LExpr.liftBVars] using he
  | abs _ _ _ _ ih => intro c; simp only [LExpr.liftBVars, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    intro c; simp only [LExpr.liftBVars, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    intro c; simp only [LExpr.liftBVars, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    intro c; simp only [LExpr.liftBVars, ite]
    exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    intro c; simp only [LExpr.liftBVars, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

/-- Instantiating type variables keeps the operators. -/
theorem applyTypeSubst {S' : Subst} {e : LExpr T.mono} (he : e.OpsIn S) :
    (e.applyTypeSubst S').OpsIn S := by
  intro o ho; rw [LExpr.getOps_applyTypeSubst] at ho; exact he o ho

/-- Substituting for free variables expressions whose operators satisfy `S` keeps them in
    `S`. -/
theorem substFvarsLifting [DecidableEq T.IDMeta] {sm : Map T.Identifier (LExpr T.mono)}
    (hsm : ∀ x r, sm.find? x = some r → r.OpsIn S) {e : LExpr T.mono} (he : e.OpsIn S) :
    (LExpr.substFvarsLifting e sm).OpsIn S := by
  unfold LExpr.substFvarsLifting
  split
  · exact he
  · suffices ∀ (e : LExpr T.mono) d, e.OpsIn S → (LExpr.substFvarsLifting.go sm e d).OpsIn S
      from this e 0 he
    intro e
    induction e with
    | const | op | bvar => intro d h; simpa only [LExpr.substFvarsLifting.go] using h
    | fvar m x ty =>
      intro d h
      simp only [LExpr.substFvarsLifting.go]
      split
      · rename_i r hr; exact replaceMetadata1.mpr (liftBVars (hsm x r hr))
      · exact h
    | abs _ _ _ _ ih => intro d; simp only [LExpr.substFvarsLifting.go, abs]; exact ih _
    | quant _ _ _ _ _ _ ihtr ihb =>
      intro d; simp only [LExpr.substFvarsLifting.go, quant]
      exact fun ⟨h₁, h₂⟩ => ⟨ihtr _ h₁, ihb _ h₂⟩
    | app _ _ _ ihf iha =>
      intro d; simp only [LExpr.substFvarsLifting.go, app]
      exact fun ⟨h₁, h₂⟩ => ⟨ihf _ h₁, iha _ h₂⟩
    | ite _ _ _ _ ihc iht ihf =>
      intro d; simp only [LExpr.substFvarsLifting.go, ite]
      exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc _ h₁, iht _ h₂, ihf _ h₃⟩
    | eq _ _ _ iha ihb =>
      intro d; simp only [LExpr.substFvarsLifting.go, eq]
      exact fun ⟨h₁, h₂⟩ => ⟨iha _ h₁, ihb _ h₂⟩

/-- Substituting the environment's values for free variables keeps the operators in `S` when
    the values' operators are. -/
theorem substFvarsFromEnv {env : Env T} (henv : ∀ x r, env x = some r → r.OpsIn S) :
    ∀ {e : LExpr T.mono}, e.OpsIn S → (LExpr.substFvarsFromEnv env e).OpsIn S := by
  intro e
  induction e with
  | const | op | bvar => intro h; simpa only [LExpr.substFvarsFromEnv] using h
  | fvar m x ty =>
    intro h
    simp only [LExpr.substFvarsFromEnv]
    split
    · rename_i r hr; exact replaceMetadata1.mpr (henv x r hr)
    · exact h
  | abs _ _ _ _ ih => simp only [LExpr.substFvarsFromEnv, abs]; exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    simp only [LExpr.substFvarsFromEnv, quant]; exact fun ⟨h₁, h₂⟩ => ⟨ihtr h₁, ihb h₂⟩
  | app _ _ _ ihf iha =>
    simp only [LExpr.substFvarsFromEnv, app]; exact fun ⟨h₁, h₂⟩ => ⟨ihf h₁, iha h₂⟩
  | ite _ _ _ _ ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv, ite]
    exact fun ⟨h₁, h₂, h₃⟩ => ⟨ihc h₁, iht h₂, ihf h₃⟩
  | eq _ _ _ iha ihb =>
    simp only [LExpr.substFvarsFromEnv, eq]; exact fun ⟨h₁, h₂⟩ => ⟨iha h₁, ihb h₂⟩

end LExpr.OpsIn

/-- The arguments of a call are subterms of it, so they have no operator it has not. -/
private theorem callOfLFunc_args_opsIn {S : T.Identifier → Prop} {F : @Factory T}
    {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hc : F.callOfLFunc e = some (callee, args, fn)) (he : e.OpsIn S) :
    ∀ a ∈ args, a.OpsIn S :=
  callOfLFunc_args_sat (fun h => LExpr.OpsIn.app.mp h) hc he

/-- **A reduction step brings in only the factory's operators.** Under a factory that brings in
only its own operators, the operators of a reduct satisfy every predicate that those of the
source, of the environment's values and the factory's functions satisfy. -/
theorem Step.opsIn [DecidableEq T.IDMeta] [Inhabited T.IDMeta] {F : @Factory T}
    (hF : F.OpsClosed) {env : Env T}
    {S : T.Identifier → Prop} (hFS : ∀ o : T.Identifier, o.name ∈ F → S o)
    (henv : ∀ x r, env x = some r → r.OpsIn S) {e e' : LExpr T.mono}
    (hs : Step F env e e') (he : e.OpsIn S) : e'.OpsIn S := by
  induction hs with
  | expand_fvar x r hx => exact LExpr.OpsIn.replaceMetadata1.mpr (henv x r hx)
  | beta e1 e2 eres h =>
    subst h
    simp only [LExpr.OpsIn.app, LExpr.OpsIn.abs] at he
    exact LExpr.OpsIn.substK (fun _ => he.2) he.1
  | reduce_2 _ _ _ _ ih =>
    simp only [LExpr.OpsIn.app] at he ⊢; exact ⟨he.1, ih he.2⟩
  | reduce_1 _ _ _ _ ih =>
    simp only [LExpr.OpsIn.app] at he ⊢; exact ⟨ih he.1, he.2⟩
  | ite_reduce_then => simp only [LExpr.OpsIn.ite] at he; exact he.2.1
  | ite_reduce_else => simp only [LExpr.OpsIn.ite] at he; exact he.2.2
  | ite_reduce_cond _ _ _ _ _ ih =>
    simp only [LExpr.OpsIn.ite] at he ⊢; exact ⟨ih he.1, he.2⟩
  | ite_reduce_then_branch _ _ _ _ _ ih =>
    simp only [LExpr.OpsIn.ite] at he ⊢; exact ⟨he.1, ih he.2.1, he.2.2⟩
  | ite_reduce_else_branch _ _ _ _ _ ih =>
    simp only [LExpr.OpsIn.ite] at he ⊢; exact ⟨he.1, he.2.1, ih he.2.2⟩
  | eq_reduce_true | eq_reduce_false => exact LExpr.OpsIn.const
  | eq_reduce_lhs _ _ _ _ ih =>
    simp only [LExpr.OpsIn.eq] at he ⊢; exact ⟨ih he.1, he.2⟩
  | eq_reduce_rhs _ _ _ _ ih =>
    simp only [LExpr.OpsIn.eq] at he ⊢; exact ⟨he.1, ih he.2⟩
  | expand_fn e callee body nb args fn ts hc hb _ hnb =>
    subst hnb
    have hmem := callOfLFunc_func_mem F e callee args fn false hc
    exact LExpr.OpsIn.substFvarsLifting
      (fun _ r hr => callOfLFunc_args_opsIn hc he r (Map.find?_zip_mem _ _ _ r hr))
      (LExpr.OpsIn.applyTypeSubst (LExpr.OpsIn.mono (fun o ho => hFS o ho) (hF.1 fn hmem body hb)))
  | eval_fn e callee e' args fn ceval hc hce hres =>
    have hmem := callOfLFunc_func_mem F e callee args fn false hc
    intro o ho
    rcases hF.2 fn hmem ceval hce _ _ args e' hres.symm o ho with h | ⟨a, ha, hoa⟩
    · exact hFS o h
    · exact callOfLFunc_args_opsIn hc he a ha o hoa
  | abs_subst_fvars =>
    simp only [LExpr.OpsIn.abs] at he ⊢
    exact LExpr.OpsIn.substFvarsFromEnv henv he
  | quant_subst_fvars_body =>
    simp only [LExpr.OpsIn.quant] at he ⊢
    exact ⟨he.1, LExpr.OpsIn.substFvarsFromEnv henv he.2⟩
  | quant_subst_fvars_trigger =>
    simp only [LExpr.OpsIn.quant] at he ⊢
    exact ⟨LExpr.OpsIn.substFvarsFromEnv henv he.1, he.2⟩

/-- **A reduction brings in only the factory's operators**: `Step.opsIn`, along a sequence of
    steps. -/
theorem StepStar.opsIn [DecidableEq T.IDMeta] [Inhabited T.IDMeta] {F : @Factory T}
    (hF : F.OpsClosed)
    {env : Env T} {S : T.Identifier → Prop} (hFS : ∀ o : T.Identifier, o.name ∈ F → S o)
    (henv : ∀ x r, env x = some r → r.OpsIn S) {e e' : LExpr T.mono}
    (hs : StepStar F env e e') (he : e.OpsIn S) : e'.OpsIn S := by
  induction hs with
  | refl => exact he
  | step _ _ _ h _ ih => exact ih (Step.opsIn hF hFS henv h he)

end OpsIn

end -- public section
end Lambda
