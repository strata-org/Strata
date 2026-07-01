/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.LExprWF

/-!
## Properties of LState substitution operations

Theorems about `substFvarsFromEnv`:
- `eraseMetadata` congruence
- Simplification lemmas for specific constructors
-/

namespace Lambda
open Strata

/-- `substFvarsFromEnv` preserves `eraseMetadata` equality. -/
theorem LExpr.substFvarsFromEnv_eraseMetadata_congr
    {T : LExprParams} [DecidableEq T.IDMeta]
    (env : Env T) (e₁ e₂ : LExpr T.mono)
    (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.substFvarsFromEnv env e₁).eraseMetadata =
    (LExpr.substFvarsFromEnv env e₂).eraseMetadata := by
  induction e₁ generalizing e₂ with
  | const m c =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars; rfl
  | op m n t =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars; rfl
  | bvar m i =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    injection h; subst_vars; rfl
  | fvar m x ty =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂; injection h with _ h_x h_ty; subst h_x h_ty
    simp only [LExpr.substFvarsFromEnv]
    split <;> (first | rfl | simp [LExpr.eraseMetadata, LExpr.replaceMetadata])
  | abs m n t b ih =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ n₂ t₂ b₂; injection h with _ hn ht hb; subst hn ht
    have hb' : b.eraseMetadata = b₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hb
    simp only [LExpr.substFvarsFromEnv, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1; exact ih b₂ hb'
  | quant m qk n ty tr b ih_tr ih_b =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ qk₂ n₂ ty₂ tr₂ b₂; injection h with _ hqk hn hty htr hb; subst hqk hn hty
    have htr' : tr.eraseMetadata = tr₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact htr
    have hb' : b.eraseMetadata = b₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hb
    simp only [LExpr.substFvarsFromEnv, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · exact ih_tr tr₂ htr'
    · exact ih_b b₂ hb'
  | app m f a ihf iha =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ f₂ a₂; injection h with _ hf ha
    have hf' : f.eraseMetadata = f₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hf
    have ha' : a.eraseMetadata = a₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact ha
    simp only [LExpr.substFvarsFromEnv, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · exact ihf f₂ hf'
    · exact iha a₂ ha'
  | eq m l r ihl ihr =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ l₂ r₂; injection h with _ hl hr
    have hl' : l.eraseMetadata = l₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hl
    have hr' : r.eraseMetadata = r₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hr
    simp only [LExpr.substFvarsFromEnv, LExpr.eraseMetadata, LExpr.replaceMetadata]
    congr 1
    · exact ihl l₂ hl'
    · exact ihr r₂ hr'
  | ite m c t f ihc iht ihf =>
    cases e₂ <;> delta LExpr.eraseMetadata LExpr.replaceMetadata at h <;> try contradiction
    rename_i m₂ c₂ t₂ f₂; injection h with _ hc ht hf
    have hc' : c.eraseMetadata = c₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hc
    have ht' : t.eraseMetadata = t₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact ht
    have hf' : f.eraseMetadata = f₂.eraseMetadata := by delta LExpr.eraseMetadata LExpr.replaceMetadata; exact hf
    simp only [LExpr.substFvarsFromEnv, LExpr.eraseMetadata, LExpr.replaceMetadata]
    exact congr (congr (congrArg _ (ihc c₂ hc')) (iht t₂ ht')) (ihf f₂ hf')

/-- `substFvarsFromEnv` is the identity on closed expressions (no free variables). -/
theorem LExpr.substFvarsFromEnv_closed_identity
    {T : LExprParams} [DecidableEq T.IDMeta]
    (env : Env T) (e : LExpr T.mono)
    (h : LExpr.freeVars e = []) :
    LExpr.substFvarsFromEnv env e = e := by
  induction e with
  | const | bvar | op => rfl
  | fvar m name ty => simp [LExpr.freeVars] at h
  | abs m nm ty body ih =>
    simp only [LExpr.substFvarsFromEnv]
    congr 1; exact ih (by simp [LExpr.freeVars] at h; exact h)
  | quant m qk nm ty tr body ih_tr ih_body =>
    simp only [LExpr.substFvarsFromEnv]
    simp [LExpr.freeVars] at h
    congr 1
    · exact ih_tr h.1
    · exact ih_body h.2
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsFromEnv]
    simp [LExpr.freeVars] at h
    congr 1
    · exact ih_fn h.1
    · exact ih_arg h.2
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv]
    simp [LExpr.freeVars] at h
    congr 1
    · exact ih1 h.1
    · exact ih2 h.2
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv]
    simp [LExpr.freeVars] at h
    exact congr (congr (congr rfl (ihc h.1)) (iht h.2.1)) (ihf h.2.2)

end Lambda
