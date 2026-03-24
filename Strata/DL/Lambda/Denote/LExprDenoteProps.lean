/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Denote.HList

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp T tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### HList cast applied to SortDenote -/

/-- Casting the argument list of `applyArgs` can be absorbed by casting the
sort in the applied function. In particular, for `opInterp`-style functions
that take the sort as a parameter, this lets us move between equivalent
index representations. -/
theorem SortDenote.applyArgs_cast_eq {xs ys : List LSort} {ret : LSort}
    (h : xs = ys)
    (g : (s : LSort) → SortDenote tcInterp s)
    (args : HList (SortDenote tcInterp) xs)
    : SortDenote.applyArgs tcInterp (g (LSort.mkArrow ret xs)) args =
      SortDenote.applyArgs tcInterp (g (LSort.mkArrow ret ys)) (HList.cast h args) := by
  subst h; rfl

/-! ### Denotation irrelevance for locally closed expressions -/

/-- Generalized denotation irrelevance: if `lcAt |Δ₁| e`, then the denotation
    depends only on the prefix `bv₁` (of length `|Δ₁|`), not the suffix. -/
theorem denote_suffix_irrel
    {e : LExpr T.mono} {τ : LMonoTy}
    {Δ₁ : List LMonoTy} {Δ₂ Δ₂' : List LMonoTy}
    (h_lc : LExpr.lcAt Δ₁.length e = true)
    (h₁ : LExpr.HasTypeA (Δ₁ ++ Δ₂) e τ)
    (h₂ : LExpr.HasTypeA (Δ₁ ++ Δ₂') e τ)
    (bv₁ : BVarVal tcInterp vt Δ₁)
    (bv₂ : BVarVal tcInterp vt Δ₂)
    (bv₂' : BVarVal tcInterp vt Δ₂')
    : LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂) e τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂') e τ h₂ := by
  induction e generalizing Δ₁ τ with
  | const => rfl
  | op _ _ ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some => rfl
  | fvar _ _ ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some => rfl
  | bvar m i =>
    simp [LExpr.lcAt] at h_lc
    rw [denote_bvar _ _ _ _ (HList.append bv₁ bv₂) h₁, denote_bvar _ _ _ _ (HList.append bv₁ bv₂') h₂]
    have h_prefix : Δ₁[i]? = some τ := by
      have h_app := HasTypeA.bvar_inv h₁
      rw [List.getElem?_append_left (by omega)] at h_app
      exact h_app
    rw [HList.get_append_left bv₁ bv₂ i (HasTypeA.bvar_inv h₁) h_prefix]
    rw [HList.get_append_left bv₁ bv₂' i (HasTypeA.bvar_inv h₂) h_prefix]
  | app _ fn arg ih_fn ih_arg =>
    have ⟨aty, h_fn₁, h_arg₁⟩ := HasTypeA.app_inv h₁
    have ⟨aty', h_fn₂, h_arg₂⟩ := HasTypeA.app_inv h₂
    simp [LExpr.lcAt, Bool.and_eq_true] at h_lc
    have h_aty : aty = aty' := by
      have h_tc₁ := LExpr.HasTypeA_to_typeCheck h_fn₁
      have h_tc₂ := LExpr.HasTypeA_to_typeCheck h_fn₂
      have h_eq := typeCheck_of_lcAt_aux (Δ := Δ₁ ++ Δ₂) (Δ' := Δ₁ ++ Δ₂') h_lc.1 (fun i hi => by
        rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)])
      rw [h_eq] at h_tc₁
      rw [h_tc₁] at h_tc₂
      cases h_tc₂
      rfl
    subst h_aty
    rw [denote_app _ h_fn₁ h_arg₁ h₁, denote_app _ h_fn₂ h_arg₂ h₂]
    rw [ih_fn h_lc.1 h_fn₁ h_fn₂ bv₁, ih_arg h_lc.2 h_arg₁ h_arg₂ bv₁]
  | ite _ c t e ih_c ih_t ih_e =>
    have ⟨h_c₁, h_t₁, h_e₁⟩ := HasTypeA.ite_inv h₁
    have ⟨h_c₂, h_t₂, h_e₂⟩ := HasTypeA.ite_inv h₂
    rw [denote_ite _ h_c₁ h_t₁ h_e₁, denote_ite _ h_c₂ h_t₂ h_e₂]
    simp [LExpr.lcAt, Bool.and_eq_true] at h_lc
    rw [ih_c h_lc.1.1 h_c₁ h_c₂ bv₁, ih_t h_lc.1.2 h_t₁ h_t₂ bv₁, ih_e h_lc.2 h_e₁ h_e₂ bv₁]
  | eq _ e1 e2 ih1 ih2 =>
    have ⟨ty', h_bool₁, h_1₁, h_2₁⟩ := HasTypeA.eq_inv h₁
    have ⟨ty'', h_bool₂, h_1₂, h_2₂⟩ := HasTypeA.eq_inv h₂
    subst h_bool₁; cases h_bool₂
    simp [LExpr.lcAt, Bool.and_eq_true] at h_lc
    have h_ty : ty' = ty'' := by
      have h_tc₁ := LExpr.HasTypeA_to_typeCheck h_1₁
      have h_tc₂ := LExpr.HasTypeA_to_typeCheck h_1₂
      have h_eq := typeCheck_of_lcAt_aux (Δ := Δ₁ ++ Δ₂) (Δ' := Δ₁ ++ Δ₂') h_lc.1
        (fun i hi => by rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)])
      rw [h_eq] at h_tc₁; rw [h_tc₁] at h_tc₂; exact Option.some.inj h_tc₂
    subst h_ty
    by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂) e1 ty' h_1₁ =
        LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂) e2 ty' h_2₁
    · rw [denote_eq_true _ h_1₁ h_2₁ h₁ heq, denote_eq_true _ h_1₂ h_2₂ h₂
            (by rw [← ih1 h_lc.1 h_1₁ h_1₂ bv₁, ← ih2 h_lc.2 h_2₁ h_2₂ bv₁]; exact heq)]
    · rw [denote_eq_false _ h_1₁ h_2₁ h₁ heq, denote_eq_false _ h_1₂ h_2₂ h₂
            (by rw [← ih1 h_lc.1 h_1₁ h_1₂ bv₁, ← ih2 h_lc.2 h_2₁ h_2₂ bv₁]; exact heq)]
  | abs _ _ ty body ih_body =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some aty =>
      have ⟨_, h_eq₁, h_body₁⟩ := HasTypeA.abs_inv h₁
      have ⟨_, h_eq₂, h_body₂⟩ := HasTypeA.abs_inv h₂
      subst h_eq₁; cases h_eq₂
      rw [denote_abs _ h_body₁ h₁, denote_abs _ h_body₂ h₂]
      funext x
      simp [LExpr.lcAt] at h_lc
      have h_len : (aty :: Δ₁).length = Δ₁.length + 1 := by simp
      exact ih_body (h_len ▸ h_lc) h_body₁ h_body₂ (.cons x bv₁)
  | quant _ qk _ ty tr body ih_tr ih_body =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some qty =>
      simp [LExpr.lcAt, Bool.and_eq_true] at h_lc
      have ⟨_, h_τ₁, h_tr₁, h_body₁⟩ := HasTypeA.quant_inv h₁
      have ⟨_, h_τ₂, h_tr₂, h_body₂⟩ := HasTypeA.quant_inv h₂
      subst h_τ₁; cases h_τ₂
      have h_len : (qty :: Δ₁).length = Δ₁.length + 1 := by simp
      cases qk with
      | all =>
        by_cases hall : ∀ x : TyDenote tcInterp vt qty,
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bv₁ bv₂)) body .bool h_body₁ : Bool) = true
        · rw [denote_quant_all_true _ h_body₁ h₁ hall]
          symm; apply denote_quant_all_true _ h_body₂ h₂
          intro x
          specialize ih_body (h_len ▸ h_lc.2) h_body₁ h_body₂ (.cons x bv₁)
          simp only [HList.append] at ih_body
          rw [← ih_body]; exact hall x
        · have ⟨w, hw⟩ := Classical.not_forall.mp hall
          have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w (HList.append bv₁ bv₂)) body .bool h_body₁ : Bool) = false :=
            Bool.eq_false_iff.mpr hw
          rw [denote_quant_all_false _ h_body₁ h₁ w hwf]
          symm; apply denote_quant_all_false _ h_body₂ h₂ w
          specialize ih_body (h_len ▸ h_lc.2) h_body₁ h_body₂ (.cons w bv₁)
          simp only [HList.append] at ih_body
          rw [← ih_body]; exact hwf
      | exist =>
        by_cases hexist : ∃ x : TyDenote tcInterp vt qty,
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bv₁ bv₂)) body .bool h_body₁ : Bool) = true
        · obtain ⟨w, hw⟩ := hexist
          rw [denote_quant_exist_true _ h_body₁ h₁ w hw]
          symm; apply denote_quant_exist_true _ h_body₂ h₂ w
          specialize ih_body (h_len ▸ h_lc.2) h_body₁ h_body₂ (.cons w bv₁)
          simp only [HList.append] at ih_body
          rw [← ih_body]; exact hw
        · have hexist_f : ∀ x : TyDenote tcInterp vt qty,
              (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bv₁ bv₂)) body .bool h_body₁ : Bool) = false :=
            fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
          rw [denote_quant_exist_false _ h_body₁ h₁ hexist_f]
          symm; apply denote_quant_exist_false _ h_body₂ h₂
          intro x
          specialize ih_body (h_len ▸ h_lc.2) h_body₁ h_body₂ (.cons x bv₁)
          simp only [HList.append] at ih_body
          rw [← ih_body]; exact hexist_f x

/-- Special case: if `lcAt 0 e`, the denotation is independent of the
    entire bound-variable valuation. -/
theorem denote_irrel_of_lcAt
    {e : LExpr T.mono} {τ : LMonoTy}
    {Δ₁ Δ₂ : List LMonoTy}
    (h_lc : LExpr.lcAt 0 e = true)
    (h₁ : LExpr.HasTypeA Δ₁ e τ)
    (h₂ : LExpr.HasTypeA Δ₂ e τ)
    (bv₁ : BVarVal tcInterp vt Δ₁)
    (bv₂ : BVarVal tcInterp vt Δ₂)
    : LExpr.denote tcInterp opInterp fvarVal vt bv₁ e τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt bv₂ e τ h₂ := by
  exact denote_suffix_irrel (Δ₁ := []) _ _ _ _ h_lc h₁ h₂ HList.nil bv₁ bv₂

/-! ### Metadata Doesn't Affect Typing or Denotations -/

-- Easier to prove by computation than via HasTypeA directly
theorem replaceMetadata_typeCheck {e: LExpr T.mono}
  (f : T.Metadata → NewMetadata):
  LExpr.typeCheck Δ e = LExpr.typeCheck Δ (e.replaceMetadata f) := by
  induction e generalizing Δ <;> simp[LExpr.replaceMetadata, LExpr.typeCheck] <;> try grind
  case op m o ty => cases ty <;> simp[LExpr.typeCheck]
  case fvar m name ty => cases ty <;> simp[LExpr.typeCheck]
  case abs m name ty body IH =>
    cases ty <;> simp[LExpr.typeCheck, IH]
  case quant m k name ty tr body IHtr IH =>
    cases ty <;> simp[LExpr.typeCheck, IH, IHtr]

theorem replaceMetadata_HasTypeA {e: LExpr T.mono}
  (f : T.Metadata → NewMetadata)
  (h₁ : LExpr.HasTypeA Δ e τ):
  LExpr.HasTypeA Δ (LExpr.replaceMetadata e f) τ := by
  rw[LExpr.HasTypeA_iff_typeCheck ] at h₁ |-
  rw[←replaceMetadata_typeCheck]
  exact h₁

theorem denote_replaceMetadata
    {T : LExprParams} [Inhabited T.mono.base.IDMeta]
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp T tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    {e₁ : LExpr T.mono} {τ : LMonoTy} (f : T.Metadata → NewMetadata)
    (h₁ : LExpr.HasTypeA Δ e₁ τ):
    let T' : LExprParams := ⟨NewMetadata, T.IDMeta⟩
    let opInterp' : OpInterp T' tcInterp := opInterp
    let fvarVal' : FreeVarVal T' tcInterp := fvarVal
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₁ τ h₁ =
    LExpr.denote tcInterp opInterp' fvarVal' vt bvarVal (LExpr.replaceMetadata e₁ f) τ (replaceMetadata_HasTypeA f h₁) := by
    induction e₁ generalizing Δ τ with
    | const m c =>
      cases h₁ with | const => simp [LExpr.replaceMetadata, LExpr.denote]
    | op m o ty =>
      cases ty with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
      | some ty => cases h₁ with | op => simp [LExpr.replaceMetadata, LExpr.denote]
    | fvar m x ty =>
      cases ty with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
      | some ty => cases h₁ with | fvar => simp [LExpr.replaceMetadata, LExpr.denote]
    | bvar m i =>
      cases h₁ with | bvar h_lookup => simp [LExpr.replaceMetadata, LExpr.denote]
    | app m fn arg ih_fn ih_arg =>
      have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h₁
      have h_fn' := replaceMetadata_HasTypeA f h_fn
      have h_arg' := replaceMetadata_HasTypeA f h_arg
      have h_app' : LExpr.HasTypeA Δ (.app (f m) (fn.replaceMetadata f) (arg.replaceMetadata f)) τ :=
        .app h_fn' h_arg'
      rw [denote_app bvarVal h_fn h_arg h₁]
      simp only [LExpr.replaceMetadata]
      rw [denote_app bvarVal h_fn' h_arg' h_app',
          ih_fn bvarVal h_fn, ih_arg bvarVal h_arg]
    | abs m name ty body ih_body =>
      cases ty with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
      | some aty =>
        cases h₁ with
        | abs h_body =>
          rename_i rty
          have h_body' := replaceMetadata_HasTypeA f h_body
          rw [denote_abs bvarVal h_body (LExpr.HasTypeA.abs h_body)]
          simp only [LExpr.replaceMetadata]
          rw [denote_abs bvarVal h_body' (.abs h_body')]
          funext x
          exact ih_body (.cons x bvarVal) h_body
    | ite m c t e ih_c ih_t ih_e =>
      cases h₁ with
      | ite h_c h_t h_e =>
        have h_c' := replaceMetadata_HasTypeA f h_c
        have h_t' := replaceMetadata_HasTypeA f h_t
        have h_e' := replaceMetadata_HasTypeA f h_e
        rw [denote_ite bvarVal h_c h_t h_e]
        simp only [LExpr.replaceMetadata]
        rw [denote_ite bvarVal h_c' h_t' h_e' (.ite h_c' h_t' h_e'),
            ih_c bvarVal h_c, ih_t bvarVal h_t, ih_e bvarVal h_e]
    | eq m e1 e2 ih1 ih2 =>
      cases h₁ with
      | eq h_1 h_2 =>
        have h_1' := replaceMetadata_HasTypeA f h_1
        have h_2' := replaceMetadata_HasTypeA f h_2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 _ h_1 =
          LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 _ h_2
        · rw [denote_eq_true bvarVal h_1 h_2 _ heq]
          simp only [LExpr.replaceMetadata]
          rw [denote_eq_true bvarVal h_1' h_2' (.eq h_1' h_2')
                (by rw [← ih1 bvarVal h_1, ← ih2 bvarVal h_2]; exact heq)]
        · rw [denote_eq_false bvarVal h_1 h_2 _ heq]
          simp only [LExpr.replaceMetadata]
          rw [denote_eq_false bvarVal h_1' h_2' (.eq h_1' h_2')
                (by rw [← ih1 bvarVal h_1, ← ih2 bvarVal h_2]; exact heq)]
    | quant m k name ty tr body ih_tr ih_body =>
      cases ty with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
      | some qty =>
        cases h₁ with
        | quant h_tr h_body =>
          have h_body' := replaceMetadata_HasTypeA f h_body
          have h_tr' := replaceMetadata_HasTypeA f h_tr
          cases k with
          | all =>
            by_cases hall : ∀ x : TyDenote tcInterp vt qty,
                (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true
            · rw [denote_quant_all_true bvarVal h_body _ hall]
              simp only [LExpr.replaceMetadata]
              exact (denote_quant_all_true bvarVal h_body' (.quant h_tr' h_body')
                (fun x => by rw [← ih_body (.cons x bvarVal) h_body]; exact hall x)).symm
            · have ⟨w, hw⟩ := Classical.not_forall.mp hall
              have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body : Bool) = false :=
                Bool.eq_false_iff.mpr hw
              rw [denote_quant_all_false bvarVal h_body _ w hwf]
              simp only [LExpr.replaceMetadata]
              exact (denote_quant_all_false bvarVal h_body' (.quant h_tr' h_body') w
                (by rw [← ih_body (.cons w bvarVal) h_body]; exact hwf)).symm
          | exist =>
            by_cases hexist : ∃ x : TyDenote tcInterp vt qty,
                (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true
            · obtain ⟨w, hw⟩ := hexist
              rw [denote_quant_exist_true bvarVal h_body _ w hw]
              simp only [LExpr.replaceMetadata]
              exact (denote_quant_exist_true bvarVal h_body' (.quant h_tr' h_body') w
                (by rw [← ih_body (.cons w bvarVal) h_body]; exact hw)).symm
            · have hexist_neg : ∀ x : TyDenote tcInterp vt qty,
                  ¬ ((LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true) :=
                fun x h => hexist ⟨x, h⟩
              have hexist_f : ∀ x : TyDenote tcInterp vt qty,
                  (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = false :=
                fun x => Bool.eq_false_iff.mpr (hexist_neg x)
              rw [denote_quant_exist_false bvarVal h_body _ hexist_f]
              simp only [LExpr.replaceMetadata]
              exact (denote_quant_exist_false bvarVal h_body' (.quant h_tr' h_body')
                (fun x => by rw [← ih_body (.cons x bvarVal) h_body]; exact hexist_f x)).symm
