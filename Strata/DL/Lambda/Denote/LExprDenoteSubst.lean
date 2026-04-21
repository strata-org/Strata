/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.Util.Tactics

/-!
## Substitution and Denotation

Proves that bound-variable operations commute with denotation.

- `substK_denote` — generalized depth-k substitution commutes with `denote`
- `subst_denote` / `varOpen_denote` — substitution and variable opening commute with `denote`
- `liftBVars_denote` — lifting bound variable indices preserves denotation
- `substFvarsLifting_denote` — free variable substitution with lifting commutes with `denote`
-/

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### Generalized substK_denote -/

/-- Generalized substitution lemma: `substK k` at depth `k` in a context
    `Δ₁ ++ [aty]` with `|Δ₁| = k`. The substituted value `v` must be locally
    closed and well-typed in the empty context. -/
theorem substK_denote
    {body : LExpr T.mono} {s : T.mono.base.Metadata → LExpr T.mono}
    {aty τ : LMonoTy}
    {Δ₁ : List LMonoTy}
    {val : TyDenote tcInterp vt aty}
    (bvarVal₁ : BVarVal tcInterp vt Δ₁)
    (h_body : LExpr.HasTypeA (Δ₁ ++ [aty]) body τ)
    (h_v : ∀ m, LExpr.HasTypeA [] (s m) aty)
    (h_subst : LExpr.HasTypeA Δ₁ (LExpr.substK Δ₁.length s body) τ)
    (h_lc : ∀ m, LExpr.lcAt 0 (s m) = true)
    (h_denote_eq : ∀ m, LExpr.denote tcInterp opInterp fvarVal vt .nil (s m) aty (h_v m) = val)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal₁
        (LExpr.substK Δ₁.length s body) τ h_subst =
      LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal₁ (.cons val .nil))
        body τ h_body := by
  induction body generalizing Δ₁ τ with
  | const m c =>
    have h1 := HasTypeA.const_inv h_subst
    have h2 := HasTypeA.const_inv h_body
    subst h1
    exact (Denotes_denote (Denotes.const bvarVal₁)).symm.trans
          (Denotes_denote (Denotes.const _))
  | op m o ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some ty =>
      have h1 := HasTypeA.op_inv h_subst; subst h1
      exact (Denotes_denote (Denotes.op bvarVal₁)).symm.trans
            (Denotes_denote (Denotes.op _))
  | fvar m x ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some ty =>
      have h1 := HasTypeA.fvar_inv h_subst; subst h1
      exact (Denotes_denote (Denotes.fvar bvarVal₁)).symm.trans
            (Denotes_denote (Denotes.fvar _))
  | bvar m i =>
    simp only [LExpr.substK]
    split
    · rename_i h_eq
      have h_ieq : i = Δ₁.length := by grind
      subst h_ieq
      simp [LExpr.substK] at h_subst
      have h_lookup := HasTypeA.bvar_inv h_body
      simp at h_lookup; subst h_lookup
      rw [denote_irrel_of_lcAt tcInterp opInterp fvarVal vt (h_lc m) h_subst (h_v m) bvarVal₁ .nil]
      rw [h_denote_eq m]
      rw [denote_bvar tcInterp opInterp fvarVal vt _ h_body]
      exact (HList.get_append_cons_self bvarVal₁
        val .nil
        (HasTypeA.bvar_inv h_body)).symm
    · rename_i h_ne
      simp [LExpr.substK, h_ne] at h_subst
      rw [denote_bvar tcInterp opInterp fvarVal vt bvarVal₁ h_subst,
          denote_bvar tcInterp opInterp fvarVal vt _ h_body]
      exact (HList.get_append_left bvarVal₁ _ i (HasTypeA.bvar_inv h_body) (HasTypeA.bvar_inv h_subst)).symm
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substK] at h_subst ⊢
    let ⟨aty_b, h_fn_b, h_arg_b⟩ := HasTypeA.app_inv h_body
    let ⟨aty_s, h_fn_s, h_arg_s⟩ := HasTypeA.app_inv h_subst
    have h_aty : aty_s = aty_b := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_fn_s
      rw [substK_typeCheck h_v] at h1
      have h2 := LExpr.HasTypeA_to_typeCheck h_fn_b
      rw [h1] at h2; cases h2; rfl
    subst h_aty
    rw [denote_app bvarVal₁ h_fn_s h_arg_s h_subst,
        denote_app _ h_fn_b h_arg_b h_body,
        ih_fn bvarVal₁ h_fn_b h_fn_s,
        ih_arg bvarVal₁ h_arg_b h_arg_s]
  | abs m name ty sub_body ih =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some aty' =>
      simp only [LExpr.substK] at h_subst ⊢
      let ⟨rty_b, h_eq_b, h_body_b⟩ := HasTypeA.abs_inv h_body
      let ⟨rty_s, h_eq_s, h_body_s⟩ := HasTypeA.abs_inv h_subst
      subst h_eq_b
      cases h_eq_s
      rw [denote_abs bvarVal₁ h_body_s h_subst,
          denote_abs _ h_body_b h_body]
      funext x
      exact ih (.cons x bvarVal₁) h_body_b h_body_s
  | ite m c t e ih_c ih_t ih_e =>
    simp only [LExpr.substK] at h_subst ⊢
    let ⟨h_c_b, h_t_b, h_e_b⟩ := HasTypeA.ite_inv h_body
    let ⟨h_c_s, h_t_s, h_e_s⟩ := HasTypeA.ite_inv h_subst
    rw [denote_ite bvarVal₁ h_c_s h_t_s h_e_s h_subst,
        denote_ite _ h_c_b h_t_b h_e_b h_body,
        ih_c bvarVal₁ h_c_b h_c_s,
        ih_t bvarVal₁ h_t_b h_t_s,
        ih_e bvarVal₁ h_e_b h_e_s]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substK] at h_subst ⊢
    let ⟨ty_b, h_τ_b, h_1_b, h_2_b⟩ := HasTypeA.eq_inv h_body
    let ⟨ty_s, h_τ_s, h_1_s, h_2_s⟩ := HasTypeA.eq_inv h_subst
    subst h_τ_b
    have h_ty : ty_s = ty_b := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_1_s
      rw [substK_typeCheck h_v] at h1
      have h2 := LExpr.HasTypeA_to_typeCheck h_1_b
      rw [h1] at h2; cases h2; rfl
    subst h_ty
    by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal₁
        (LExpr.substK Δ₁.length s e1) ty_s h_1_s =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal₁
        (LExpr.substK Δ₁.length s e2) ty_s h_2_s
    · rw [denote_eq_true bvarVal₁ h_1_s h_2_s h_subst heq,
          denote_eq_true _ h_1_b h_2_b h_body
            (by rw [← ih1 bvarVal₁ h_1_b h_1_s, ← ih2 bvarVal₁ h_2_b h_2_s]; exact heq)]
    · rw [denote_eq_false bvarVal₁ h_1_s h_2_s h_subst heq,
          denote_eq_false _ h_1_b h_2_b h_body
            (by rw [← ih1 bvarVal₁ h_1_b h_1_s, ← ih2 bvarVal₁ h_2_b h_2_s]; exact heq)]
  | quant m qk name qty tr sub_body ih_tr ih_body =>
    cases qty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some qty' =>
      simp only [LExpr.substK] at h_subst ⊢
      let ⟨_, h_τ_b, h_tr_b, h_body_b⟩ := HasTypeA.quant_inv h_body
      let ⟨_, h_τ_s, h_tr_s, h_body_s⟩ := HasTypeA.quant_inv h_subst
      subst h_τ_b
      exact denote_quant_congr h_body_s h_body_b h_subst h_body fun x => by
        specialize ih_body (.cons x bvarVal₁) h_body_b h_body_s
        simp at ih_body
        exact ih_body

/-- Bound-variable substitution commutes with denotation. -/
theorem subst_denote
    {body : LExpr T.mono} {v : LExpr T.mono}
    {aty τ : LMonoTy}
    (h_body : LExpr.HasTypeA [aty] body τ)
    (h_v : LExpr.HasTypeA [] v aty)
    (h_subst : LExpr.HasTypeA [] (LExpr.subst (fun _ => v) body) τ)
    (h_lc : LExpr.lcAt 0 v = true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil
        (LExpr.subst (fun _ => v) body) τ h_subst =
      LExpr.denote tcInterp opInterp fvarVal vt
        (.cons (LExpr.denote tcInterp opInterp fvarVal vt .nil v aty h_v) .nil) body τ h_body := by
  exact substK_denote (Δ₁ := []) (s := fun _ => v)
    (val := LExpr.denote tcInterp opInterp fvarVal vt .nil v aty h_v)
    (bvarVal₁ := HList.nil) (h_body := h_body) (h_v := fun _ => h_v)
    (h_subst := h_subst) (h_lc := fun _ => h_lc) (h_denote_eq := fun _ => rfl)

/-- `varOpen` commutes with denotation: opening a bound variable with a free
variable `x` and then denoting under `fvarVal` is the same as denoting the
original body under `bvarVal` extended with `fvarVal x`. -/
theorem varOpen_denote
    {body : LExpr T.mono} {x : Identifier T.IDMeta}
    {aty τ : LMonoTy}
    (h_body : LExpr.HasTypeA [aty] body τ)
    (h_open : LExpr.HasTypeA [] (LExpr.varOpen 0 (x, some aty) body) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil
        (LExpr.varOpen 0 (x, some aty) body) τ h_open =
      LExpr.denote tcInterp opInterp fvarVal vt
        (.cons (fvarVal x (LMonoTy.substTyVars vt aty)) .nil) body τ h_body := by
  unfold LExpr.varOpen
  exact substK_denote (Δ₁ := []) (s := fun m => .fvar m x (some aty))
    (val := fvarVal x (LMonoTy.substTyVars vt aty))
    (bvarVal₁ := HList.nil) (h_body := h_body)
    (h_v := fun m => LExpr.typeCheck_to_HasTypeA (by simp [LExpr.typeCheck]))
    (h_subst := h_open)
    (h_lc := fun _ => by simp [LExpr.lcAt])
    (h_denote_eq := fun m => by simp [LExpr.denote])

/-! ### liftBVars and denotation -/

/-- `liftBVars` preserves `typeCheck`: lifting bvar indices past an inserted
block doesn't change the type. -/
theorem liftBVars_typeCheck
    (e : LExpr T.mono)
    {Δ₁ Δ_insert Δ_outer : List LMonoTy}
    : LExpr.typeCheck (Δ₁ ++ Δ_insert ++ Δ_outer) (LExpr.liftBVars Δ_insert.length e Δ₁.length)
      = LExpr.typeCheck (Δ₁ ++ Δ_outer) e := by
  induction e generalizing Δ₁ with
  | const => simp [LExpr.liftBVars, LExpr.typeCheck]
  | op m o ty => cases ty <;> simp [LExpr.liftBVars, LExpr.typeCheck]
  | fvar m name ty => cases ty <;> simp [LExpr.liftBVars, LExpr.typeCheck]
  | bvar m i =>
    simp only [LExpr.liftBVars, LExpr.typeCheck]
    split
    · -- i ≥ Δ₁.length: shifted to i + Δ_insert.length
      rename_i h_ge
      simp only [LExpr.typeCheck]
      grind
    · -- i < Δ₁.length: not shifted
      rename_i h_lt
      simp only [LExpr.typeCheck]
      grind
  | abs m name ty body ih =>
    simp [LExpr.liftBVars]
    cases ty with
    | none => rfl
    | some aty =>
      simp[LExpr.typeCheck]
      specialize ih (Δ₁ := aty :: Δ₁)
      grind
  | quant m qk name ty tr body ih_tr ih_body =>
    simp [LExpr.liftBVars]
    cases ty with
    | none => rfl
    | some qty =>
      simp[LExpr.typeCheck]
      specialize ih_tr (Δ₁ := qty :: Δ₁)
      specialize ih_body (Δ₁ := qty :: Δ₁)
      grind
  | app m fn arg ih_fn ih_arg =>
    simp [LExpr.liftBVars, LExpr.typeCheck]
    grind
  | ite m c t e ih_c ih_t ih_e =>
    simp [LExpr.liftBVars, LExpr.typeCheck]
    grind
  | eq m e1 e2 ih1 ih2 =>
    simp [LExpr.liftBVars, LExpr.typeCheck]
    grind

/-- If `liftBVars` is well-typed in the extended context, then the original
expression is well-typed in the outer context. -/
theorem liftBVars_hasTypeA_inv
    {e : LExpr T.mono} {τ : LMonoTy}
    {Δ_body Δ_outer : List LMonoTy}
    (h : LExpr.HasTypeA (Δ_body ++ Δ_outer) (LExpr.liftBVars Δ_body.length e) τ)
    : LExpr.HasTypeA Δ_outer e τ := by
  rw [LExpr.HasTypeA_iff_typeCheck] at h ⊢
  have hty := liftBVars_typeCheck (Δ₁ := []) (Δ_insert := Δ_body) (Δ_outer := Δ_outer) (e := e)
  simp at hty
  rw [hty] at h
  exact h

/-- Lifting bound variable indices preserves denotation: inserting a block
`Δ_insert` into the middle of the bvar context (between `Δ₁` and `Δ_outer`)
and shifting bvar indices accordingly doesn't change the denotation. -/
theorem liftBVars_denote
    {e : LExpr T.mono} {τ : LMonoTy}
    {Δ₁ Δ_insert Δ_outer : List LMonoTy}
    (h_orig : LExpr.HasTypeA (Δ₁ ++ Δ_outer) e τ)
    (h_lifted : LExpr.HasTypeA (Δ₁ ++ (Δ_insert ++ Δ_outer)) (LExpr.liftBVars Δ_insert.length e Δ₁.length) τ)
    (bv₁ : BVarVal tcInterp vt Δ₁)
    (bv_insert : BVarVal tcInterp vt Δ_insert)
    (bv_outer : BVarVal tcInterp vt Δ_outer)
    : LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ (HList.append bv_insert bv_outer))
        (LExpr.liftBVars Δ_insert.length e Δ₁.length) τ h_lifted =
      LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv_outer) e τ h_orig := by
  induction e generalizing Δ₁ bv₁ τ with
  | const m c =>
    simp only [LExpr.liftBVars] at h_lifted ⊢
    rfl
  | op m o ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_orig) (by simp [LExpr.typeCheck])
    | some ty =>
      simp only [LExpr.liftBVars] at h_lifted ⊢
      have h1 := HasTypeA.op_inv h_lifted; have h2 := HasTypeA.op_inv h_orig
      subst h1; rfl
  | fvar m name ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_orig) (by simp [LExpr.typeCheck])
    | some ty =>
      simp only [LExpr.liftBVars] at h_lifted ⊢
      have h1 := HasTypeA.fvar_inv h_lifted; have h2 := HasTypeA.fvar_inv h_orig
      subst h1; rfl
  | bvar m i =>
    simp only [LExpr.liftBVars] at h_lifted ⊢
    by_cases h_ge : i ≥ Δ₁.length
    · -- i ≥ |Δ₁|: shifted to i + |Δ_insert|
      simp [h_ge] at h_lifted ⊢
      rw [denote_bvar _ _ _ _ _ h_lifted, denote_bvar _ _ _ _ _ h_orig]
      rw [HList.get_append_right bv₁ (bv_insert.append bv_outer) (i + Δ_insert.length)
            (HasTypeA.bvar_inv h_lifted)
            (by have := HasTypeA.bvar_inv h_orig; grind)
            (by simp; omega)]
      rw [HList.get_append_right bv_insert bv_outer (i + Δ_insert.length - Δ₁.length)
            (by have := HasTypeA.bvar_inv h_orig; grind)
            (by have := HasTypeA.bvar_inv h_orig; grind)]
      rw [HList.get_append_right bv₁ bv_outer i (HasTypeA.bvar_inv h_orig)
            (by have := HasTypeA.bvar_inv h_orig; grind)
            (by omega)]
      congr 1; omega
      grind
    · -- i < |Δ₁|: not shifted
      simp [h_ge] at h_lifted ⊢
      rw [denote_bvar _ _ _ _ _ h_lifted, denote_bvar _ _ _ _ _ h_orig]
      have h_bv := HasTypeA.bvar_inv h_orig
      rw [HList.get_append_left bv₁ (bv_insert.append bv_outer) i
            (HasTypeA.bvar_inv h_lifted)
            (by grind)]
      rw [HList.get_append_left bv₁ bv_outer i (HasTypeA.bvar_inv h_orig)
            (by grind)]
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.liftBVars] at h_lifted ⊢
    let ⟨aty_l, h_fn_l, h_arg_l⟩ := HasTypeA.app_inv h_lifted
    let ⟨aty_o, h_fn_o, h_arg_o⟩ := HasTypeA.app_inv h_orig
    have h_aty : aty_l = aty_o := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_fn_l
      rw [←List.append_assoc] at h1
      rw [liftBVars_typeCheck] at h1
      have h2 := LExpr.HasTypeA_to_typeCheck h_fn_o
      rw [h1] at h2; cases h2; rfl
    subst h_aty
    rw [denote_app _ h_fn_l h_arg_l h_lifted, denote_app _ h_fn_o h_arg_o h_orig,
        ih_fn h_fn_o h_fn_l bv₁, ih_arg h_arg_o h_arg_l bv₁]
  | abs m name ty body ih =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_orig) (by simp [LExpr.typeCheck])
    | some aty =>
      simp only [LExpr.liftBVars] at h_lifted ⊢
      let ⟨rty_l, h_eq_l, h_body_l⟩ := HasTypeA.abs_inv h_lifted
      let ⟨rty_o, h_eq_o, h_body_o⟩ := HasTypeA.abs_inv h_orig
      subst h_eq_l
      cases h_eq_o
      rw [denote_abs _ h_body_l h_lifted, denote_abs _ h_body_o h_orig]
      funext x
      exact ih h_body_o h_body_l (.cons x bv₁)
  | ite m c t e ih_c ih_t ih_e =>
    simp only [LExpr.liftBVars] at h_lifted ⊢
    let ⟨h_c_l, h_t_l, h_e_l⟩ := HasTypeA.ite_inv h_lifted
    let ⟨h_c_o, h_t_o, h_e_o⟩ := HasTypeA.ite_inv h_orig
    rw [denote_ite _ h_c_l h_t_l h_e_l h_lifted,
        denote_ite _ h_c_o h_t_o h_e_o h_orig,
        ih_c h_c_o h_c_l bv₁, ih_t h_t_o h_t_l bv₁, ih_e h_e_o h_e_l bv₁]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.liftBVars] at h_lifted ⊢
    let ⟨ty_l, h_τ_l, h_1_l, h_2_l⟩ := HasTypeA.eq_inv h_lifted
    let ⟨ty_o, h_τ_o, h_1_o, h_2_o⟩ := HasTypeA.eq_inv h_orig
    subst h_τ_o
    have h_ty : ty_l = ty_o := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_1_l
      rw [show Δ₁ ++ (Δ_insert ++ Δ_outer) = Δ₁ ++ Δ_insert ++ Δ_outer from (List.append_assoc ..).symm] at h1
      rw [liftBVars_typeCheck] at h1
      have h2 := LExpr.HasTypeA_to_typeCheck h_1_o
      rw [h1] at h2; cases h2; rfl
    subst h_ty
    by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bv₁ (HList.append bv_insert bv_outer))
        (LExpr.liftBVars Δ_insert.length e1 Δ₁.length) ty_l h_1_l =
      LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bv₁ (HList.append bv_insert bv_outer))
        (LExpr.liftBVars Δ_insert.length e2 Δ₁.length) ty_l h_2_l
    · rw [denote_eq_true _ h_1_l h_2_l h_lifted heq,
          denote_eq_true _ h_1_o h_2_o h_orig
            (by rw [← ih1 h_1_o h_1_l bv₁, ← ih2 h_2_o h_2_l bv₁]; exact heq)]
    · rw [denote_eq_false _ h_1_l h_2_l h_lifted heq,
          denote_eq_false _ h_1_o h_2_o h_orig
            (by rw [← ih1 h_1_o h_1_l bv₁, ← ih2 h_2_o h_2_l bv₁]; exact heq)]
  | quant m qk name qty tr body ih_tr ih_body =>
    cases qty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_orig) (by simp [LExpr.typeCheck])
    | some qty' =>
      simp only [LExpr.liftBVars] at h_lifted ⊢
      let ⟨_, h_τ_l, h_tr_l, h_body_l⟩ := HasTypeA.quant_inv h_lifted
      let ⟨_, h_τ_o, h_tr_o, h_body_o⟩ := HasTypeA.quant_inv h_orig
      subst h_τ_o
      have h_ih_body : ∀ x : TyDenote tcInterp vt qty',
          LExpr.denote tcInterp opInterp fvarVal vt
            (.cons x (HList.append bv₁ (HList.append bv_insert bv_outer)))
            (LExpr.liftBVars Δ_insert.length body (Δ₁.length + 1)) .bool h_body_l =
          LExpr.denote tcInterp opInterp fvarVal vt
            (.cons x (HList.append bv₁ bv_outer)) body .bool h_body_o := by
        intro x
        exact ih_body h_body_o h_body_l (.cons x bv₁)
      exact denote_quant_congr h_body_l h_body_o h_lifted h_orig h_ih_body

/-! ### denoteArgs indexing -/

/-- The i-th element of `denoteArgs` is the denotation of the i-th expression. -/
theorem denoteArgs_get
    {exprs : List (LExpr T.mono)} {tys : List LMonoTy} {e : LExpr T.mono} {ty : LMonoTy}
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ) exprs tys)
    (i : Nat)
    (h_e : exprs[i]? = some e) (h_ty : tys[i]? = some ty)
    (h_sort : (tys.map (LMonoTy.substTyVars vt))[i]? = some (LMonoTy.substTyVars vt ty))
    : (denoteArgs (tcInterp := tcInterp) (opInterp := opInterp) fvarVal vt bvarVal exprs tys h_wt).get i h_sort
      = LExpr.denote tcInterp opInterp fvarVal vt bvarVal e ty (List.Forall₂.get? h_wt i h_e h_ty) := by
  induction h_wt generalizing i with
  | nil => simp at h_e
  | cons h_head h_tail ih =>
    cases i with
    | zero =>
      simp at h_e h_ty; cases h_e; cases h_ty
      simp [denoteArgs]
    | succ n =>
      simp at h_e h_ty
      simp only [denoteArgs]
      exact ih n h_e h_ty (by simpa using h_sort)

/-! ### withArgs lemmas -/

/-- If `name` is not in the keys of `sortBindings`, then `withArgs` falls
through to the original `fvarVal`. -/
theorem IdentInterp.withArgs_not_mem [DecidableEq T.IDMeta]
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_not_mem : name ∉ sortBindings.map Prod.fst)
    : (fvarVal.withArgs sortBindings h_args) name s = fvarVal name s := by
  fun_induction IdentInterp.withArgs <;> simp_all

/-- If `name` is the i-th key of `sortBindings` (first occurrence), then
`withArgs` returns the i-th element of `vals`. -/
theorem IdentInterp.withArgs_get [DecidableEq T.IDMeta]
    (fvarVal : IdentInterp T tcInterp)
    (sortBindings : List (Identifier T.IDMeta × LSort))
    (vals : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (name : Identifier T.IDMeta) (s : LSort)
    (i : Nat)
    (h_key : (sortBindings.map Prod.fst)[i]? = some name)
    (h_sort : (sortBindings.map Prod.snd)[i]? = some s)
    (h_first : ∀ j < i, (sortBindings.map Prod.fst)[j]? ≠ some name)
    : (fvarVal.withArgs sortBindings vals) name s = vals.get i h_sort := by
  fun_induction IdentInterp.withArgs generalizing i with
  | case1 =>
    -- sortBindings = [], vals = .nil
    simp at h_key
  | case2 rest vs v =>
    have : i = 0 := by
      cases i with
      | zero => rfl
      | succ i' =>
        specialize h_first 0 (by omega)
        simp_all
    subst_vars
    rfl
  | case3 =>
    have: i ≠ 0 := by
      intros heq; subst_vars; simp at h_sort; subst_vars; contradiction
    cases i <;> try contradiction
    rename_i IH i'
    simp
    apply IH <;> simp_all
    intros j hj x
    specialize h_first (j + 1) (by omega)
    simp_all
  | case4 =>
    have: i ≠ 0 := by
      intros heq; subst_vars; simp at h_key; subst_vars; contradiction
    cases i <;> try contradiction
    rename_i IH i'
    simp
    apply IH <;> simp_all
    intros j hj x
    specialize h_first (j + 1) (by omega)
    simp_all

/-- `go` preserves `typeCheck` when fvar annotations match binding types. -/
private theorem go_typeCheck [DecidableEq T.IDMeta]
    {bindings : List (T.Identifier × LExpr T.mono)}
    {Δ_outer : List LMonoTy}
    {tys : List LMonoTy}
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) tys)
    {e : LExpr T.mono} {Δ_body : List LMonoTy}
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip tys) e)
    : LExpr.typeCheck (Δ_body ++ Δ_outer) (LExpr.substFvarsLifting.go bindings e Δ_body.length)
      = LExpr.typeCheck (Δ_body ++ Δ_outer) e := by
  induction e generalizing Δ_body with
  | const => simp [LExpr.substFvarsLifting.go, LExpr.typeCheck]
  | op => simp [LExpr.substFvarsLifting.go]
  | bvar => simp [LExpr.substFvarsLifting.go, LExpr.typeCheck]
  | fvar m name ty =>
    simp only [LExpr.substFvarsLifting.go]
    cases ty with
    | none =>
      simp[Lambda.fvars_annotated_by] at h_annot
    | some ty =>
      cases hfind : Map.find? bindings name with
      | none => rfl
      | some e' =>
        simp only [LExpr.typeCheck]
        have h := liftBVars_typeCheck e' (Δ₁ := []) (Δ_insert := Δ_body) (Δ_outer := Δ_outer)
        simp at h
        rw[h]
        -- Need: typeCheck Δ_outer e' = some ty
        -- From find?_zip: get ty' with find? tyMap name = some ty' and index i
        -- From h_annot: ty = ty'
        -- From Forall₂.get?: HasTypeA Δ_outer e' ty'
        have hlen : tys.length = bindings.length := by
          have h := h_wt.length_eq.symm
          grind
        obtain ⟨ty', i, hfind_zip, hsnd, htys⟩ := Map.find?_zip hfind hlen
        have hty_eq := h_annot ty' hfind_zip
        subst hty_eq
        exact (LExpr.HasTypeA_iff_typeCheck _ _ _).mp (h_wt.get? i hsnd htys)
  | app m fn arg ih_fn ih_arg =>
    simp [LExpr.substFvarsLifting.go, LExpr.typeCheck]
    rw [ih_fn h_annot.1, ih_arg h_annot.2]
  | abs m name ty body ih =>
    simp [LExpr.substFvarsLifting.go]
    cases ty with
    | none => rfl
    | some aty =>
      simp [LExpr.typeCheck]
      have h_len : (aty :: Δ_body).length = Δ_body.length + 1 := by simp
      rw [← h_len]
      have h_cons : aty :: (Δ_body ++ Δ_outer) = (aty :: Δ_body) ++ Δ_outer := by simp
      rw [h_cons]
      rw [ih (Δ_body := aty :: Δ_body) h_annot]
  | ite m c t e ih_c ih_t ih_e =>
    simp [LExpr.substFvarsLifting.go, LExpr.typeCheck]
    rw [ih_c h_annot.1, ih_t h_annot.2.1, ih_e h_annot.2.2]
  | eq m e1 e2 ih1 ih2 =>
    simp [LExpr.substFvarsLifting.go, LExpr.typeCheck]
    rw [ih1 h_annot.1, ih2 h_annot.2]
  | quant m qk name ty tr body ih_tr ih_body =>
    simp [LExpr.substFvarsLifting.go]
    cases ty with
    | none => rfl
    | some qty =>
      simp [LExpr.typeCheck]
      have h_len : (qty :: Δ_body).length = Δ_body.length + 1 := by simp
      rw [← h_len]
      have h_cons : qty :: (Δ_body ++ Δ_outer) = (qty :: Δ_body) ++ Δ_outer := by simp
      rw [h_cons]
      rw [ih_tr (Δ_body := qty :: Δ_body) h_annot.1,
          ih_body (Δ_body := qty :: Δ_body) h_annot.2]

/-- `substFvarsLifting` preserves `typeCheck` when fvar annotations match binding types. -/
theorem substFvarsLifting_typeCheck [DecidableEq T.IDMeta]
    {bindings : List (T.Identifier × LExpr T.mono)}
    {Δ : List LMonoTy}
    {tys : List LMonoTy}
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ) (bindings.map Prod.snd) tys)
    {e : LExpr T.mono} {τ : LMonoTy}
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip tys) e)
    (h : LExpr.HasTypeA Δ e τ)
    : LExpr.HasTypeA Δ (LExpr.substFvarsLifting e bindings) τ := by
  simp only [LExpr.substFvarsLifting]
  split
  · exact h
  · rw [LExpr.HasTypeA_iff_typeCheck] at h ⊢
    have h_tc := go_typeCheck (Δ_body := []) h_wt h_annot
    simp at h_tc
    rw [h_tc, h]

/-! ### Free-variable substitution commutes with denotation -/

/-- Inner lemma: `go` at depth `|Δ_body|` commutes with denotation. -/
private theorem substFvarsLifting_go_denote [DecidableEq T.IDMeta]
    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    {Δ_outer : List LMonoTy}
    (bvarVal_outer : BVarVal tcInterp vt Δ_outer)
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)
    {tys : List LMonoTy}
    (h_tys_len : tys.length = bindings.length)
    (h_sorts : sortBindings.map Prod.snd = tys.map (LMonoTy.substTyVars vt))
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) tys)
    (h_denotes : h_args = HList.cast h_sorts.symm
        (denoteArgs tcInterp opInterp fvarVal vt bvarVal_outer (bindings.map Prod.snd) tys h_wt))
    {body : LExpr T.mono} {τ : LMonoTy}
    {Δ_body : List LMonoTy}
    (bvarVal_body : BVarVal tcInterp vt Δ_body)
    (h_body : LExpr.HasTypeA (Δ_body ++ Δ_outer) body τ)
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip tys) body)
    (h_subst : LExpr.HasTypeA (Δ_body ++ Δ_outer)
        (LExpr.substFvarsLifting.go bindings body Δ_body.length) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal_body bvarVal_outer)
        (LExpr.substFvarsLifting.go bindings body Δ_body.length) τ h_subst =
      LExpr.denote tcInterp opInterp
        (fvarVal.withArgs sortBindings h_args)
        vt (HList.append bvarVal_body bvarVal_outer) body τ h_body := by
  induction body generalizing Δ_body τ with
  | const m c =>
    simp [LExpr.substFvarsLifting.go, LExpr.denote] at h_subst ⊢
  | op m o ty =>
    simp [LExpr.substFvarsLifting.go] at h_subst ⊢
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some ty => rfl
  | bvar m i =>
    simp [LExpr.substFvarsLifting.go] at h_subst ⊢
    rw [denote_bvar _ _ _ _ _ h_subst, denote_bvar _ _ _ _ _ h_body]
  | fvar m name ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some ty =>
      simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
      -- Lean does not let us generalize directly, use tactic
      generalize_lhs_last_arg
      rename_i heq;
      revert heq
      clear h_subst
      cases hfind : Map.find? bindings name with
      | some e =>
        rename_i hfind
        simp
        intro heq
        -- LHS: liftBVars_denote with Δ₁=[], Δ_insert=Δ_body
        -- Need h_orig : HasTypeA Δ_outer e τ from h_wt and hfind
        have h_orig : LExpr.HasTypeA Δ_outer e τ := by
          exact liftBVars_hasTypeA_inv heq
        have h_lift := liftBVars_denote (tcInterp := tcInterp) (opInterp := opInterp)
          (fvarVal := fvarVal) (vt := vt) (Δ₁ := []) h_orig heq .nil bvarVal_body bvarVal_outer
        simp [HList.append] at h_lift
        rw [h_lift]
        -- RHS: denote_fvar then withArgs_mem
        rw [denote_fvar _ _ _ _ _ h_body]
        -- Goal: denote ... e τ h_orig = fvar_inv ▸ withArgs ... name (ty.substTyVars vt)
        -- Step 1: subst τ = ty from fvar_inv
        have h_ty_eq := HasTypeA.fvar_inv h_body
        subst h_ty_eq
        simp
        -- Goal: denote ... e τ h_orig = withArgs ... name (τ.substTyVars vt)
        -- Get index from Map.find?_index
        obtain ⟨i, h_key_b, h_val_b, h_first_bindings⟩ := Map.find?_index hfind
        have h_key : (sortBindings.map Prod.fst)[i]? = some name := by
          rw [← h_keys]; exact h_key_b
        have h_sort : (sortBindings.map Prod.snd)[i]? = some (LMonoTy.substTyVars vt τ) := by
          have h_i_lt : i < tys.length := by
            rw [h_tys_len]
            have ⟨h_bound, _⟩ := List.getElem?_eq_some_iff.mp h_val_b
            simp at h_bound ⊢; exact h_bound
          have h_tys_eq : tys[i]? = some tys[i] :=
            List.getElem?_eq_some_iff.mpr ⟨h_i_lt, rfl⟩
          have h_wt_i := List.Forall₂.get? h_wt i h_val_b h_tys_eq
          have h_eq := HasTypeA_unique h_wt_i h_orig
          rw [h_sorts, List.getElem?_map, h_tys_eq, h_eq]; simp
        have h_first : ∀ j < i, (sortBindings.map Prod.fst)[j]? ≠ some name := by
          intro j hj; rw [← h_keys]; exact h_first_bindings j hj
        rw [IdentInterp.withArgs_get (tcInterp := tcInterp) fvarVal sortBindings h_args name _ i h_key h_sort h_first]
        rw [h_denotes, HList.get_cast]
        · have h_tys_eq : tys[i]? = some τ := by
            have h_i_lt : i < tys.length := by
              rw [h_tys_len]
              have ⟨h_bound, _⟩ := List.getElem?_eq_some_iff.mp h_val_b
              simp at h_bound ⊢; exact h_bound
            have h_tys_i := List.getElem?_eq_some_iff.mpr ⟨h_i_lt, rfl⟩
            have h_wt_i := List.Forall₂.get? h_wt i h_val_b h_tys_i
            rw [HasTypeA_unique h_wt_i h_orig] at h_tys_i
            exact h_tys_i
          rw [denoteArgs_get _ _ _ _ h_wt i h_val_b h_tys_eq]
        · rw [← h_sorts]; exact h_sort
      | none =>
        -- find? name = none
        rename_i hfind
        simp
        intros h_subst
        rw [denote_fvar _ _ _ _ _ h_subst, denote_fvar _ _ _ _ _ h_body]
        congr 1
        have h_not_mem : name ∉ (bindings.map Prod.fst) := by
          have hkey := Map.find?_of_not_mem_values _ hfind
          rw[Map.keys_eq_map_fst] at hkey
          exact hkey
        rw [h_keys] at h_not_mem
        exact (IdentInterp.withArgs_not_mem _ fvarVal h_args h_not_mem).symm
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
    let ⟨aty_s, h_fn_s, h_arg_s⟩ := HasTypeA.app_inv h_subst
    let ⟨aty_b, h_fn_b, h_arg_b⟩ := HasTypeA.app_inv h_body
    have h_aty : aty_s = aty_b := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_fn_s
      have h_annot_fn := h_annot.1
      rw [go_typeCheck h_wt h_annot_fn] at h1
      have h2 := LExpr.HasTypeA_to_typeCheck h_fn_b
      rw [h1] at h2; cases h2; rfl
    subst h_aty
    rw [denote_app _ h_fn_s h_arg_s h_subst, denote_app _ h_fn_b h_arg_b h_body]
    rw [ih_fn bvarVal_body h_fn_b h_annot.1 h_fn_s, ih_arg bvarVal_body h_arg_b h_annot.2 h_arg_s]
  | abs m name ty body' ih =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some aty =>
      simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
      let ⟨rty_b, h_eq_b, h_body_b⟩ := HasTypeA.abs_inv h_body
      let ⟨rty_s, h_eq_s, h_body_s⟩ := HasTypeA.abs_inv h_subst
      subst h_eq_b; cases h_eq_s
      rw [denote_abs _ h_body_s h_subst, denote_abs _ h_body_b h_body]
      funext x
      exact ih (.cons x bvarVal_body) h_body_b h_annot h_body_s
  | ite m c t e ih_c ih_t ih_e =>
    simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
    let ⟨h_c_b, h_t_b, h_e_b⟩ := HasTypeA.ite_inv h_body
    let ⟨h_c_s, h_t_s, h_e_s⟩ := HasTypeA.ite_inv h_subst
    rw [denote_ite _ h_c_s h_t_s h_e_s h_subst,
        denote_ite _ h_c_b h_t_b h_e_b h_body,
        ih_c bvarVal_body h_c_b h_annot.1 h_c_s,
        ih_t bvarVal_body h_t_b h_annot.2.1 h_t_s,
        ih_e bvarVal_body h_e_b h_annot.2.2 h_e_s]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
    let ⟨ty_b, h_τ_b, h_1_b, h_2_b⟩ := HasTypeA.eq_inv h_body
    let ⟨ty_s, h_τ_s, h_1_s, h_2_s⟩ := HasTypeA.eq_inv h_subst
    subst h_τ_b
    have h_ty : ty_s = ty_b := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_1_s
      rw [go_typeCheck h_wt h_annot.1] at h1
      have h2 := LExpr.HasTypeA_to_typeCheck h_1_b
      rw [h1] at h2; cases h2; rfl
    subst h_ty
    by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal_body bvarVal_outer)
        (LExpr.substFvarsLifting.go bindings e1 Δ_body.length) ty_s h_1_s =
      LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal_body bvarVal_outer)
        (LExpr.substFvarsLifting.go bindings e2 Δ_body.length) ty_s h_2_s
    · rw [denote_eq_true _ h_1_s h_2_s h_subst heq,
          denote_eq_true _ h_1_b h_2_b h_body
            (by rw [← ih1 bvarVal_body h_1_b h_annot.1 h_1_s,
                     ← ih2 bvarVal_body h_2_b h_annot.2 h_2_s]; exact heq)]
    · rw [denote_eq_false _ h_1_s h_2_s h_subst heq,
          denote_eq_false _ h_1_b h_2_b h_body
            (by rw [← ih1 bvarVal_body h_1_b h_annot.1 h_1_s,
                     ← ih2 bvarVal_body h_2_b h_annot.2 h_2_s]; exact heq)]
  | quant m qk name qty tr sub_body ih_tr ih_body =>
    cases qty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some qty' =>
      simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
      let ⟨_, h_τ_b, h_tr_b, h_body_b⟩ := HasTypeA.quant_inv h_body
      let ⟨_, h_τ_s, h_tr_s, h_body_s⟩ := HasTypeA.quant_inv h_subst
      subst h_τ_b
      have h_ih_body : ∀ x : TyDenote tcInterp vt qty',
          LExpr.denote tcInterp opInterp fvarVal vt
            (.cons x (HList.append bvarVal_body bvarVal_outer))
            (LExpr.substFvarsLifting.go bindings sub_body (Δ_body.length + 1)) .bool h_body_s =
          LExpr.denote tcInterp opInterp (fvarVal.withArgs sortBindings h_args) vt
            (.cons x (HList.append bvarVal_body bvarVal_outer)) sub_body .bool h_body_b := by
        intro x
        have h_ih := ih_body (.cons x bvarVal_body) h_body_b h_annot.2 h_body_s
        rw [show (HList.cons x bvarVal_body).append bvarVal_outer =
            HList.cons x (HList.append bvarVal_body bvarVal_outer) from rfl] at h_ih
        exact h_ih
      exact denote_quant_congr h_body_s h_body_b h_subst h_body h_ih_body

/-- Free-variable substitution commutes with denotation (generalized to
arbitrary bound-variable context for replacements). -/
theorem substFvarsLifting_denote [DecidableEq T.IDMeta]
    {body : LExpr T.mono} {τ : LMonoTy}
    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    {Δ_outer : List LMonoTy}
    (bvarVal_outer : BVarVal tcInterp vt Δ_outer)
    (h_body : LExpr.HasTypeA Δ_outer body τ)
    (h_subst : LExpr.HasTypeA Δ_outer (LExpr.substFvarsLifting body bindings) τ)
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)
    (h_len : bindings.length = sortBindings.length)
    {tys : List LMonoTy}
    (h_tys_len : tys.length = bindings.length)
    (h_sorts : sortBindings.map Prod.snd = tys.map (LMonoTy.substTyVars vt))
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) tys)
    (h_denotes : h_args = HList.cast h_sorts.symm
        (denoteArgs tcInterp opInterp fvarVal vt bvarVal_outer (bindings.map Prod.snd) tys h_wt))
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip tys) body)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal_outer
        (LExpr.substFvarsLifting body bindings) τ h_subst =
      LExpr.denote tcInterp opInterp
        (fvarVal.withArgs sortBindings h_args)
        vt bvarVal_outer body τ h_body := by
  unfold LExpr.substFvarsLifting at h_subst ⊢
  split
  · -- bindings.isEmpty = true → bindings = [], sortBindings = []
    rename_i h_empty
    have h_bindings_nil : bindings = [] := by
      cases bindings with
      | nil => rfl
      | cons => simp [Map.isEmpty] at h_empty
    have h_sort_nil : sortBindings = [] := by
      have : sortBindings.length = 0 := by rw [← h_len, h_bindings_nil]; simp
      exact List.eq_nil_of_length_eq_zero this
    subst h_bindings_nil h_sort_nil
    cases h_args
    exact denote_ext tcInterp vt
      (by intros; rfl) (by intro n ty _; rfl) (by intros; rfl)
      _ h_body
  · -- bindings.isEmpty = false → apply go_denote with Δ_body = [], bvarVal_body = .nil
    rename_i h_not_empty
    simp [h_not_empty] at h_subst
    have h_go := substFvarsLifting_go_denote (tcInterp := tcInterp) (opInterp := opInterp)
      (fvarVal := fvarVal) (vt := vt)
      bvarVal_outer h_args h_keys h_tys_len h_sorts h_wt h_denotes
      (Δ_body := []) .nil h_body h_annot (by simp [h_subst])
    simpa using h_go

/-! ## `substFvars` denotation (via locally closed replacements) -/

/-- Free-variable substitution commutes with denotation: for locally closed
replacement terms, substituting free variables and then evaluating equals
evaluating the original body under an extended free-variable valuation. -/
theorem substFvars_denote [DecidableEq T.IDMeta]
    {body : LExpr T.mono} {τ : LMonoTy}
    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    {Δ_outer : List LMonoTy}
    (bvarVal_outer : BVarVal tcInterp vt Δ_outer)
    (h_body : LExpr.HasTypeA Δ_outer body τ)
    (h_subst : LExpr.HasTypeA Δ_outer (LExpr.substFvars body bindings) τ)
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)
    (h_len : bindings.length = sortBindings.length)
    {tys : List LMonoTy}
    (h_tys_len : tys.length = bindings.length)
    (h_sorts : sortBindings.map Prod.snd = tys.map (LMonoTy.substTyVars vt))
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) tys)
    (h_denotes : h_args = HList.cast h_sorts.symm
        (denoteArgs tcInterp opInterp fvarVal vt bvarVal_outer (bindings.map Prod.snd) tys h_wt))
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip tys) body)
    (h_lc : ∀ (k : T.Identifier) (v : LExpr T.mono), Map.find? bindings k = some v → LExpr.lcAt 0 v = true)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal_outer
        (LExpr.substFvars body bindings) τ h_subst =
      LExpr.denote tcInterp opInterp
        (fvarVal.withArgs sortBindings h_args)
        vt bvarVal_outer body τ h_body := by
  have h_eq : body.substFvars bindings = body.substFvarsLifting bindings :=
    LExpr.substFvars_eq_substFvarsLifting_of_lcAt h_lc
  revert h_eq
  generalize body.substFvars bindings = e' at h_subst ⊢
  intros h_eq
  subst h_eq
  exact substFvarsLifting_denote _ _ _ _ bvarVal_outer h_body h_subst h_args h_keys h_len
    h_tys_len h_sorts h_wt h_denotes h_annot
