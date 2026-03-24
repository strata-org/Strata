/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Denote.HList
import all Strata.DL.Lambda.Denote.LExprDenoteProps

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp T tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### Generalized substK_denote -/

/-
Informal proof of substK_denote:

By induction on body, generalizing Δ₁, τ, bv₁.

case const/op/fvar:
  substK doesn't change these. Both sides denote to the same constant/op/fvar
  value regardless of bvarVal. Use Denotes + Denotes_denote.

case bvar m i:
  substK |Δ₁| s (bvar i) = if i == |Δ₁| then s m else bvar i.

  - i < |Δ₁|: Both sides look up bv₁[i]. LHS via h_subst, RHS via
    HList.get_append_left since i < |Δ₁|.
  - i = |Δ₁|: LHS = denote bv₁ v. RHS = (bv₁ ++ [val])[|Δ₁|] = val = denote .nil v.
    Equal by denote_irrel_of_lcAt.
  - i > |Δ₁|: Vacuous — (Δ₁ ++ [aty])[i]? = none since i ≥ |Δ₁| + 1.

case app m fn arg:
  Decompose with app_inv, apply denote_app on both sides, use IH on fn and arg.

case abs m name (some bty) sub_body:
  Decompose with abs_inv on both sides.
  Apply denote_abs on both sides.
  LHS = fun x => denote (cons x bv₁) (substK (|Δ₁|+1) s sub_body)
  RHS = fun x => denote (cons x (bv₁ ++ [val])) sub_body
  Apply IH with Δ₁' = bty :: Δ₁, noting (bty :: Δ₁) ++ [aty] = bty :: (Δ₁ ++ [aty]).

case ite/eq/quant: Similar decomposition with unfolding lemmas + IH.
-/

/-- Generalized substitution lemma: `substK k` at depth `k` in a context
    `Δ₁ ++ [aty]` with `|Δ₁| = k`. The substituted value `v` must be locally
    closed and well-typed in the empty context. -/
theorem substK_denote
    {body : LExpr T.mono} {v : LExpr T.mono}
    {aty τ : LMonoTy}
    {Δ₁ : List LMonoTy}
    (bvarVal₁ : BVarVal tcInterp vt Δ₁)
    (h_body : LExpr.HasTypeA (Δ₁ ++ [aty]) body τ)
    (h_v : LExpr.HasTypeA [] v aty)
    (h_subst : LExpr.HasTypeA Δ₁ (LExpr.substK Δ₁.length (fun _ => v) body) τ)
    (h_lc : LExpr.lcAt 0 v = true)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal₁
        (LExpr.substK Δ₁.length (fun _ => v) body) τ h_subst =
      LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal₁ (.cons (LExpr.denote tcInterp opInterp fvarVal vt .nil v aty h_v) .nil))
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
      rw [denote_irrel_of_lcAt tcInterp opInterp fvarVal vt h_lc h_subst h_v bvarVal₁ .nil]
      rw [denote_bvar tcInterp opInterp fvarVal vt _ h_body]
      exact (HList.get_append_cons_self bvarVal₁
        (LExpr.denote tcInterp opInterp fvarVal vt .nil v aty h_v) .nil
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
        (LExpr.substK Δ₁.length (fun _ => v) e1) ty_s h_1_s =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal₁
        (LExpr.substK Δ₁.length (fun _ => v) e2) ty_s h_2_s
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
      cases qk with
      | all =>
        by_cases hall : ∀ x : TyDenote tcInterp vt qty',
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal₁)
              (LExpr.substK (Δ₁.length + 1) (fun _ => v) sub_body) .bool h_body_s : Bool) = true
        · rw [denote_quant_all_true bvarVal₁ h_body_s h_subst hall]
          symm
          apply denote_quant_all_true
          intros x
          specialize ih_body (.cons x bvarVal₁) h_body_b h_body_s
          simp at ih_body
          rw[hall] at ih_body
          exact ih_body.symm
        · have ⟨w, hw⟩ := Classical.not_forall.mp hall
          have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal₁)
              (LExpr.substK (Δ₁.length + 1) (fun _ => v) sub_body) .bool h_body_s : Bool) = false :=
            Bool.eq_false_iff.mpr hw
          rw [denote_quant_all_false bvarVal₁ h_body_s h_subst w hwf]
          symm
          apply denote_quant_all_false _ h_body_b h_body w
          specialize ih_body (.cons w bvarVal₁) h_body_b h_body_s
          simp at ih_body
          rw [hwf] at ih_body
          exact ih_body.symm
      | exist =>
        by_cases hexist : ∃ x : TyDenote tcInterp vt qty',
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal₁)
              (LExpr.substK (Δ₁.length + 1) (fun _ => v) sub_body) .bool h_body_s : Bool) = true
        · obtain ⟨w, hw⟩ := hexist
          rw [denote_quant_exist_true bvarVal₁ h_body_s h_subst w hw]
          symm
          apply denote_quant_exist_true _ h_body_b h_body w
          specialize ih_body (.cons w bvarVal₁) h_body_b h_body_s
          simp at ih_body
          rw [hw] at ih_body
          exact ih_body.symm
        · have hexist_f : ∀ x : TyDenote tcInterp vt qty',
              (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal₁)
                (LExpr.substK (Δ₁.length + 1) (fun _ => v) sub_body) .bool h_body_s : Bool) = false :=
            fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
          rw [denote_quant_exist_false bvarVal₁ h_body_s h_subst hexist_f]
          symm
          apply denote_quant_exist_false _ h_body_b h_body
          intros x
          specialize ih_body (.cons x bvarVal₁) h_body_b h_body_s
          simp at ih_body
          rw [hexist_f] at ih_body
          exact ih_body.symm

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
  exact substK_denote (Δ₁ := []) _ _ _ _ _ h_body h_v h_subst h_lc

/-- Free-variable substitution commutes with denotation. -/
theorem substFvars_denote [DecidableEq T.IDMeta]
    {body : LExpr T.mono} {τ : LMonoTy}
    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    (h_body : LExpr.HasTypeA [] body τ)
    (h_subst : LExpr.HasTypeA [] (LExpr.substFvars body bindings) τ)
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)
    (h_len : bindings.length = sortBindings.length)
    : LExpr.denote tcInterp opInterp
        (fvarVal.withArgs sortBindings h_args)
        vt .nil body τ h_body =
      LExpr.denote tcInterp opInterp fvarVal vt .nil
        (LExpr.substFvars body bindings) τ h_subst := by
  sorry
