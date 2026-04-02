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
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Generalize

namespace Lambda
open Lean Elab Tactic Meta in
/-- Generalize the last argument of the LHS of an equality goal. -/
elab "generalize_lhs_last_arg" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, lhs, _) := goalType.eq? | throwError "Goal is not an equality"
  match lhs with
  | Expr.app _fn lastArg =>
    let (_, newGoal) ← goal.generalize #[{ expr := lastArg }]
    replaceMainGoal [newGoal]
  | _ => throwError "LHS is not a function application"

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
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
      cases qk with
      | all =>
        by_cases hall : ∀ x : TyDenote tcInterp vt qty',
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bv₁ (HList.append bv_insert bv_outer)))
              (LExpr.liftBVars Δ_insert.length body (Δ₁.length + 1)) .bool h_body_l : Bool) = true
        · rw [denote_quant_all_true _ h_body_l h_lifted hall]
          symm; apply denote_quant_all_true; intros x
          rw [← h_ih_body]; exact (hall x)
        · have ⟨w, hw⟩ := Classical.not_forall.mp hall
          have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w (HList.append bv₁ (HList.append bv_insert bv_outer)))
              (LExpr.liftBVars Δ_insert.length body (Δ₁.length + 1)) .bool h_body_l : Bool) = false :=
            Bool.eq_false_iff.mpr hw
          rw [denote_quant_all_false _ h_body_l h_lifted w hwf]
          symm; apply denote_quant_all_false _ h_body_o h_orig w
          rw [← h_ih_body]; exact hwf
      | exist =>
        by_cases hexist : ∃ x : TyDenote tcInterp vt qty',
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bv₁ (HList.append bv_insert bv_outer)))
              (LExpr.liftBVars Δ_insert.length body (Δ₁.length + 1)) .bool h_body_l : Bool) = true
        · obtain ⟨w, hw⟩ := hexist
          rw [denote_quant_exist_true _ h_body_l h_lifted w hw]
          symm; apply denote_quant_exist_true _ h_body_o h_orig w
          rw [← h_ih_body]; exact hw
        · have hexist_f : ∀ x : TyDenote tcInterp vt qty',
              (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bv₁ (HList.append bv_insert bv_outer)))
                (LExpr.liftBVars Δ_insert.length body (Δ₁.length + 1)) .bool h_body_l : Bool) = false :=
            fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
          rw [denote_quant_exist_false _ h_body_l h_lifted hexist_f]
          symm; apply denote_quant_exist_false _ h_body_o h_orig; intros x
          rw [← h_ih_body]; exact (hexist_f x)

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
      simp only [denoteArgs, HList.get_cons_succ]
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
      have : (aty :: Δ_body).length = Δ_body.length + 1 := by simp
      rw [← this]
      have : aty :: (Δ_body ++ Δ_outer) = (aty :: Δ_body) ++ Δ_outer := by simp
      rw [this]
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
      have : (qty :: Δ_body).length = Δ_body.length + 1 := by simp
      rw [← this]
      have : qty :: (Δ_body ++ Δ_outer) = (qty :: Δ_body) ++ Δ_outer := by simp
      rw [this]
      rw [ih_tr (Δ_body := qty :: Δ_body) h_annot.1,
          ih_body (Δ_body := qty :: Δ_body) h_annot.2]

/-! ### Free-variable substitution commutes with denotation -/
set_option pp.proofs true

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
      cases qk with
      | all =>
        by_cases hall : ∀ x : TyDenote tcInterp vt qty',
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bvarVal_body bvarVal_outer))
              (LExpr.substFvarsLifting.go bindings sub_body (Δ_body.length + 1)) .bool h_body_s : Bool) = true
        · rw [denote_quant_all_true _ h_body_s h_subst hall]
          symm; apply denote_quant_all_true; intros x
          rw [← h_ih_body]; exact (hall x)
        · have ⟨w, hw⟩ := Classical.not_forall.mp hall
          have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w (HList.append bvarVal_body bvarVal_outer))
              (LExpr.substFvarsLifting.go bindings sub_body (Δ_body.length + 1)) .bool h_body_s : Bool) = false :=
            Bool.eq_false_iff.mpr hw
          rw [denote_quant_all_false _ h_body_s h_subst w hwf]
          symm; apply denote_quant_all_false _ h_body_b h_body w
          rw [← h_ih_body]; exact hwf
      | exist =>
        by_cases hexist : ∃ x : TyDenote tcInterp vt qty',
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bvarVal_body bvarVal_outer))
              (LExpr.substFvarsLifting.go bindings sub_body (Δ_body.length + 1)) .bool h_body_s : Bool) = true
        · obtain ⟨w, hw⟩ := hexist
          rw [denote_quant_exist_true _ h_body_s h_subst w hw]
          symm; apply denote_quant_exist_true _ h_body_b h_body w
          rw [← h_ih_body]; exact hw
        · have hexist_f : ∀ x : TyDenote tcInterp vt qty',
              (LExpr.denote tcInterp opInterp fvarVal vt (.cons x (HList.append bvarVal_body bvarVal_outer))
                (LExpr.substFvarsLifting.go bindings sub_body (Δ_body.length + 1)) .bool h_body_s : Bool) = false :=
            fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
          rw [denote_quant_exist_false _ h_body_s h_subst hexist_f]
          symm; apply denote_quant_exist_false _ h_body_b h_body; intros x
          rw [← h_ih_body]; exact (hexist_f x)

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
    have := substFvarsLifting_go_denote (tcInterp := tcInterp) (opInterp := opInterp)
      (fvarVal := fvarVal) (vt := vt)
      bvarVal_outer h_args h_keys h_tys_len h_sorts h_wt h_denotes
      (Δ_body := []) .nil h_body h_annot (by simp [h_subst])
    simpa using this

/-! ### `LMonoTy.substMap` — clean type-variable substitution for proofs -/

/-- Apply a simple type-variable substitution (a `Map`) to a monomorphic type.
Unlike `LMonoTy.subst` (which uses multi-scope `Subst` with `hasEmptyScopes`
guard), this is clean for equational reasoning. -/
def LMonoTy.substMap (σ : Map TyIdentifier LMonoTy) : LMonoTy → LMonoTy
  | .ftvar x    => (σ.find? x).getD (.ftvar x)
  | .bitvec n   => .bitvec n
  | .tcons name args => .tcons name (args.map (substMap σ))

theorem substTyVars_substMap (vt : TyVarVal) (σ : Map TyIdentifier LMonoTy) (ty : LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.substMap σ ty) =
    LMonoTy.substTyVars
      (fun x => match Map.find? σ x with | some t => LMonoTy.substTyVars vt t | none => vt x)
      ty := by
  sorry

/-! ### Polymorphic type-checking for `go` -/

/-- Polymorphic version of `go_typeCheck`. When fvar annotations match
`inputTys` and the args are typed at `argTys = inputTys.map (substMap σ)`,
then `go` transforms the type by `substMap σ`. -/
private theorem go_typeCheck_poly [DecidableEq T.IDMeta]
    {σ : Map TyIdentifier LMonoTy}
    {bindings : List (T.Identifier × LExpr T.mono)}
    {Δ_outer : List LMonoTy}
    {argTys inputTys : List LMonoTy}
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) argTys)
    (h_inst : argTys = inputTys.map (LMonoTy.substMap σ))
    (h_inputTys_len : inputTys.length = bindings.length)
    {e : LExpr T.mono} {Δ_body : List LMonoTy} {τ : LMonoTy}
    (h_body : LExpr.HasTypeA (Δ_body ++ Δ_outer) e τ)
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip inputTys) e)
    : LExpr.HasTypeA (Δ_body ++ Δ_outer)
        (LExpr.substFvarsLifting.go bindings e Δ_body.length) (LMonoTy.substMap σ τ) := by
  sorry

/-! ### Polymorphic free-variable substitution commutes with denotation -/

/-- Inner lemma: polymorphic version of `substFvarsLifting_go_denote`.
The body is evaluated at `vt'` with type `τ_body`, and the substituted body
at `vt` with type `τ_subst`, where the semantic sorts agree via
`substTyVars_substMap`. A cast by `h_sort_eq` reconciles the result types. -/
private theorem substFvarsLifting_go_denote_poly [DecidableEq T.IDMeta]
    {σ : Map TyIdentifier LMonoTy}
    {vt : TyVarVal}
    {vt' : TyVarVal}
    (hvt' : vt' = fun x => match σ.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x)

    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    {Δ_outer : List LMonoTy}

    (bvarVal_outer_vt  : BVarVal tcInterp vt  Δ_outer)
    (bvarVal_outer_vt' : BVarVal tcInterp vt' Δ_outer)

    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)

    {argTys inputTys : List LMonoTy}
    (h_argTys_len : argTys.length = bindings.length)
    (h_inputTys_len : inputTys.length = bindings.length)
    (h_inst : argTys = inputTys.map (LMonoTy.substMap σ))
    (h_sorts : sortBindings.map Prod.snd = argTys.map (LMonoTy.substTyVars vt))
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) argTys)
    (h_denotes : h_args = HList.cast h_sorts.symm
        (denoteArgs tcInterp opInterp fvarVal vt bvarVal_outer_vt
          (bindings.map Prod.snd) argTys h_wt))

    {body : LExpr T.mono} {τ_body τ_subst : LMonoTy}
    {Δ_body : List LMonoTy}

    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip inputTys) body)

    (bvarVal_body_vt  : BVarVal tcInterp vt  Δ_body)
    (bvarVal_body_vt' : BVarVal tcInterp vt' Δ_body)

    (h_body  : LExpr.HasTypeA (Δ_body ++ Δ_outer) body τ_body)
    (h_subst : LExpr.HasTypeA (Δ_body ++ Δ_outer)
        (LExpr.substFvarsLifting.go bindings body Δ_body.length) τ_subst)

    (h_sort_eq : LMonoTy.substTyVars vt' τ_body = LMonoTy.substTyVars vt τ_subst)

    (h_td_eq : TyDenote tcInterp vt' τ_body = TyDenote tcInterp vt τ_subst)

    (h_bvar_eq : ∀ i (τ_b : LMonoTy)
        (hb : (Δ_body ++ Δ_outer)[i]? = some τ_b),
        LMonoTy.substTyVars vt' τ_b = LMonoTy.substTyVars vt τ_b ∧
        HEq ((bvarVal_body_vt'.append bvarVal_outer_vt').get i hb)
             ((bvarVal_body_vt.append bvarVal_outer_vt).get i hb))

    : LExpr.denote tcInterp opInterp fvarVal vt
          (HList.append bvarVal_body_vt bvarVal_outer_vt)
          (LExpr.substFvarsLifting.go bindings body Δ_body.length)
          τ_subst h_subst
      = cast h_td_eq
        (LExpr.denote tcInterp opInterp
          (fvarVal.withArgs sortBindings h_args)
          vt' (HList.append bvarVal_body_vt' bvarVal_outer_vt')
          body τ_body h_body) := by
  induction body generalizing Δ_body τ_body τ_subst with
  | const m c =>
    simp only [LExpr.substFvarsLifting.go]
    rw [denote_const _ _ _ _ _ h_subst, denote_const _ _ _ _ _ h_body]
    have hc_subst := HasTypeA.const_inv h_subst
    have hc_body := HasTypeA.const_inv h_body
    subst hc_subst hc_body
    simp
    -- Goal: denoteConst tcInterp vt c = cast h_td_eq (denoteConst tcInterp vt' c)
    -- denoteConst returns ground values independent of vt
    exact denoteConst_cast_vt tcInterp vt vt' c h_td_eq
  | op m o ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some ty =>
      simp only [LExpr.substFvarsLifting.go]
      rw [denote_op _ _ _ _ _ h_subst, denote_op _ _ _ _ _ h_body]
      have ho_subst := HasTypeA.op_inv h_subst
      have ho_body := HasTypeA.op_inv h_body
      subst ho_subst ho_body
      simp
      have : h_td_eq = congrArg (SortDenote tcInterp) h_sort_eq := proof_irrel _ _
      rw [this]
      exact cast_congrArg_dep_fn h_sort_eq (opInterp o.name)
  | bvar m i =>
    simp only [LExpr.substFvarsLifting.go]
    rw [denote_bvar _ _ _ _ _ h_subst, denote_bvar _ _ _ _ _ h_body]
    have hb_subst := HasTypeA.bvar_inv h_subst
    have hb_body := HasTypeA.bvar_inv h_body
    have h_τ_eq : τ_subst = τ_body := by
      have := hb_subst.symm.trans hb_body
      exact Option.some.inj this
    subst h_τ_eq
    have ⟨_, h_heq_b⟩ := h_bvar_eq i _ hb_body
    have : h_td_eq = congrArg (SortDenote tcInterp) h_sort_eq := proof_irrel _ _
    rw [this]
    have h1 : HasTypeA.bvar_inv h_subst = hb_body := proof_irrel _ _
    have h2 : HasTypeA.bvar_inv h_body = hb_body := proof_irrel _ _
    rw [h1]
    exact eq_of_heq (h_heq_b.symm.trans (cast_heq _ _).symm)
  | fvar m name ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some ty =>
      simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
      generalize_lhs_last_arg
      rename_i heq; revert heq
      clear h_subst
      cases hfind : Map.find? bindings name with
      | some e_arg =>
        -- fvar replaced by liftBVars
        simp
        intro heq
        rw [denote_fvar _ _ _ _ _ h_body]
        have hf_body := HasTypeA.fvar_inv h_body
        subst hf_body
        simp
        -- LHS: denote ... (liftBVars depth e_arg) τ_subst heq
        -- RHS: cast h_td_eq (withArgs ... name (substTyVars vt' τ_body))
        have h_orig : LExpr.HasTypeA Δ_outer e_arg τ_subst :=
          liftBVars_hasTypeA_inv heq
        have h_lift := liftBVars_denote (tcInterp := tcInterp) (opInterp := opInterp)
          (fvarVal := fvarVal) (vt := vt) (Δ₁ := []) h_orig heq .nil bvarVal_body_vt bvarVal_outer_vt
        simp [HList.append] at h_lift
        rw [h_lift]
        -- LHS is now: denote ... e_arg τ_subst h_orig (at vt, bvarVal_outer_vt)
        -- RHS: cast h_td_eq (withArgs ... name (substTyVars vt' τ_body))
        -- Get index from Map.find?_index
        obtain ⟨i, h_key_b, h_val_b, h_first_bindings⟩ := Map.find?_index hfind
        -- Get sort binding info
        have h_key : (sortBindings.map Prod.fst)[i]? = some name := by
          rw [← h_keys]; exact h_key_b
        -- Get τ_subst = argTys[i] from h_wt
        have h_i_lt : i < argTys.length := by
          rw [h_argTys_len]
          have := (List.getElem?_eq_some_iff.mp h_val_b).1
          grind
        have h_tys_eq : argTys[i]? = some argTys[i] :=
          List.getElem?_eq_some_iff.mpr ⟨h_i_lt, rfl⟩
        have h_wt_i := List.Forall₂.get? h_wt i h_val_b h_tys_eq
        have h_τ_subst_eq : argTys[i] = τ_subst := HasTypeA_unique h_wt_i h_orig
        subst h_τ_subst_eq
        -- Goal: denote ... e_arg argTys[i] h_orig
        --     = cast h_td_eq (withArgs ... name (substTyVars vt' τ_body))
        have h_sort : (sortBindings.map Prod.snd)[i]? = some (LMonoTy.substTyVars vt' τ_body) := by
          rw [h_sorts, List.getElem?_map, h_tys_eq]; simp
          rw [← h_sort_eq]
        have h_first : ∀ j < i, (sortBindings.map Prod.fst)[j]? ≠ some name := by
          intro j hj; rw [← h_keys]; exact h_first_bindings j hj
        rw [IdentInterp.withArgs_get (tcInterp := tcInterp) fvarVal sortBindings h_args
            name _ i h_key h_sort h_first]
        -- Goal: denote ... e_arg argTys[i] h_orig = cast h_td_eq (h_args.get i h_sort)
        have h_sort_vt : (argTys.map (LMonoTy.substTyVars vt))[i]? = some (LMonoTy.substTyVars vt argTys[i]) := by
          rw [List.getElem?_map, h_tys_eq]; simp
        rw [h_denotes, HList.get_cast_gen h_sorts.symm _ i h_sort_vt h_sort h_sort_eq.symm]
        have h_da_get := denoteArgs_get (tcInterp := tcInterp) (opInterp := opInterp)
          (fvarVal := fvarVal) (vt := vt) (bvarVal := bvarVal_outer_vt)
          h_wt i h_val_b h_tys_eq h_sort_vt
        have h_wt_pi : List.Forall₂.get? h_wt i h_val_b h_tys_eq = h_orig := proof_irrel _ _
        rw [h_wt_pi] at h_da_get
        rw [h_da_get]
        -- Goal: denote ... = cast h_td_eq (h_sort_eq.symm ▸ denote ...)
        -- Round-trip cast
        have : h_td_eq = congrArg (SortDenote tcInterp) h_sort_eq := proof_irrel _ _
        subst this
        rw[cast_subst_roundtrip]
        assumption
      | none =>
        -- fvar unchanged
        simp
        intro h_subst
        rw [denote_fvar _ _ _ _ _ h_subst, denote_fvar _ _ _ _ _ h_body]
        have hf_body := HasTypeA.fvar_inv h_body
        have hf_subst := HasTypeA.fvar_inv h_subst
        subst hf_body hf_subst
        simp
        -- Goal: fvarVal name (substTyVars vt ty) = cast h_td_eq (withArgs ... name (substTyVars vt' ty))
        have h_not_mem : name ∉ (bindings.map Prod.fst) := by
          have := Map.find?_of_not_mem_values _ hfind
          rw [Map.keys_eq_map_fst] at this
          exact this
        rw [h_keys] at h_not_mem
        rw [IdentInterp.withArgs_not_mem _ fvarVal h_args h_not_mem]
        -- Goal: fvarVal name (substTyVars vt ty) = cast h_td_eq (fvarVal name (substTyVars vt' ty))
        have : h_td_eq = congrArg (SortDenote tcInterp) h_sort_eq := proof_irrel _ _
        rw [this]
        exact cast_congrArg_dep_fn h_sort_eq (fvarVal name)
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
    let ⟨aty_b, h_fn_b, h_arg_b⟩ := HasTypeA.app_inv h_body
    let ⟨aty_s, h_fn_s, h_arg_s⟩ := HasTypeA.app_inv h_subst
    have h_annot_fn : fvars_annotated_by (bindings.map Prod.fst |>.zip inputTys) fn := by
      simp [fvars_annotated_by] at h_annot; exact h_annot.1
    have h_annot_arg : fvars_annotated_by (bindings.map Prod.fst |>.zip inputTys) arg := by
      simp [fvars_annotated_by] at h_annot; exact h_annot.2
    have h_go_fn := go_typeCheck_poly h_wt h_inst h_inputTys_len h_fn_b h_annot_fn
    have h_fn_s_tc := LExpr.HasTypeA_to_typeCheck h_fn_s
    rw [LExpr.HasTypeA_to_typeCheck h_go_fn] at h_fn_s_tc
    -- h_fn_s_tc : some (substMap σ (aty_b.arrow τ_body)) = some (aty_s.arrow τ_subst)
    simp [LMonoTy.arrow, LMonoTy.substMap] at h_fn_s_tc
    obtain ⟨h_aty_eq, h_τ_eq⟩ := h_fn_s_tc
    -- h_aty_eq : substMap σ aty_b = aty_s, h_τ_eq : substMap σ τ_body = τ_subst
    subst h_aty_eq; subst h_τ_eq
    rw [denote_app _ h_fn_s h_arg_s h_subst, denote_app _ h_fn_b h_arg_b h_body]
    -- Sort equalities for IHs
    have h_sort_eq_arg : LMonoTy.substTyVars vt' aty_b =
        LMonoTy.substTyVars vt (LMonoTy.substMap σ aty_b) := by
      rw [substTyVars_substMap]; congr
    have h_sort_eq_fn : LMonoTy.substTyVars vt' (aty_b.arrow τ_body) =
        LMonoTy.substTyVars vt ((LMonoTy.substMap σ aty_b).arrow (LMonoTy.substMap σ τ_body)) := by
      unfold LMonoTy.arrow LMonoTy.substTyVars
      congr 1
      simp[Lambda.LMonoTy.substTyVars.map]
      constructor
      . exact h_sort_eq_arg
      · exact h_sort_eq
    have h_td_eq_arg : TyDenote tcInterp vt' aty_b = TyDenote tcInterp vt (LMonoTy.substMap σ aty_b) :=
      congrArg (SortDenote tcInterp) h_sort_eq_arg
    have h_td_eq_fn : TyDenote tcInterp vt' (aty_b.arrow τ_body) =
        TyDenote tcInterp vt ((LMonoTy.substMap σ aty_b).arrow (LMonoTy.substMap σ τ_body)) :=
      congrArg (SortDenote tcInterp) h_sort_eq_fn
    rw [ih_fn h_annot_fn bvarVal_body_vt bvarVal_body_vt' h_fn_b h_fn_s h_sort_eq_fn h_td_eq_fn h_bvar_eq]
    rw [ih_arg h_annot_arg bvarVal_body_vt bvarVal_body_vt' h_arg_b h_arg_s h_sort_eq_arg h_td_eq_arg h_bvar_eq]
    exact cast_app h_td_eq_fn h_td_eq_arg h_td_eq _ _
  | abs m name ty body' ih =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some aty =>
      simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
      let ⟨rty_b, h_eq_b, h_body_b⟩ := HasTypeA.abs_inv h_body
      let ⟨rty_s, h_eq_s, h_body_s⟩ := HasTypeA.abs_inv h_subst
      subst h_eq_b; cases h_eq_s
      -- Extract arrow components from h_sort_eq
      have h_sort_eq_aty : LMonoTy.substTyVars vt' aty = LMonoTy.substTyVars vt aty := by
        have := congrArg (fun s => match s with | .tcons _ args => args[0]? | _ => none) h_sort_eq
        simp [LMonoTy.substTyVars, Lambda.LMonoTy.substTyVars.map] at this
        exact this
      have h_sort_eq_rty : LMonoTy.substTyVars vt' rty_b = LMonoTy.substTyVars vt rty_s := by
        have := congrArg (fun s => match s with | .tcons _ args => args[1]? | _ => none) h_sort_eq
        simp [LMonoTy.substTyVars, Lambda.LMonoTy.substTyVars.map] at this
        exact this
      have h_td_eq_aty : TyDenote tcInterp vt' aty = TyDenote tcInterp vt aty :=
        congrArg (SortDenote tcInterp) h_sort_eq_aty
      have h_td_eq_rty : TyDenote tcInterp vt' rty_b = TyDenote tcInterp vt rty_s :=
        congrArg (SortDenote tcInterp) h_sort_eq_rty
      rw [denote_abs (HList.append bvarVal_body_vt bvarVal_outer_vt) h_body_s h_subst,
          denote_abs _ h_body_b h_body]
      -- Goal: (fun x => denote ... (go body') rty_s) = cast h_td_eq (fun x => denote ... body' rty_b)
      -- h_td_eq : (TyDenote vt' aty → TyDenote vt' rty_b) = (TyDenote vt aty → TyDenote vt rty_s)
      -- Push cast through arrow, then funext
      funext x
      -- x : TyDenote vt aty
      -- RHS: (cast h_td_eq f) x = cast h_td_eq_rty (f (cast h_td_eq_aty.symm x))
      rw [cast_fn_apply h_td_eq h_td_eq_aty h_td_eq_rty]
      -- Now apply IH with Δ_body := aty :: Δ_body
      have h_body_s' : LExpr.HasTypeA ((aty :: Δ_body) ++ Δ_outer)
          (LExpr.substFvarsLifting.go bindings body' (aty :: Δ_body).length) rty_s := by
        simp [List.length]; exact h_body_s
      have h_body_b' : LExpr.HasTypeA ((aty :: Δ_body) ++ Δ_outer) body' rty_b := by
        simp; exact h_body_b
      -- The LHS has `go body' (Δ_body.length + 1)` but IH needs `go body' (aty :: Δ_body).length`
      -- These are definitionally equal, so just use conv to change the HasTypeA proof
      have : LExpr.denote tcInterp opInterp fvarVal vt
          (HList.cons x (HList.append bvarVal_body_vt bvarVal_outer_vt))
          (LExpr.substFvarsLifting.go bindings body' (Δ_body.length + 1)) rty_s h_body_s =
        LExpr.denote tcInterp opInterp fvarVal vt
          (HList.append (.cons x bvarVal_body_vt) bvarVal_outer_vt)
          (LExpr.substFvarsLifting.go bindings body' (aty :: Δ_body).length) rty_s h_body_s' := by
        rfl
      rw [this]
      rw [ih h_annot (.cons x bvarVal_body_vt) (.cons (cast h_td_eq_aty.symm x) bvarVal_body_vt')
          h_body_b' h_body_s' h_sort_eq_rty h_td_eq_rty]
      · -- main goal: cast ... (denote ... h_body_b') = cast ... (denote ... h_body_b)
        congr 1
      · -- h_bvar_eq extended
        intro i τ_b hb
        cases i with
        | zero =>
          simp at hb
          subst hb
          constructor
          · exact h_sort_eq_aty
          · simp [HList.append]
        | succ j =>
          simp at hb ⊢
          exact h_bvar_eq j τ_b hb
  | ite m c t e ih_c ih_t ih_e =>
    simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
    let ⟨h_c_b, h_t_b, h_e_b⟩ := HasTypeA.ite_inv h_body
    let ⟨h_c_s, h_t_s, h_e_s⟩ := HasTypeA.ite_inv h_subst
    -- Sort equalities for IHs
    -- Condition is .bool on both sides
    have h_sort_eq_c : LMonoTy.substTyVars vt' LMonoTy.bool =
        LMonoTy.substTyVars vt LMonoTy.bool := by rfl
    have h_td_eq_c : TyDenote tcInterp vt' LMonoTy.bool =
        TyDenote tcInterp vt LMonoTy.bool :=
      congrArg (SortDenote tcInterp) h_sort_eq_c
    -- go_typeCheck_poly on c gives HasTypeA ... (go c) (substMap σ .bool) = HasTypeA ... (go c) .bool
    -- So h_c_s types at .bool and go c types at substMap σ .bool = .bool
    -- For ih_t and ih_e, use h_sort_eq directly
    rw [denote_ite _ h_c_s h_t_s h_e_s h_subst, denote_ite _ h_c_b h_t_b h_e_b h_body]
    rw [ih_c h_annot.1 bvarVal_body_vt bvarVal_body_vt' h_c_b h_c_s h_sort_eq_c h_td_eq_c h_bvar_eq]
    rw [ih_t h_annot.2.1 bvarVal_body_vt bvarVal_body_vt' h_t_b h_t_s h_sort_eq h_td_eq h_bvar_eq]
    rw [ih_e h_annot.2.2 bvarVal_body_vt bvarVal_body_vt' h_e_b h_e_s h_sort_eq h_td_eq h_bvar_eq]
    -- cast h_td_eq_c is Bool = Bool, so identity
    have : h_td_eq_c = rfl := proof_irrel _ _
    rw [this]; simp [cast]
    -- Goal: bif ... then cast h_td_eq ... else cast h_td_eq ... = cast h_td_eq (bif ... then ... else ...)
    cases (LExpr.denote tcInterp opInterp (fvarVal.withArgs sortBindings h_args) vt'
      (HList.append bvarVal_body_vt' bvarVal_outer_vt') c LMonoTy.bool h_c_b) <;> rfl
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
    let ⟨ty_b, h_τ_b, h_1_b, h_2_b⟩ := HasTypeA.eq_inv h_body
    let ⟨ty_s, h_τ_s, h_1_s, h_2_s⟩ := HasTypeA.eq_inv h_subst
    subst h_τ_b; cases h_τ_s
    -- Derive ty_s = substMap σ ty_b
    have h_go_e1 := go_typeCheck_poly h_wt h_inst h_inputTys_len h_1_b h_annot.1
    have h_ty_eq : ty_s = LMonoTy.substMap σ ty_b := by
      have h1 := LExpr.HasTypeA_to_typeCheck h_1_s
      rw [LExpr.HasTypeA_to_typeCheck h_go_e1] at h1
      cases h1; rfl
    subst h_ty_eq
    have h_sort_eq_sub : LMonoTy.substTyVars vt' ty_b =
        LMonoTy.substTyVars vt (LMonoTy.substMap σ ty_b) := by
      rw [substTyVars_substMap]; congr
    have h_td_eq_sub : TyDenote tcInterp vt' ty_b =
        TyDenote tcInterp vt (LMonoTy.substMap σ ty_b) :=
      congrArg (SortDenote tcInterp) h_sort_eq_sub
    -- Both sides are .bool, so h_td_eq is Bool = Bool
    have h_td_rfl : h_td_eq = rfl := proof_irrel _ _
    rw [h_td_rfl]; simp [cast]
    -- Now goal has no cast on the outer level
    have h_ih1 := ih1 h_annot.1 bvarVal_body_vt bvarVal_body_vt' h_1_b h_1_s h_sort_eq_sub h_td_eq_sub h_bvar_eq
    have h_ih2 := ih2 h_annot.2 bvarVal_body_vt bvarVal_body_vt' h_2_b h_2_s h_sort_eq_sub h_td_eq_sub h_bvar_eq
    by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal_body_vt bvarVal_outer_vt)
        (LExpr.substFvarsLifting.go bindings e1 Δ_body.length) (LMonoTy.substMap σ ty_b) h_1_s =
      LExpr.denote tcInterp opInterp fvarVal vt
        (HList.append bvarVal_body_vt bvarVal_outer_vt)
        (LExpr.substFvarsLifting.go bindings e2 Δ_body.length) (LMonoTy.substMap σ ty_b) h_2_s
    · rw [denote_eq_true _ h_1_s h_2_s h_subst heq,
          denote_eq_true _ h_1_b h_2_b h_body
            (cast_injective h_td_eq_sub (h_ih1.symm.trans (heq.trans h_ih2)))]
    · rw [denote_eq_false _ h_1_s h_2_s h_subst heq,
          denote_eq_false _ h_1_b h_2_b h_body
            (by intro h; apply heq; rw [h_ih1, h_ih2, h])]
  | quant m qk name qty tr sub_body ih_tr ih_body =>
    cases qty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some qty' =>
      simp only [LExpr.substFvarsLifting.go] at h_subst ⊢
      let ⟨_, h_τ_b, h_tr_b, h_body_b⟩ := HasTypeA.quant_inv h_body
      let ⟨_, h_τ_s, h_tr_s, h_body_s⟩ := HasTypeA.quant_inv h_subst
      subst h_τ_b; cases h_τ_s
      -- Both sides are .bool, so h_td_eq is Bool = Bool
      have h_td_rfl : h_td_eq = rfl := proof_irrel _ _
      rw [h_td_rfl]; simp [cast]
      -- Need h_sort_eq_qty for the quantifier domain
      -- From the plan: go doesn't change type annotations, so both sides have qty' at index 0.
      -- go_typeCheck_poly on sub_body gives HasTypeA with substMap σ applied.
      -- Since the context has qty' at index 0, substMap σ qty' = qty'.
      -- Then substTyVars_substMap gives substTyVars vt (substMap σ qty') = substTyVars vt' qty'.
      -- Combined: substTyVars vt qty' = substTyVars vt' qty'.
      have h_sort_eq_qty : LMonoTy.substTyVars vt' qty' = LMonoTy.substTyVars vt qty' := by
        -- From go_typeCheck_poly: go sub_body types at substMap σ .bool = .bool in context qty' :: Δ_body ++ Δ_outer.
        -- The bvar at index 0 has type qty' in the original context.
        -- In the substituted context, it would have type substMap σ qty' if the context changed,
        -- but the context is the same (qty' :: ...), so substMap σ qty' = qty'.
        -- Then substTyVars_substMap gives the result.
        -- For now, this needs a lemma about substMap σ qty' = qty' for binder types.
        -- This is the same issue as abs case but there we got it from h_sort_eq on the arrow.
        -- Here we need it separately. Use substTyVars_substMap with substMap σ qty' = qty'.
        -- TODO: prove substMap σ qty' = qty' from the context
        rw [← substTyVars_substMap (σ := σ) (vt := vt) (vt' := vt') hvt']
      have h_td_eq_qty : TyDenote tcInterp vt' qty' = TyDenote tcInterp vt qty' :=
        congrArg (SortDenote tcInterp) h_sort_eq_qty
      -- Prepare IH arguments
      have h_body_s' : LExpr.HasTypeA ((qty' :: Δ_body) ++ Δ_outer)
          (LExpr.substFvarsLifting.go bindings sub_body (qty' :: Δ_body).length) .bool := by
        simp [List.length]; exact h_body_s
      have h_body_b' : LExpr.HasTypeA ((qty' :: Δ_body) ++ Δ_outer) sub_body .bool := by
        simp; exact h_body_b
      -- Extended h_bvar_eq for qty' :: Δ_body
      have h_bvar_eq_ext : ∀ (x : TyDenote tcInterp vt qty'),
          ∀ (i : Nat) (τ_b : LMonoTy) (hb : ((qty' :: Δ_body) ++ Δ_outer)[i]? = some τ_b),
          LMonoTy.substTyVars vt' τ_b = LMonoTy.substTyVars vt τ_b ∧
            (HList.append (.cons (cast h_td_eq_qty.symm x) bvarVal_body_vt') bvarVal_outer_vt').get i hb ≍
              (HList.append (.cons x bvarVal_body_vt) bvarVal_outer_vt).get i hb := by
        intro x i τ_b hb
        cases i with
        | zero =>
          simp at hb; subst hb
          exact ⟨h_sort_eq_qty, by simp [HList.append]; exact cast_heq h_td_eq_qty.symm x⟩
        | succ j =>
          simp at hb ⊢
          exact h_bvar_eq j τ_b hb
      -- Helper: IH applied to sub_body for a given x
      have ih_body_applied : ∀ (x : TyDenote tcInterp vt qty'),
          LExpr.denote tcInterp opInterp fvarVal vt
            (HList.append (.cons x bvarVal_body_vt) bvarVal_outer_vt)
            (LExpr.substFvarsLifting.go bindings sub_body (qty' :: Δ_body).length) .bool h_body_s' =
          LExpr.denote tcInterp opInterp (fvarVal.withArgs sortBindings h_args) vt'
            (HList.append (.cons (cast h_td_eq_qty.symm x) bvarVal_body_vt') bvarVal_outer_vt')
            sub_body .bool h_body_b' := by
        intro x
        have h := ih_body h_annot.2 (.cons x bvarVal_body_vt)
          (.cons (cast h_td_eq_qty.symm x) bvarVal_body_vt')
          h_body_b' h_body_s' h_sort_eq h_td_eq (h_bvar_eq_ext x)
        simp at h; exact h
      cases qk with
      | all =>
        trace_state
        sorry
      | exist =>
        sorry

/-- Polymorphic version of `substFvarsLifting_denote`. Wraps the `go` version
with `Δ_body = []`. -/
theorem substFvarsLifting_denote_poly [DecidableEq T.IDMeta]
    {σ : Map TyIdentifier LMonoTy}
    {vt : TyVarVal}
    {vt' : TyVarVal}
    (hvt' : vt' = fun x => match σ.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x)

    {body : LExpr T.mono} {τ_body τ_subst : LMonoTy}
    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    {Δ_outer : List LMonoTy}
    (bvarVal_outer_vt  : BVarVal tcInterp vt  Δ_outer)
    (bvarVal_outer_vt' : BVarVal tcInterp vt' Δ_outer)
    (h_body  : LExpr.HasTypeA Δ_outer body τ_body)
    (h_subst : LExpr.HasTypeA Δ_outer (LExpr.substFvarsLifting body bindings) τ_subst)
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)
    {argTys inputTys : List LMonoTy}
    (h_argTys_len : argTys.length = bindings.length)
    (h_inputTys_len : inputTys.length = bindings.length)
    (h_inst : argTys = inputTys.map (LMonoTy.substMap σ))
    (h_sorts : sortBindings.map Prod.snd = argTys.map (LMonoTy.substTyVars vt))
    (h_wt : List.Forall₂ (LExpr.HasTypeA Δ_outer) (bindings.map Prod.snd) argTys)
    (h_denotes : h_args = HList.cast h_sorts.symm
        (denoteArgs tcInterp opInterp fvarVal vt bvarVal_outer_vt
          (bindings.map Prod.snd) argTys h_wt))
    (h_annot : fvars_annotated_by (bindings.map Prod.fst |>.zip inputTys) body)
    (h_sort_eq : LMonoTy.substTyVars vt' τ_body = LMonoTy.substTyVars vt τ_subst)
    (h_td_eq : TyDenote tcInterp vt' τ_body = TyDenote tcInterp vt τ_subst)
    (h_bvar_eq : ∀ i (τ_b : LMonoTy)
        (hb : Δ_outer[i]? = some τ_b),
        LMonoTy.substTyVars vt' τ_b = LMonoTy.substTyVars vt τ_b ∧
        HEq (bvarVal_outer_vt'.get i hb) (bvarVal_outer_vt.get i hb))
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal_outer_vt
          (LExpr.substFvarsLifting body bindings) τ_subst h_subst
      = cast h_td_eq
        (LExpr.denote tcInterp opInterp
          (fvarVal.withArgs sortBindings h_args)
          vt' bvarVal_outer_vt' body τ_body h_body) := by
  sorry
