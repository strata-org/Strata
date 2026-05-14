/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.LExprAnnotated

/-!
## Denotation Properties

Extensionality, irrelevance, and structural properties of `denote`.

- `denote_ext` — extensionality: denotation depends only on used ops, fvars, and bvars
- `denote_irrel_of_lcAt` — closed expressions are independent of the bvar valuation
- `denote_replaceMetadata` — denotation is invariant under metadata replacement
- `denoteArgs_eq_of_denote_eq` / `denoteArgs_eq_implies_denote_eq` — pointwise ↔ aggregate argument equality
-/

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### denoteConst properties -/

/-- Casting a function and its argument is the same as casting the result. -/
theorem cast_app {A A' B B' : Sort _}
    (h_fn : (A → B) = (A' → B')) (h_arg : A = A') (h_ret : B = B')
    (f : A → B) (x : A)
    : (cast h_fn f) (cast h_arg x) = cast h_ret (f x) := by
  subst h_arg; subst h_ret; rfl

/-- Apply a cast function to an argument in the target domain. -/
theorem cast_fn_apply {A A' B B' : Sort _}
    (h_fn : (A → B) = (A' → B')) (h_arg : A = A') (h_ret : B = B')
    (f : A → B) (x : A')
    : (cast h_fn f) x = cast h_ret (f (cast h_arg.symm x)) := by
  subst h_arg; subst h_ret; rfl

/-- `cast` is injective. -/
theorem cast_injective {α β : Sort _} (h : α = β) {a b : α}
    (heq : cast h a = cast h b) : a = b := by
  cases h; exact heq

/-- `denoteConst` is independent of the type variable valuation `vt`. -/
theorem denoteConst_cast_vt (vt vt' : TyVarVal) (c : LConst)
    (h : TyDenote tcInterp vt' c.ty = TyDenote tcInterp vt c.ty)
    : denoteConst tcInterp vt c = cast h (denoteConst tcInterp vt' c) := by
  cases c <;> simp [denoteConst, LConst.ty, TyDenote, LMonoTy.substTyVars] at h ⊢ <;> grind

/-- If the body denotation agrees for all witnesses, the quantifier denotation
agrees regardless of quantifier kind. Allows different expressions, metadata,
names, triggers, bvarVals, opInterps, and fvarVals on each side. -/
theorem denote_quant_congr
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp₁ opInterp₂ : OpInterp tcInterp}
    {fvarVal₁ : FreeVarVal T tcInterp}
    {fvarVal₂ : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m₁ m₂ : T.Metadata} {name₁ name₂ : String}
    {tr₁ body₁ tr₂ body₂ : LExpr T.mono} {qty : LMonoTy}
    {k : QuantifierKind}
    {Δ₁ Δ₂ : List LMonoTy}
    {bvarVal₁ : BVarVal tcInterp vt Δ₁}
    {bvarVal₂ : BVarVal tcInterp vt Δ₂}
    (h_body₁ : LExpr.HasTypeA (qty :: Δ₁) body₁ .bool)
    (h_body₂ : LExpr.HasTypeA (qty :: Δ₂) body₂ .bool)
    (h_quant₁ : LExpr.HasTypeA Δ₁ (.quant m₁ k name₁ (some qty) tr₁ body₁) .bool)
    (h_quant₂ : LExpr.HasTypeA Δ₂ (.quant m₂ k name₂ (some qty) tr₂ body₂) .bool)
    (h_eq : ∀ x : TyDenote tcInterp vt qty,
      (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body₁ .bool h_body₁ : Bool) =
      (LExpr.denote tcInterp opInterp₂ fvarVal₂ vt (.cons x bvarVal₂) body₂ .bool h_body₂ : Bool))
    : (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt bvarVal₁
        (.quant m₁ k name₁ (some qty) tr₁ body₁) .bool h_quant₁ : Bool) =
      (LExpr.denote tcInterp opInterp₂ fvarVal₂ vt bvarVal₂
        (.quant m₂ k name₂ (some qty) tr₂ body₂) .bool h_quant₂ : Bool) := by
  cases k with
  | all =>
    by_cases hall : ∀ x, (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body₁ .bool h_body₁ : Bool) = true
    · rw [denote_quant_all_true _ h_body₁ h_quant₁ hall]
      exact (denote_quant_all_true _ h_body₂ h_quant₂ (fun x => (h_eq x) ▸ hall x)).symm
    · have ⟨w, hw⟩ := Classical.not_forall.mp hall
      have hwf := Bool.eq_false_iff.mpr hw
      rw [denote_quant_all_false _ h_body₁ h_quant₁ w hwf]
      exact (denote_quant_all_false _ h_body₂ h_quant₂ w ((h_eq w) ▸ hwf)).symm
  | exist =>
    by_cases hexist : ∃ x, (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body₁ .bool h_body₁ : Bool) = true
    · obtain ⟨w, hw⟩ := hexist
      rw [denote_quant_exist_true _ h_body₁ h_quant₁ w hw]
      exact (denote_quant_exist_true _ h_body₂ h_quant₂ w ((h_eq w) ▸ hw)).symm
    · have hexist_f : ∀ x, (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body₁ .bool h_body₁ : Bool) = false :=
        fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
      rw [denote_quant_exist_false _ h_body₁ h_quant₁ hexist_f]
      exact (denote_quant_exist_false _ h_body₂ h_quant₂ (fun x => (h_eq x) ▸ hexist_f x)).symm

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
    · have h_eq_rhs : LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂') e1 ty' h_1₂ =
            LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂') e2 ty' h_2₂ := by
        rw [← ih1 h_lc.1 h_1₁ h_1₂ bv₁, ← ih2 h_lc.2 h_2₁ h_2₂ bv₁]; exact heq
      rw [denote_eq_true _ h_1₁ h_2₁ h₁ heq, denote_eq_true _ h_1₂ h_2₂ h₂ h_eq_rhs]
    · have h_neq_rhs : LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂') e1 ty' h_1₂ ≠
            LExpr.denote tcInterp opInterp fvarVal vt (HList.append bv₁ bv₂') e2 ty' h_2₂ := by
        rw [← ih1 h_lc.1 h_1₁ h_1₂ bv₁, ← ih2 h_lc.2 h_2₁ h_2₂ bv₁]; exact heq
      rw [denote_eq_false _ h_1₁ h_2₁ h₁ heq, denote_eq_false _ h_1₂ h_2₂ h₂ h_neq_rhs]
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
      exact denote_quant_congr h_body₁ h_body₂ h₁ h₂ fun x => by
        specialize ih_body (h_len ▸ h_lc.2) h_body₁ h_body₂ (.cons x bv₁)
        simp only [HList.append] at ih_body
        exact ih_body

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

/-! ### Collecting ops and bvar indices from an expression -/

/-- The set of operation names (with type annotations) used in an expression. -/
def LExpr.usedOps : LExpr ⟨T, TyTy⟩ → List (Identifier T.IDMeta × Option TyTy)
  | .op _ o ty => [(o, ty)]
  | .const _ _ | .bvar _ _ | .fvar _ _ _ => []
  | .abs _ _ _ e => usedOps e
  | .quant _ _ _ _ tr e => usedOps tr ++ usedOps e
  | .app _ fn arg => usedOps fn ++ usedOps arg
  | .ite _ c t e => usedOps c ++ usedOps t ++ usedOps e
  | .eq _ e1 e2 => usedOps e1 ++ usedOps e2

/-- The set of *outer* bound variable indices referenced by an expression.
Under each binder, index 0 (the locally-bound variable) is dropped and
all other indices are decremented by 1. -/
def LExpr.usedBvars : LExpr ⟨T, TyTy⟩ → List Nat
  | .bvar _ i => [i]
  | .const _ _ | .op _ _ _ | .fvar _ _ _ => []
  | .abs _ _ _ e => usedBvars e |>.filterMap (fun i => if i = 0 then none else some (i - 1))
  | .quant _ _ _ _ tr e =>
    let shift := fun i => if i = 0 then none else some (i - 1)
    (usedBvars tr |>.filterMap shift) ++ (usedBvars e |>.filterMap shift)
  | .app _ fn arg => usedBvars fn ++ usedBvars arg
  | .ite _ c t e => usedBvars c ++ usedBvars t ++ usedBvars e
  | .eq _ e1 e2 => usedBvars e1 ++ usedBvars e2

private theorem bvar_ext_cons
    {bvarVal₁ bvarVal₂ : BVarVal tcInterp vt Δ}
    {bvars : List Nat}
    (x : TyDenote tcInterp vt a)
    (h_bvar : ∀ i (τ' : LMonoTy) (h₁ : Δ[i]? = some τ') (h₂ : Δ[i]? = some τ'),
        i ∈ bvars.filterMap (fun i => if i = 0 then none else some (i - 1)) →
        bvarVal₁.get i h₁ = bvarVal₂.get i h₂)
    : ∀ i (τ' : LMonoTy) (h₁ : (a :: Δ)[i]? = some τ') (h₂ : (a :: Δ)[i]? = some τ'),
        i ∈ bvars → HList.get (.cons x bvarVal₁) i h₁ = HList.get (.cons x bvarVal₂) i h₂ := by
  intro i τ' hi₁ hi₂ hb
  cases i with
  | zero =>
    have h_eq : τ' = a := by simpa using hi₁.symm
    subst h_eq
    rw [HList.get_cons_zero, HList.get_cons_zero]
  | succ j =>
    rw [HList.get_cons_succ, HList.get_cons_succ]
    exact h_bvar j τ' (by simpa using hi₁) (by simpa using hi₂)
      (List.mem_filterMap.mpr ⟨j + 1, hb, by simp⟩)

/-! ### Extensionality for denote -/

/-- If two interpretations agree on all free variables, operations, and bound
variables that appear in an expression, then `denote` produces the same
result. -/
theorem denote_ext
    {e : LExpr T.mono} {τ : LMonoTy}
    {Δ : List LMonoTy}
    {opInterp₁ opInterp₂ : OpInterp tcInterp}
    {fvarVal₁ fvarVal₂ : FreeVarVal T tcInterp}
    {bvarVal₁ bvarVal₂ : BVarVal tcInterp vt Δ}
    (h_op : ∀ o ty, (o, some ty) ∈ e.usedOps → opInterp₁ o.name (LMonoTy.substTyVars vt ty) = opInterp₂ o.name (LMonoTy.substTyVars vt ty))
    (h_fvar : ∀ name ty, (name, some ty) ∈ e.freeVars → fvarVal₁ name (LMonoTy.substTyVars vt ty) = fvarVal₂ name (LMonoTy.substTyVars vt ty))
    (h_bvar : ∀ i (τ' : LMonoTy) (h₁ : Δ[i]? = some τ') (h₂ : Δ[i]? = some τ'), i ∈ e.usedBvars → bvarVal₁.get i h₁ = bvarVal₂.get i h₂)
    (h₁ : LExpr.HasTypeA Δ e τ)
    (h₂ : LExpr.HasTypeA Δ e τ)
    : LExpr.denote tcInterp opInterp₁ fvarVal₁ vt bvarVal₁ e τ h₁ =
      LExpr.denote tcInterp opInterp₂ fvarVal₂ vt bvarVal₂ e τ h₂ := by
  induction e generalizing Δ τ bvarVal₁ bvarVal₂ with
  | const => rfl
  | op _ _ ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some ty =>
      simp [LExpr.denote]
      rw[h_op _ _ (List.Mem.head _)]
  | fvar _ _ ty =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some ty =>
      simp [LExpr.denote]
      rw[h_fvar _ _ (List.Mem.head _)]
  | bvar m i =>
    rw [denote_bvar _ _ _ _ bvarVal₁ h₁, denote_bvar _ _ _ _ bvarVal₂ h₂]
    exact h_bvar i _ (HasTypeA.bvar_inv h₁) (HasTypeA.bvar_inv h₂) (List.Mem.head _)
  | app _ fn arg ih_fn ih_arg =>
    have ⟨aty, h_fn₁, h_arg₁⟩ := HasTypeA.app_inv h₁
    have ⟨aty', h_fn₂, h_arg₂⟩ := HasTypeA.app_inv h₂
    have h_aty : aty = aty' := by
      have h_tc₁ := LExpr.HasTypeA_to_typeCheck h_fn₁
      have h_tc₂ := LExpr.HasTypeA_to_typeCheck h_fn₂
      rw [h_tc₁] at h_tc₂; cases h_tc₂; rfl
    subst h_aty
    rw [denote_app _ h_fn₁ h_arg₁ h₁, denote_app _ h_fn₂ h_arg₂ h₂]
    rw [ih_fn
        (fun o ty ho => h_op o ty (List.mem_append_left _ ho))
        (fun n ty hf => h_fvar n ty (List.mem_append_left _ hf))
        (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ hb))
        h_fn₁ h_fn₂,
      ih_arg
        (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
        (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
        (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb))
        h_arg₁ h_arg₂]
  | ite _ c t e ih_c ih_t ih_e =>
    have ⟨h_c₁, h_t₁, h_e₁⟩ := HasTypeA.ite_inv h₁
    have ⟨h_c₂, h_t₂, h_e₂⟩ := HasTypeA.ite_inv h₂
    rw [denote_ite _ h_c₁ h_t₁ h_e₁, denote_ite _ h_c₂ h_t₂ h_e₂]
    rw [ih_c (fun o ty ho => h_op o ty (List.mem_append_left _ (List.mem_append_left _ ho)))
            (fun n ty hf => h_fvar n ty (List.mem_append_left _ (List.mem_append_left _ hf)))
            (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ (List.mem_append_left _ hb)))
            h_c₁ h_c₂,
        ih_t (fun o ty ho => h_op o ty (List.mem_append_left _ (List.mem_append_right _ ho)))
            (fun n ty hf => h_fvar n ty (List.mem_append_left _ (List.mem_append_right _ hf)))
            (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ (List.mem_append_right _ hb)))
            h_t₁ h_t₂,
        ih_e (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
            (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
            (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb))
            h_e₁ h_e₂]
  | eq _ e1 e2 ih1 ih2 =>
    have ⟨ty', h_bool₁, h_1₁, h_2₁⟩ := HasTypeA.eq_inv h₁
    have ⟨ty'', h_bool₂, h_1₂, h_2₂⟩ := HasTypeA.eq_inv h₂
    subst h_bool₁; cases h_bool₂
    have h_ty : ty' = ty'' := by
      have h_tc₁ := LExpr.HasTypeA_to_typeCheck h_1₁
      have h_tc₂ := LExpr.HasTypeA_to_typeCheck h_1₂
      rw [h_tc₁] at h_tc₂; exact Option.some.inj h_tc₂
    subst h_ty
    by_cases heq : LExpr.denote tcInterp opInterp₁ fvarVal₁ vt bvarVal₁ e1 ty' h_1₁ =
        LExpr.denote tcInterp opInterp₁ fvarVal₁ vt bvarVal₁ e2 ty' h_2₁
    · have h_eq_rhs : LExpr.denote tcInterp opInterp₂ fvarVal₂ vt bvarVal₂ e1 ty' h_1₂ =
            LExpr.denote tcInterp opInterp₂ fvarVal₂ vt bvarVal₂ e2 ty' h_2₂ := by
        rw [← ih1 (fun o ty ho => h_op o ty (List.mem_append_left _ ho))
                    (fun n ty hf => h_fvar n ty (List.mem_append_left _ hf))
                    (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ hb)) h_1₁ h_1₂,
                ← ih2 (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
                    (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
                    (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)) h_2₁ h_2₂]; exact heq
      rw [denote_eq_true _ h_1₁ h_2₁ h₁ heq, denote_eq_true _ h_1₂ h_2₂ h₂ h_eq_rhs]
    · have h_neq_rhs : LExpr.denote tcInterp opInterp₂ fvarVal₂ vt bvarVal₂ e1 ty' h_1₂ ≠
            LExpr.denote tcInterp opInterp₂ fvarVal₂ vt bvarVal₂ e2 ty' h_2₂ := by
        rw [← ih1 (fun o ty ho => h_op o ty (List.mem_append_left _ ho))
                    (fun n ty hf => h_fvar n ty (List.mem_append_left _ hf))
                    (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ hb)) h_1₁ h_1₂,
                ← ih2 (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
                    (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
                    (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)) h_2₁ h_2₂]; exact heq
      rw [denote_eq_false _ h_1₁ h_2₁ h₁ heq, denote_eq_false _ h_1₂ h_2₂ h₂ h_neq_rhs]
  | abs _ _ ty body ih_body =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some aty =>
      have ⟨_, h_eq₁, h_body₁⟩ := HasTypeA.abs_inv h₁
      have ⟨_, h_eq₂, h_body₂⟩ := HasTypeA.abs_inv h₂
      subst h_eq₁; cases h_eq₂
      rw [denote_abs _ h_body₁ h₁, denote_abs _ h_body₂ h₂]
      funext x
      apply ih_body
      · -- h_op: usedOps (abs ...) = usedOps body
        exact fun o ty ho => h_op o ty ho
      · -- h_fvar: freeVars (abs ...) = freeVars body
        exact fun n ty hf => h_fvar n ty hf
      · -- h_bvar: for i ∈ usedBvars body, (.cons x bv₁).get i = (.cons x bv₂).get i
        exact bvar_ext_cons tcInterp vt x (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ hb)
  | quant _ qk _ ty tr body ih_tr ih_body =>
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some qty =>
      have ⟨_, h_τ₁, h_tr₁, h_body₁⟩ := HasTypeA.quant_inv h₁
      have ⟨_, h_τ₂, h_tr₂, h_body₂⟩ := HasTypeA.quant_inv h₂
      subst h_τ₁; cases h_τ₂
      exact denote_quant_congr h_body₁ h_body₂ h₁ h₂ fun x =>
        ih_body
          (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
          (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
          (bvar_ext_cons tcInterp vt x (fun i τ' hi₁ hi₂ hb =>
            h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)))
          h_body₁ h_body₂

/-- For a closed expression (no free variables), the denotation is independent
of the free-variable valuation. -/
theorem denote_closed_fvarVal_irrel
    {e : LExpr T.mono} {τ : LMonoTy}
    {Δ : List LMonoTy}
    {fvarVal₁ fvarVal₂ : FreeVarVal T tcInterp}
    {bvarVal : BVarVal tcInterp vt Δ}
    (hclosed : e.closed = true)
    (h₁ : LExpr.HasTypeA Δ e τ)
    (h₂ : LExpr.HasTypeA Δ e τ)
    : LExpr.denote tcInterp opInterp fvarVal₁ vt bvarVal e τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal₂ vt bvarVal e τ h₂ := by
  have hfv : e.freeVars = [] := List.isEmpty_iff.mp hclosed
  apply denote_ext (opInterp₁ := opInterp) (opInterp₂ := opInterp)
    (bvarVal₁ := bvarVal) (bvarVal₂ := bvarVal)
  · intro o ty _; rfl
  · intro name ty hmem; exact absurd (hfv ▸ hmem : _ ∈ ([] : List _)) (by grind)
  · intro _ _ _ _ _; rfl

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

/-- Replacing metadata preserves denotation. -/
theorem denote_replaceMetadata
    {T : LExprParams} [Inhabited T.mono.base.IDMeta]
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    {e₁ : LExpr T.mono} {τ : LMonoTy} (f : T.Metadata → NewMetadata)
    (h₁ : LExpr.HasTypeA Δ e₁ τ):
    let T' : LExprParams := ⟨NewMetadata, T.IDMeta⟩
    let opInterp' : OpInterp tcInterp := opInterp
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

/-- If two expression lists have pointwise equal denotations at the same types,
then `denoteArgs` produces equal HLists. -/
theorem denoteArgs_eq_of_denote_eq
    {Δ : List LMonoTy}
    {args1 args2 : List (LExpr T.mono)}
    {argTys : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_args1 : List.Forall₂ (LExpr.HasTypeA Δ) args1 argTys)
    (h_args2 : List.Forall₂ (LExpr.HasTypeA Δ) args2 argTys)
    (hpw : ∀ (i : Nat) (a1 a2 : LExpr T.mono) (τ : LMonoTy),
      args1[i]? = some a1 → args2[i]? = some a2 → argTys[i]? = some τ →
      ∀ (ht1 : LExpr.HasTypeA Δ a1 τ) (ht2 : LExpr.HasTypeA Δ a2 τ),
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal a1 τ ht1 =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal a2 τ ht2)
    : denoteArgs tcInterp opInterp fvarVal vt bvarVal args1 argTys h_args1 =
      denoteArgs tcInterp opInterp fvarVal vt bvarVal args2 argTys h_args2 := by
  induction h_args1 generalizing args2 with
  | nil =>
    cases h_args2
    rfl
  | cons h1_head h1_tail ih =>
    cases h_args2 with
    | cons h2_head h2_tail =>
      simp only [denoteArgs]
      congr 1
      · exact hpw 0 _ _ _ (by simp) (by simp) (by simp) h1_head h2_head
      · exact ih h2_tail (fun i a1 a2 τ ha1 ha2 hτ ht1 ht2 =>
          hpw (i + 1) a1 a2 τ
            (by simp only [List.getElem?_cons_succ]; exact ha1)
            (by simp only [List.getElem?_cons_succ]; exact ha2)
            (by simp only [List.getElem?_cons_succ]; exact hτ)
            ht1 ht2)

/-- Reverse of `denoteArgs_eq_of_denote_eq`: if `denoteArgs` HLists are equal,
then pointwise denotations are equal. -/
theorem denoteArgs_eq_implies_denote_eq
    {Δ : List LMonoTy}
    {args₁ args₂ : List (LExpr T.mono)}
    {argTys : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_args₁ : List.Forall₂ (LExpr.HasTypeA Δ) args₁ argTys)
    (h_args₂ : List.Forall₂ (LExpr.HasTypeA Δ) args₂ argTys)
    (hdArgs : denoteArgs tcInterp opInterp fvarVal vt bvarVal args₁ argTys h_args₁ =
              denoteArgs tcInterp opInterp fvarVal vt bvarVal args₂ argTys h_args₂)
    : ∀ (i : Nat) (a₁ a₂ : LExpr T.mono) (σ : LMonoTy),
        args₁[i]? = some a₁ → args₂[i]? = some a₂ → argTys[i]? = some σ →
        (ha₁ : LExpr.HasTypeA Δ a₁ σ) → (ha₂ : LExpr.HasTypeA Δ a₂ σ) →
        LExpr.denote tcInterp opInterp fvarVal vt bvarVal a₁ σ ha₁ =
        LExpr.denote tcInterp opInterp fvarVal vt bvarVal a₂ σ ha₂ := by
  induction h_args₁ generalizing args₂ with
  | nil =>
    intro i a₁ a₂ σ ha₁
    simp at ha₁
  | cons h1_head h1_tail ih =>
    cases h_args₂ with
    | cons h2_head h2_tail =>
      simp only [denoteArgs] at hdArgs
      have hhead := HList.cons.inj hdArgs |>.1
      have htail := HList.cons.inj hdArgs |>.2
      intro i a₁ a₂ σ ha₁ ha₂ hσ hta₁ hta₂
      cases i with
      | zero =>
        simp at ha₁ ha₂ hσ
        cases ha₁; cases ha₂; cases hσ
        have h_eq₁ := HasTypeA_unique h1_head hta₁
        have h_eq₂ := HasTypeA_unique h2_head hta₂
        grind
      | succ n =>
        simp only [List.getElem?_cons_succ] at ha₁ ha₂ hσ
        exact ih h2_tail htail n a₁ a₂ σ ha₁ ha₂ hσ hta₁ hta₂

/-- `denote` is invariant under changing the type index by an equality proof. -/
theorem denote_cast_ty {Δ : List LMonoTy} {e : LExpr T.mono} {τ₁ τ₂ : LMonoTy}
    (h_eq : τ₁ = τ₂) (h₁ : LExpr.HasTypeA Δ e τ₁) (h₂ : LExpr.HasTypeA Δ e τ₂)
    (bv : BVarVal tcInterp vt Δ)
    : LExpr.denote tcInterp opInterp fvarVal vt bv e τ₁ h₁ =
      cast (congrArg (TyDenote tcInterp vt) h_eq.symm)
        (LExpr.denote tcInterp opInterp fvarVal vt bv e τ₂ h₂) := by
  subst h_eq; rfl

theorem denoteArgs_cast_ty {Δ : List LMonoTy} {l : List (LExpr T.mono)}
  {τ₁ τ₂ : List LMonoTy} (h_eq : τ₁ = τ₂)
  (h₁ : List.Forall₂ (LExpr.HasTypeA Δ) l τ₁)
  (h₂ : List.Forall₂ (LExpr.HasTypeA Δ) l τ₂)
    (bv : BVarVal tcInterp vt Δ)
    : denoteArgs tcInterp opInterp fvarVal vt bv l τ₁ h₁ =
      HList.cast (congrArg (List.map (Lambda.LMonoTy.substTyVars vt)) h_eq.symm)
        (denoteArgs tcInterp opInterp fvarVal vt bv l τ₂ h₂) := by
  subst h_eq; rfl

theorem applyArgs_cast_ty {args1 args2 : List LMonoTy} {ret1 ret2 : LMonoTy}
  (h_args: args1 = args2) (h_ret : ret1 = ret2)
  -- (s: SortDenote tcInterp (LSort.mkArrow ret1 args1))
  (h: HList (SortDenote tcInterp) (List.map (Lambda.LMonoTy.substTyVars vt) args1)):
  @SortDenote.applyArgs tcInterp  _ _
    (opInterp n ((Lambda.LMonoTy.substTyVars vt ret1).mkArrow
          (List.map (Lambda.LMonoTy.substTyVars vt) args1))) h =
  cast (congrArg (fun x => SortDenote tcInterp (Lambda.LMonoTy.substTyVars vt x)) h_ret.symm) (@SortDenote.applyArgs tcInterp  _ _
    (opInterp n ((Lambda.LMonoTy.substTyVars vt ret2).mkArrow
          (List.map (Lambda.LMonoTy.substTyVars vt) args2)))
    (HList.cast (congrArg (List.map (Lambda.LMonoTy.substTyVars vt)) h_args) h)) := by
  subst h_args h_ret; rfl

/-! ### fvars_annotated_by lemmas -/

section FvarsAnnotatedBy
variable [DecidableEq T.IDMeta]

/-- `fvars_annotated_by` transfers when `find?` on one map implies `find?` on another. -/
theorem fvars_annotated_by_of_find_sub
    (m₁ m₂ : Map T.Identifier LMonoTy) (e : LExpr T.mono)
    (h : ∀ k v, Map.find? m₁ k = some v → Map.find? m₂ k = some v)
    (h_annot : fvars_annotated_by m₂ e)
    : fvars_annotated_by m₁ e := by
  induction e with
  | fvar _ name ty =>
    cases ty with
    | none => exact h_annot
    | some t =>
      intro ty' h_find
      exact h_annot ty' (h name ty' h_find)
  | const | bvar | op => trivial
  | app _ _ _ ih_fn ih_arg => exact ⟨ih_fn h_annot.1, ih_arg h_annot.2⟩
  | abs _ _ _ _ ih => exact ih h_annot
  | ite _ _ _ _ ih_c ih_t ih_e =>
    exact ⟨ih_c h_annot.1, ih_t h_annot.2.1, ih_e h_annot.2.2⟩
  | eq _ _ _ ih1 ih2 => exact ⟨ih1 h_annot.1, ih2 h_annot.2⟩
  | quant _ _ _ _ _ _ ih_tr ih_body =>
    exact ⟨ih_tr h_annot.1, ih_body h_annot.2⟩

/-- If `fvars_annotated_by tyMap e` and `(name, some ty) ∈ e.freeVars` and
`tyMap.find? name = some ty'`, then `ty = ty'`. -/
theorem fvars_annotated_by_freeVars
    (tyMap : Map T.Identifier LMonoTy) (e : LExpr T.mono)
    (h_annot : fvars_annotated_by tyMap e)
    (name : T.Identifier) (ty ty' : LMonoTy)
    (h_fv : (name, some ty) ∈ e.freeVars)
    (h_find : Map.find? tyMap name = some ty')
    : ty = ty' := by
  induction e with
  | fvar _ x annot =>
    simp only [LExpr.freeVars] at h_fv
    simp only [List.mem_singleton] at h_fv
    obtain ⟨h_name_eq, h_annot_eq⟩ := Prod.mk.inj h_fv
    subst h_name_eq
    cases annot with
    | none => exact absurd h_annot (by simp [fvars_annotated_by])
    | some t =>
      simp at h_annot_eq; subst h_annot_eq
      exact h_annot ty' h_find
  | const => simp [LExpr.freeVars] at h_fv
  | bvar => simp [LExpr.freeVars] at h_fv
  | op => simp [LExpr.freeVars] at h_fv
  | app _ fn arg ih_fn ih_arg =>
    simp only [LExpr.freeVars, List.mem_append] at h_fv
    rcases h_fv with h_fn | h_arg
    · exact ih_fn h_annot.1 h_fn
    · exact ih_arg h_annot.2 h_arg
  | abs _ _ _ body ih =>
    exact ih h_annot h_fv
  | ite _ c t el ih_c ih_t ih_e =>
    simp only [LExpr.freeVars, List.mem_append] at h_fv
    rcases h_fv with (h_c | h_t) | h_el
    · exact ih_c h_annot.1 h_c
    · exact ih_t h_annot.2.1 h_t
    · exact ih_e h_annot.2.2 h_el
  | eq _ e1 e2 ih1 ih2 =>
    simp only [LExpr.freeVars, List.mem_append] at h_fv
    rcases h_fv with h_1 | h_2
    · exact ih1 h_annot.1 h_1
    · exact ih2 h_annot.2 h_2
  | quant _ _ _ _ tr body ih_tr ih_body =>
    simp only [LExpr.freeVars, List.mem_append] at h_fv
    rcases h_fv with h_tr | h_body
    · exact ih_tr h_annot.1 h_tr
    · exact ih_body h_annot.2 h_body

end FvarsAnnotatedBy
