/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Denote.HList

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

/-- Casting a dependent function application via `congrArg` is the same as
applying the function at the new index. -/
theorem cast_congrArg_dep_fn {α : Type} {F : α → Type} {a b : α}
    (h : a = b) (f : (x : α) → F x)
    : f b = cast (congrArg F h) (f a) := by subst h; rfl

/-- Combining `cast` with `▸` on a round trip is the identity. -/
theorem cast_subst_roundtrip {α : Type} {F : α → Sort _} {a b : α}
    (h_eq : a = b) (h_td : F a = F b) (x : F b)
    : cast h_td (h_eq.symm ▸ x) = x := by
  subst h_eq; rfl

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
  cases c <;> simp [denoteConst, LConst.ty, TyDenote, LMonoTy.substTyVars] at h ⊢ <;> exact h ▸ rfl

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
    have : τ' = a := by simpa using hi₁.symm
    subst this
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
    · rw [denote_eq_true _ h_1₁ h_2₁ h₁ heq, denote_eq_true _ h_1₂ h_2₂ h₂
            (by rw [← ih1 (fun o ty ho => h_op o ty (List.mem_append_left _ ho))
                        (fun n ty hf => h_fvar n ty (List.mem_append_left _ hf))
                        (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ hb)) h_1₁ h_1₂,
                    ← ih2 (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
                        (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
                        (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)) h_2₁ h_2₂]; exact heq)]
    · rw [denote_eq_false _ h_1₁ h_2₁ h₁ heq, denote_eq_false _ h_1₂ h_2₂ h₂
            (by rw [← ih1 (fun o ty ho => h_op o ty (List.mem_append_left _ ho))
                        (fun n ty hf => h_fvar n ty (List.mem_append_left _ hf))
                        (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_left _ hb)) h_1₁ h_1₂,
                    ← ih2 (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
                        (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
                        (fun i τ' hi₁ hi₂ hb => h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)) h_2₁ h_2₂]; exact heq)]
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
      cases qk with
      | all =>
        by_cases hall : ∀ x : TyDenote tcInterp vt qty,
            (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body .bool h_body₁ : Bool) = true
        · rw [denote_quant_all_true _ h_body₁ h₁ hall]
          symm; apply denote_quant_all_true _ h_body₂ h₂; intro x
          rw [← ih_body
            (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
            (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
            (bvar_ext_cons tcInterp vt x (fun i τ' hi₁ hi₂ hb =>
              h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)))
            h_body₁ h_body₂]
          exact hall x
        · have ⟨w, hw⟩ := Classical.not_forall.mp hall
          have hwf : (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons w bvarVal₁) body .bool h_body₁ : Bool) = false :=
            Bool.eq_false_iff.mpr hw
          rw [denote_quant_all_false _ h_body₁ h₁ w hwf]
          symm; apply denote_quant_all_false _ h_body₂ h₂ w
          rw [← ih_body
            (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
            (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
            (bvar_ext_cons tcInterp vt w (fun i τ' hi₁ hi₂ hb =>
              h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)))
            h_body₁ h_body₂]
          exact hwf
      | exist =>
        by_cases hexist : ∃ x : TyDenote tcInterp vt qty,
            (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body .bool h_body₁ : Bool) = true
        · obtain ⟨w, hw⟩ := hexist
          rw [denote_quant_exist_true _ h_body₁ h₁ w hw]
          symm; apply denote_quant_exist_true _ h_body₂ h₂ w
          rw [← ih_body
            (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
            (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
            (bvar_ext_cons tcInterp vt w (fun i τ' hi₁ hi₂ hb =>
              h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)))
            h_body₁ h_body₂]
          exact hw
        · have hexist_f : ∀ x : TyDenote tcInterp vt qty,
              (LExpr.denote tcInterp opInterp₁ fvarVal₁ vt (.cons x bvarVal₁) body .bool h_body₁ : Bool) = false :=
            fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
          rw [denote_quant_exist_false _ h_body₁ h₁ hexist_f]
          symm; apply denote_quant_exist_false _ h_body₂ h₂; intro x
          rw [← ih_body
            (fun o ty ho => h_op o ty (List.mem_append_right _ ho))
            (fun n ty hf => h_fvar n ty (List.mem_append_right _ hf))
            (bvar_ext_cons tcInterp vt x (fun i τ' hi₁ hi₂ hb =>
              h_bvar i τ' hi₁ hi₂ (List.mem_append_right _ hb)))
            h_body₁ h_body₂]
          exact hexist_f x

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
private theorem denote_cast_ty {Δ : List LMonoTy} {e : LExpr T.mono} {τ₁ τ₂ : LMonoTy}
    (h_eq : τ₁ = τ₂) (h₁ : LExpr.HasTypeA Δ e τ₁) (h₂ : LExpr.HasTypeA Δ e τ₂)
    (bv : BVarVal tcInterp vt Δ)
    : LExpr.denote tcInterp opInterp fvarVal vt bv e τ₁ h₁ =
      cast (congrArg (TyDenote tcInterp vt) h_eq.symm)
        (LExpr.denote tcInterp opInterp fvarVal vt bv e τ₂ h₂) := by
  subst h_eq; rfl
