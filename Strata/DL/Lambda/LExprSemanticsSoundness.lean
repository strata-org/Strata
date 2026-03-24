/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprAnnotated
import all Strata.DL.Lambda.LExprDenote
import all Strata.DL.Lambda.Semantics

namespace Lambda

variable {T : LExprParams} [DecidableEq T.Metadata] [DecidableEq T.Identifier]
    [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp T tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### HList cast infrastructure -/

/-- Cast an `HList` along a proof that the index lists are equal. -/
def HList.cast {α : Type} {f : α → Type} {xs ys : List α}
    (h : xs = ys) (hlist : HList f xs) : HList f ys :=
  h ▸ hlist

@[simp] theorem HList.cast_rfl {α : Type} {f : α → Type} {xs : List α}
    (hlist : HList f xs) : HList.cast rfl hlist = hlist := rfl

@[simp] theorem HList.cast_cast {α : Type} {f : α → Type} {xs ys zs : List α}
    (h₁ : xs = ys) (h₂ : ys = zs) (hlist : HList f xs)
    : HList.cast h₂ (HList.cast h₁ hlist) = HList.cast (h₁.trans h₂) hlist := by
  subst h₁; subst h₂; rfl

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

/-! ### Helper lemmas -/

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- `callOfLFunc` only returns functions that are members of the factory. -/
theorem Factory.callOfLFunc_mem {F : @Factory T} {e : LExpr T.mono} {callee args fn} :
    F.callOfLFunc e = some (callee, args, fn) → fn ∈ F := by
  simp [Factory.callOfLFunc]
  cases getLFuncCall e with | mk op args' =>
  simp; cases op <;> simp
  rename_i m name ty
  cases h : F.getFactoryLFunc name.name <;> simp
  rename_i func
  cases args'.length == func.inputs.length <;> simp
  intro _ _ h_fn; subst h_fn
  exact Array.mem_of_find?_eq_some h

/-! ### HasTypeA implies lcAt -/

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- Well-typed expressions have all bound variables within the context. -/
theorem HasTypeA_lcAt {e : LExpr T.mono} {Δ : List LMonoTy} {τ : LMonoTy}
    (h : LExpr.HasTypeA Δ e τ) : LExpr.lcAt Δ.length e = true := by
  induction h with
  | const => simp [LExpr.lcAt]
  | op => simp [LExpr.lcAt]
  | fvar => simp [LExpr.lcAt]
  | bvar hlookup => simp [LExpr.lcAt]; grind
  | abs _ ih => simp [LExpr.lcAt, ih] at *
  | quant _ _ ih_tr ih_body => simp [LExpr.lcAt, ih_tr, ih_body] at *
  | app _ _ ih_fn ih_arg => simp [LExpr.lcAt, ih_fn, ih_arg]
  | ite _ _ _ ih_c ih_t ih_e => simp [LExpr.lcAt, ih_c, ih_t, ih_e]
  | eq _ _ ih1 ih2 => simp [LExpr.lcAt, ih1, ih2]

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- Well-typed in the empty context implies locally closed. -/
theorem HasTypeA_nil_lcAt {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] e τ) : LExpr.lcAt 0 e = true :=
  HasTypeA_lcAt h

/-! ### Weakening and context-irrelevance for lcAt 0 expressions -/

/-! ### HList infrastructure for context splitting -/

/-- Append two HLists. -/
def HList.append {α : Type} {f : α → Type} {xs ys : List α}
    : HList f xs → HList f ys → HList f (xs ++ ys)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (HList.append xs ys)

/-- Get from an appended HList at index < |xs| returns the same as get from xs. -/
theorem HList.get_append_left {f : α → Type} {xs ys : List α} {a : α}
    (hxs : HList f xs) (hys : HList f ys)
    (i : Nat) (h : (xs ++ ys)[i]? = some a) (h' : xs[i]? = some a)
    : HList.get (HList.append hxs hys) i h = HList.get hxs i h' := by
  induction hxs generalizing i with
  | nil => simp at h'
  | cons x xs ih =>
    cases i with
    | zero => simp [HList.append, HList.get] at *
    | succ n => simp [HList.append, HList.get] at *; simp at h h'; exact ih n h h'

/-- Get from (xs ++ cons v ys) at index |xs| returns v. -/
theorem HList.get_append_cons_self {f : α → Type} {xs : List α} {a : α} {ys : List α}
    (hxs : HList f xs) (v : f a) (hys : HList f ys)
    (h : (xs ++ a :: ys)[xs.length]? = some a)
    : HList.get (HList.append hxs (.cons v hys)) xs.length h = v := by
  induction hxs with
  | nil => simp [HList.append, HList.get]
  | cons x xs' ih => simp [HList.append, HList.get] at *; exact ih trivial

/-! ### Unfolding lemma for bvar -/

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- Unfolding lemma for `denote` of a bound variable. -/
theorem denote_bvar
    {m : T.mono.base.Metadata} {i : Nat} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.bvar m i) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.bvar m i) τ h =
      bvarVal.get i (HasTypeA.bvar_inv h) := by rfl

/-! ### typeCheck context irrelevance for lcAt expressions -/

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- typeCheck depends only on the first k context entries for lcAt k expressions. -/
theorem typeCheck_of_lcAt_aux
    {e : LExpr T.mono} {k : Nat} {Δ Δ' : List LMonoTy}
    (hlc : LExpr.lcAt k e = true)
    (hagree : ∀ i, i < k → Δ[i]? = Δ'[i]?)
    : LExpr.typeCheck Δ e = LExpr.typeCheck Δ' e := by
  induction e generalizing k Δ Δ' with
  | const => rfl
  | op m o ty => cases ty <;> rfl
  | fvar m name ty => cases ty <;> rfl
  | bvar m i =>
    simp only [LExpr.typeCheck]
    simp [LExpr.lcAt] at hlc
    exact hagree i hlc
  | app m fn arg ih_fn ih_arg =>
    simp [LExpr.lcAt] at hlc
    simp only [LExpr.typeCheck]
    rw [ih_fn hlc.1 hagree, ih_arg hlc.2 hagree]
  | ite m c t e ih_c ih_t ih_e =>
    simp [LExpr.lcAt] at hlc
    simp only [LExpr.typeCheck]
    rw [ih_c hlc.1.1 hagree, ih_t hlc.1.2 hagree, ih_e hlc.2 hagree]
  | eq m e1 e2 ih1 ih2 =>
    simp [LExpr.lcAt] at hlc
    simp only [LExpr.typeCheck]
    rw [ih1 hlc.1 hagree, ih2 hlc.2 hagree]
  | abs m name ty body ih =>
    cases ty with
    | none => simp [LExpr.typeCheck]
    | some aty' =>
      simp [LExpr.lcAt] at hlc
      simp only [LExpr.typeCheck]
      rw [@ih _ (aty' :: Δ) (aty' :: Δ') hlc]
      grind
  | quant m qk name qty tr body ih_tr ih_body =>
    cases qty with
    | none => simp [LExpr.typeCheck]
    | some qty' =>
      simp [LExpr.lcAt] at hlc
      simp only [LExpr.typeCheck]
      have hagree' : ∀ i, i < k + 1 → (qty' :: Δ)[i]? = (qty' :: Δ')[i]? := fun i hi => by
        cases i with
        | zero => rfl
        | succ j => simp [List.getElem?_cons_succ]; exact hagree j (by omega)
      rw [ih_tr hlc.1 hagree', ih_body hlc.2 hagree']

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- typeCheck is independent of context for closed terms (lcAt 0). -/
theorem typeCheck_of_lcAt
    {e : LExpr T.mono} {Δ' : List LMonoTy}
    (hlc : LExpr.lcAt 0 e = true)
    : LExpr.typeCheck Δ' e = LExpr.typeCheck [] e :=
  typeCheck_of_lcAt_aux hlc (by omega)

/-! ### Denotation irrelevance for locally closed expressions -/

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
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

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
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

/-! ### Generalized substK_denote -/

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- Substitution preserves typeCheck results. -/
theorem substK_typeCheck
    {e : LExpr T.mono} {v : LExpr T.mono}
    {aty : LMonoTy} {Δ₁ : List LMonoTy}
    (h_v : LExpr.HasTypeA [] v aty)
    : LExpr.typeCheck Δ₁ (LExpr.substK Δ₁.length (fun _ => v) e) =
      LExpr.typeCheck (Δ₁ ++ [aty]) e := by
  induction e generalizing Δ₁ with
  | const => rfl
  | op m o ty => cases ty <;> rfl
  | fvar m name ty => cases ty <;> rfl
  | bvar m i =>
    simp only [LExpr.substK, LExpr.typeCheck]
    by_cases h : i == Δ₁.length
    · have hi : i = Δ₁.length := by grind
      subst hi; simp
      rw [typeCheck_of_lcAt (HasTypeA_nil_lcAt h_v),
          LExpr.HasTypeA_to_typeCheck h_v]
    · simp [h]
      have hi : i ≠ Δ₁.length := by grind
      by_cases hlt : i < Δ₁.length
      · simp[LExpr.typeCheck]
        grind
      · have hge : i ≥ Δ₁.length + 1 := by omega
        simp [List.getElem?_append_right (by omega : Δ₁.length ≤ i)]
        simp[LExpr.typeCheck]
        grind
  | abs m name ty body ih =>
    cases ty with
    | none => simp [LExpr.substK, LExpr.typeCheck]
    | some aty' =>
      simp only [LExpr.substK, LExpr.typeCheck]
      have h_len : (aty' :: Δ₁).length = Δ₁.length + 1 := by grind
      rw [show LExpr.typeCheck (aty' :: Δ₁) (LExpr.substK (Δ₁.length + 1) (fun x => v) body)
            = LExpr.typeCheck (aty' :: (Δ₁ ++ [aty])) body from by rw [← h_len, ih]; simp [List.cons_append]]
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substK, LExpr.typeCheck]
    rw [ih_fn, ih_arg]
  | ite m c t e ih_c ih_t ih_e =>
    simp only [LExpr.substK, LExpr.typeCheck]
    rw [ih_c, ih_t, ih_e]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substK, LExpr.typeCheck]
    rw [ih1, ih2]
  | quant m qk name qty tr body ih_tr ih_body =>
    cases qty with
    | none => simp [LExpr.substK, LExpr.typeCheck]
    | some qty' =>
      simp only [LExpr.substK, LExpr.typeCheck]
      have h_len : (qty' :: Δ₁).length = Δ₁.length + 1 := by grind
      rw [show LExpr.typeCheck (qty' :: Δ₁) (LExpr.substK (Δ₁.length + 1) (fun x => v) tr)
            = LExpr.typeCheck (qty' :: (Δ₁ ++ [aty])) tr from by rw [← h_len, ih_tr]; simp [List.cons_append],
          show LExpr.typeCheck (qty' :: Δ₁) (LExpr.substK (Δ₁.length + 1) (fun x => v) body)
            = LExpr.typeCheck (qty' :: (Δ₁ ++ [aty])) body from by rw [← h_len, ih_body]; simp [List.cons_append]]

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

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
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
    -- substK doesn't change const. Both sides denote to denoteConst c.
    have h1 := HasTypeA.const_inv h_subst  -- τ = c.ty
    have h2 := HasTypeA.const_inv h_body   -- τ = c.ty
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
    · -- i = |Δ₁|: substK returns v
      rename_i h_eq
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
    · -- i ≠ |Δ₁|
      rename_i h_ne
      simp [LExpr.substK, h_ne] at h_subst
      rw [denote_bvar tcInterp opInterp fvarVal vt bvarVal₁ h_subst,
          denote_bvar tcInterp opInterp fvarVal vt _ h_body]
      exact (HList.get_append_left bvarVal₁ _ i (HasTypeA.bvar_inv h_body) (HasTypeA.bvar_inv h_subst)).symm
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substK] at h_subst ⊢
    let ⟨aty_b, h_fn_b, h_arg_b⟩ := HasTypeA.app_inv h_body
    let ⟨aty_s, h_fn_s, h_arg_s⟩ := HasTypeA.app_inv h_subst
    -- Need aty_s = aty_b to apply IH uniformly
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

omit [DecidableEq
  T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
/-- Bound-variable substitution commutes with denotation: the denotation of
`subst (fun _ => v) body` in the empty bvar context equals the denotation of
`body` in context `[aty]` with bvar 0 mapped to `denote v`.

Requires `v` to be locally closed (no bound variables), which is always the
case when `v` is well-typed in the empty context. -/
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

/-- Free-variable substitution commutes with denotation: the denotation of
`substFvars body bindings` equals the denotation of `body` with `fvarVal`
updated to map each substituted name to the denotation of its replacement. -/
theorem substFvars_denote
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

/-! ### Metadata Doesn't Affect Typing or Denotations -/

-- Easier to prove by computation than via HasTypeA directly
omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta] in
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

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta]  [Inhabited T.mono.base.IDMeta]in
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

-- omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] in
-- theorem eql_rewrite
--   {F : @Factory T}
--   {e₁ e₂ : LExpr T.mono}
--   (hv₁ : LExpr.isCanonicalValue F e₁)
--   (hv₂ : LExpr.isCanonicalValue F e₂):
--   LExpr.eql F e₁ e₂ hv₁ hv₂ = LExpr.eqModuloTypes e₁ e₂ := by
--   unfold LExpr.eql; split <;> grind
omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] in
theorem eqModuloMeta_true_implies_denote_eq
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eqModuloMeta e₁ e₂ = true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
    unfold LExpr.eqModuloMeta at heql
    -- Lean is confused by BEq and DecidableEq
    have heq: (e₁.eraseMetadata = e₂.eraseMetadata) := by
      unfold BEq.beq instBEqLExprOfIdentifier at heql
      simp at heql
      rw[LExpr.beq_eq] at heql
      exact heql
    rw[denote_replaceMetadata _ _ _ _ .nil (fun _ => ()) h₁]
    rw[denote_replaceMetadata _ _ _ _ .nil (fun _ => ()) h₂]
    unfold LExpr.eraseMetadata at heq
    generalize replaceMetadata_HasTypeA (fun _ => ()) h₁ = ht₁
    generalize e₁.replaceMetadata (fun _ => ()) = e₁' at *
    subst heq
    rfl


omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] in
/-- For canonical values, if syntactic equality (`eql`) returns true, then the
denotations are equal. -/
theorem eql_true_implies_denote_eq
    {F : @Factory T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eql F e₁ e₂ = some true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
    sorry

/-- For binder-free canonical values, if syntactic equality (`eql`) returns
false, then the denotations are not equal. The `containsBinder = false`
precondition is essential: for expressions with binders, structural inequality
does not imply semantic inequality (e.g., `λ (if #true then %0 else %0)` vs
`λ %0`). -/
theorem eql_false_implies_denote_ne
    {F : @Factory T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eql F e₁ e₂ = some false)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ ≠
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  sorry

/-- If `callOfLFunc F e = some (callee, args, fn)` and `e : τ` and `F` is
well-typed, then `τ = fn.output`. -/
theorem callOfLFunc_output_type
    {F : @Factory T}
    {e : LExpr T.mono} {τ : LMonoTy}
    {callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hFwt : Factory.WellTyped F)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    (h : LExpr.HasTypeA [] e τ)
    : τ = fn.output := by
  sorry

/-- If `callOfLFunc F e = some (callee, args, fn)` and `e` is well-typed, then
the denotation of `e` equals `opInterp fn.name` applied to the denotations of
`args`. -/
theorem callOfLFunc_denote
    {F : @Factory T}
    {e : LExpr T.mono} {τ : LMonoTy}
    {callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    (h : LExpr.HasTypeA [] e τ)
    : ∃ (h_args : List.Forall₂ (LExpr.HasTypeA []) args (List.map Prod.snd fn.inputs)),
      let inputSorts := (List.map Prod.snd fn.inputs).map (LMonoTy.substTyVars vt)
      let fullSort := LSort.mkArrow (LMonoTy.substTyVars vt τ) inputSorts
      LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h =
        SortDenote.applyArgs tcInterp (opInterp fn.name fullSort)
          (denoteArgs tcInterp opInterp fvarVal vt h_args) := by
  sorry


/-! ### Main theorem -/

/-- If `e₁` steps to `e₂` under a factory `F` and environment `env`, and both
are well-typed at the same type `τ`, then (given consistency of the factory and
environment with the semantic interpretations) they have the same denotation. -/
theorem Step.denote_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hFwt : Factory.WellTyped F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  induction hstep generalizing τ with
  | expand_fvar x e henv =>
    cases h₁ with
    | fvar => simp [LExpr.denote]; exact (hEnv vt x _ _ henv h₂).symm
  | beta e1 v2 eres hval heq =>
    subst heq
    cases h₁
    rename_i aty htyv2 htyabs
    cases htyabs with
    | abs =>
      rename_i h_body
      rw [denote_app .nil (.abs h_body) htyv2,
          denote_abs .nil h_body]
      exact (subst_denote tcInterp opInterp fvarVal vt h_body htyv2 h₂
              (HasTypeA_nil_lcAt htyv2)).symm
  | reduce_2 v1 e2 e2' hstep' ih =>
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        have haty := HasTypeA_unique h_fn h_fn'
        cases haty
        rw [denote_app .nil h_fn h_arg,
            denote_app .nil h_fn' h_arg']
        congr 1
        rw[ih h_arg h_arg']
  | reduce_1 e1 e1' e2 hstep' ih =>
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        have haty := HasTypeA_unique h_arg h_arg'
        subst haty
        rw [denote_app .nil h_fn h_arg,
            denote_app .nil h_fn' h_arg']
        congr 1
        rw[ih h_fn h_fn']
  | ite_reduce_then ethen eelse =>
    cases h₁ with
    | ite h_c h_t h_e =>
      rw [denote_ite .nil h_c h_t h_e]
      have hc: LExpr.denote tcInterp opInterp fvarVal vt .nil
          (.const _ (.boolConst true)) .bool h_c = true := by rfl
      rw [hc]; rfl
  | ite_reduce_else ethen eelse =>
    cases h₁ with
    | ite h_c h_t h_e =>
      rw [denote_ite .nil h_c h_t h_e]
      have hc : LExpr.denote tcInterp opInterp fvarVal vt .nil
          (.const _ (.boolConst false)) .bool h_c = false := by rfl
      rw [hc]; rfl
  | ite_reduce_cond econd econd' ethen eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_c h_c']
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_t h_t']
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_e h_e']
  | eq_reduce_true e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_true .nil h_1 h_2 _
          (eql_true_implies_denote_eq tcInterp opInterp fvarVal vt h_1 h_2 heql)]
      rfl
  | eq_reduce_false e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_false .nil h_1 h_2 _
          (eql_false_implies_denote_ne tcInterp opInterp fvarVal vt
            h_1 h_2 heql)]
      rfl
  | eq_reduce_lhs e1 e1' e2 hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_2 h_2'; subst hty
        have ih_eq := ih h_1 h_1'
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil e1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | eq_reduce_rhs v1 e2 e2' hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_1 h_1'; subst hty
        have ih_eq := ih h_2 h_2'
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | expand_fn e callee fnbody new_body args fn hcall hbody heq =>
    subst heq
    obtain ⟨h_args, h_denote_e⟩ := callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    have h_tau : τ = fn.output := callOfLFunc_output_type hFwt hcall h₁
    subst h_tau
    have hfn_in : fn ∈ F := Factory.callOfLFunc_mem hcall
    have h_body_ty : LExpr.HasTypeA [] fnbody fn.output := hFwt fn hfn_in fnbody hbody
    have h_map_eq : (List.map Prod.snd fn.inputs).map (LMonoTy.substTyVars vt) =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).map Prod.snd := by
      simp [List.map_map, Function.comp]
    -- Transport denoteArgs to the InterpConsistentBody index
    let args' : HList (SortDenote tcInterp)
        ((fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).map Prod.snd) :=
      HList.cast h_map_eq (denoteArgs tcInterp opInterp fvarVal vt h_args)
    have h_consistent := hF.1 fn hfn_in fnbody hbody vt fvarVal h_body_ty args'
    have h_arity : args.length = fn.inputs.length := by
      have := h_args.length_eq; simp at this; exact this
    have h_keys : (fn.inputs.keys.zip args).map Prod.fst =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).map Prod.fst := by
      rw [ListMap.keys_eq_map_fst,
          List.map_fst_zip (l₁ := fn.inputs.map Prod.fst) (l₂ := args) (by simp; omega),
          List.map_map]; rfl
    have h_len : (fn.inputs.keys.zip args).length =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).length := by
      simp [ListMap.keys_eq_map_fst, List.length_zip, h_arity]
    have h_subst := substFvars_denote tcInterp opInterp fvarVal vt
        (sortBindings := fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty)))
        h_body_ty h₂ args' h_keys h_len
    rw [h_denote_e, ← h_subst]
    -- Goal: applyArgs (opInterp fn.name (mkArrow ret xs)) (denoteArgs h_args)
    --     = denote (withArgs ...) fnbody
    -- h_consistent: applyArgs (opInterp fn.name (mkArrow ret ys)) args' = same RHS
    -- Use applyArgs_cast_eq to rewrite LHS, replacing (denoteArgs h_args) with args'
    rw [SortDenote.applyArgs_cast_eq tcInterp h_map_eq (opInterp fn.name)
        (denoteArgs tcInterp opInterp fvarVal vt h_args)]
    exact h_consistent
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    have h_tau := callOfLFunc_output_type hFwt hcall h₁; subst h_tau
    obtain ⟨h_args, h_denote_e⟩ := callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    have hfn_in : fn ∈ F := Factory.callOfLFunc_mem hcall
    rename_i m
    have h_consistent := hF.2 fn hfn_in denotefn heval vt fvarVal m args e'
        hresult.symm h_args h₂
    rw [h_denote_e, ← h_consistent]

/-- A single step preserves well-typedness. -/
theorem Step.type_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    : LExpr.HasTypeA [] e₂ τ := by
  sorry

/-- Multi-step version: if `e₁` reduces to `e₂` in zero or more steps, and
both are well-typed at `τ`, they have the same denotation. -/
theorem StepStar.denote_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hsteps : StepStar F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  sorry

end Lambda
