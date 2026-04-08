/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF

/-! ## Type Checking for Annotated Lambda Expressions

`LExpr.typeCheck` returns `some τ` when the expression is well-typed with type
`τ`, and `none` otherwise. `HasTypeA` is the corresponding inductive typing
relation, and the two are proved equivalent.
-/

namespace Lambda

open LExpr

public section

/-- Return `some (dom, cod)` if the type is an arrow, `none` otherwise. -/
def LMonoTy.isArrow : LMonoTy → Option (LMonoTy × LMonoTy)
  | .tcons "arrow" [dom, cod] => some (dom, cod)
  | _ => none

@[simp] theorem LMonoTy.isArrow_arrow (t1 t2 : LMonoTy) :
    (LMonoTy.arrow t1 t2).isArrow = some (t1, t2) := by
  simp [LMonoTy.arrow, isArrow]

theorem LMonoTy.isArrow_some {t t1 t2 : LMonoTy} :
    t.isArrow = some (t1, t2) → t = .arrow t1 t2 := by
  simp [LMonoTy.arrow, isArrow]
  cases t <;> grind

/-- Typecheck an annotated `LExpr`, returning `some τ` if well-typed, `none`
otherwise. `ctx` maps de Bruijn indices to their types from enclosing
binders. -/
@[expose]
def LExpr.typeCheck {T : LExprParams} (ctx : List LMonoTy) : LExpr T.mono → Option LMonoTy
  | .const _ c => some c.ty
  | .op _ _ (some ty) => some ty
  | .op _ _ none => none
  | .fvar _ _ (some ty) => some ty
  | .fvar _ _ none => none
  | .bvar _ i => ctx[i]?
  | .abs _ _ (some aty) body => do
    let rty ← typeCheck (aty :: ctx) body
    some (.arrow aty rty)
  | .abs _ _ none _ => none
  | .quant _ _ _ (some qty) tr body => do
    let _ ← typeCheck (qty :: ctx) tr
    let bty ← typeCheck (qty :: ctx) body
    guard (bty == .bool)
    some .bool
  | .quant _ _ _ none _ _ => none
  | .app _ fn arg => do
    let fty ← typeCheck ctx fn
    let aty ← typeCheck ctx arg
    let (dom, cod) ← fty.isArrow
    guard (dom == aty)
    some cod
  | .ite _ c t e => do
    let cty ← typeCheck ctx c
    let tty ← typeCheck ctx t
    let ety ← typeCheck ctx e
    guard (cty == .bool)
    guard (tty == ety)
    some tty
  | .eq _ e1 e2 => do
    let ty1 ← typeCheck ctx e1
    let ty2 ← typeCheck ctx e2
    guard (ty1 == ty2)
    some .bool

/-- Declarative typing rules for annotated expressions. -/
inductive LExpr.HasTypeA {T : LExprParams} : List LMonoTy → LExpr T.mono → LMonoTy → Prop where
  | const : HasTypeA Δ (.const m c) c.ty
  | op    : HasTypeA Δ (.op m o (some ty)) ty
  | fvar  : HasTypeA Δ (.fvar m x (some ty)) ty
  | bvar  : Δ[i]? = some t → HasTypeA Δ (.bvar m i) t
  | abs   : HasTypeA (aty :: Δ) body rty →
            HasTypeA Δ (.abs m name (some aty) body) (.arrow aty rty)
  | quant : HasTypeA (qty :: Δ) tr τ_tr →
            HasTypeA (qty :: Δ) body .bool →
            HasTypeA Δ (.quant m k name (some qty) tr body) .bool
  | app   : HasTypeA Δ fn (.arrow aty rty) →
            HasTypeA Δ arg aty →
            HasTypeA Δ (.app m fn arg) rty
  | ite   : HasTypeA Δ c .bool →
            HasTypeA Δ t τ →
            HasTypeA Δ e τ →
            HasTypeA Δ (.ite m c t e) τ
  | eq    : HasTypeA Δ e1 τ →
            HasTypeA Δ e2 τ →
            HasTypeA Δ (.eq m e1 e2) .bool

theorem LExpr.HasTypeA_to_typeCheck {T : LExprParams} {Δ : List LMonoTy}
    {e : LExpr T.mono} {τ : LMonoTy}
    (h : HasTypeA Δ e τ) : typeCheck Δ e = some τ := by
  induction h with
  | const => simp [typeCheck]
  | op => simp [typeCheck]
  | fvar => simp [typeCheck]
  | bvar hlookup => simp [typeCheck, hlookup]
  | abs _ ih => simp [typeCheck, ih, bind, Option.bind, LMonoTy.arrow]
  | quant _ _ ihtr ihbody =>
    simp [typeCheck, ihtr, ihbody, bind, Option.bind, guard]
  | app _ _ ihfn iharg =>
    simp [typeCheck, ihfn, iharg, bind, Option.bind, guard]
  | ite _ _ _ ihc iht ihe =>
    simp [typeCheck, ihc, iht, ihe, bind, Option.bind, guard]
  | eq _ _ ih1 ih2 =>
    simp [typeCheck, ih1, ih2, bind, Option.bind, guard]

theorem LExpr.typeCheck_to_HasTypeA {T : LExprParams} {Δ : List LMonoTy}
    {e : LExpr T.mono} {τ : LMonoTy}
    (h : typeCheck Δ e = some τ) : HasTypeA Δ e τ := by
  induction e generalizing Δ τ with
  | const _ c => simp [typeCheck] at h; subst h; exact .const
  | op _ _ ty =>
    cases ty with
    | some t => simp [typeCheck] at h; subst h; exact .op
    | none => simp [typeCheck] at h
  | fvar _ _ ty =>
    cases ty with
    | some t => simp [typeCheck] at h; subst h; exact .fvar
    | none => simp [typeCheck] at h
  | bvar _ i => simp [typeCheck] at h; exact .bvar h
  | abs _ _ ty body ih =>
    cases ty with
    | some aty =>
      simp [typeCheck, bind, Option.bind] at h
      split at h <;> simp_all
      rename_i rty heq; subst h
      show HasTypeA _ _ (.arrow aty rty)
      exact .abs (ih heq)
    | none => simp [typeCheck] at h
  | quant _ _ _ ty tr body ihtr ihbody =>
    cases ty with
    | some qty =>
      simp [typeCheck, bind, Option.bind, guard] at h
      split at h <;> simp_all
      rename_i τ_tr htr
      split at h <;> simp_all
      rename_i bty hbody
      split at h <;> simp_all
      subst_vars
      exact .quant (ihtr htr) (ihbody hbody)
    | none => simp [typeCheck] at h
  | app _ fn arg ihfn iharg =>
    simp [typeCheck, bind, Option.bind] at h
    split at h <;> simp_all
    rename_i fty hfn
    split at h <;> simp_all
    rename_i aty' harg
    split at h <;> simp_all
    rename_i arrow
    have := LMonoTy.isArrow_some arrow
    subst_vars
    simp [guard] at h
    split at h <;> simp_all
    subst_vars
    exact .app (ihfn hfn) (iharg harg)
  | ite _ c t e ihc iht ihe =>
    simp [typeCheck, bind, Option.bind, guard] at h
    split at h <;> simp_all
    rename_i cty hc
    split at h <;> simp_all
    rename_i tty ht
    split at h <;> simp_all
    rename_i ety he
    split at h <;> simp_all
    split at h <;> simp_all
    subst_vars
    exact .ite (ihc hc) (iht ht) (ihe he)
  | eq _ e1 e2 ih1 ih2 =>
    simp [typeCheck, bind, Option.bind, guard] at h
    split at h <;> simp_all
    rename_i ty1 h1
    split at h <;> simp_all
    rename_i ty2 h2
    split at h <;> simp_all
    subst_vars
    exact .eq (ih1 h1) (ih2 h2)

theorem LExpr.HasTypeA_iff_typeCheck {T : LExprParams} (Δ : List LMonoTy)
    (e : LExpr T.mono) (τ : LMonoTy) :
    HasTypeA Δ e τ ↔ typeCheck Δ e = some τ :=
  ⟨HasTypeA_to_typeCheck, typeCheck_to_HasTypeA⟩

theorem HasTypeA_unique {T : LExprParams} {Δ : List LMonoTy} {e : LExpr T.mono} {τ₁ τ₂ : LMonoTy}
    (h₁ : LExpr.HasTypeA Δ e τ₁) (h₂ : LExpr.HasTypeA Δ e τ₂) : τ₁ = τ₂ := by
  have := LExpr.HasTypeA_to_typeCheck h₁
  have := LExpr.HasTypeA_to_typeCheck h₂
  simp_all

/-! ### HasTypeA implies lcAt -/

/-- Well-typed expressions have all bound variables within the context. -/
theorem HasTypeA_lcAt {T : LExprParams} {e : LExpr T.mono} {Δ : List LMonoTy} {τ : LMonoTy}
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

/-- Well-typed in the empty context implies locally closed. -/
theorem HasTypeA_nil_lcAt {T : LExprParams} {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] e τ) : LExpr.lcAt 0 e = true :=
  HasTypeA_lcAt h

/-! ### typeCheck context irrelevance for lcAt expressions -/

/-- typeCheck depends only on the first k context entries for lcAt k expressions. -/
theorem typeCheck_of_lcAt_aux {T : LExprParams}
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

/-- typeCheck is independent of context for closed terms (lcAt 0). -/
theorem typeCheck_of_lcAt {T : LExprParams}
    {e : LExpr T.mono} {Δ' : List LMonoTy}
    (hlc : LExpr.lcAt 0 e = true)
    : LExpr.typeCheck Δ' e = LExpr.typeCheck [] e :=
  typeCheck_of_lcAt_aux hlc (by omega)

/-- Substitution preserves typeCheck results. Generalized to an arbitrary
substitution function `s` (not just a constant one) so that `varOpen`
(which uses metadata-dependent `fun m => fvar m x ty`) is covered. -/
theorem substK_typeCheck {T : LExprParams}
    {e : LExpr T.mono} {s : T.mono.base.Metadata → LExpr T.mono}
    {aty : LMonoTy} {Δ₁ : List LMonoTy}
    (h_s : ∀ m, LExpr.HasTypeA [] (s m) aty)
    : LExpr.typeCheck Δ₁ (LExpr.substK Δ₁.length s e) =
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
      rw [typeCheck_of_lcAt (HasTypeA_nil_lcAt (h_s m)),
          LExpr.HasTypeA_to_typeCheck (h_s m)]
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
      rw [show LExpr.typeCheck (aty' :: Δ₁) (LExpr.substK (Δ₁.length + 1) s body)
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
      rw [show LExpr.typeCheck (qty' :: Δ₁) (LExpr.substK (Δ₁.length + 1) s tr)
            = LExpr.typeCheck (qty' :: (Δ₁ ++ [aty])) tr from by rw [← h_len, ih_tr]; simp [List.cons_append],
          show LExpr.typeCheck (qty' :: Δ₁) (LExpr.substK (Δ₁.length + 1) s body)
            = LExpr.typeCheck (qty' :: (Δ₁ ++ [aty])) body from by rw [← h_len, ih_body]; simp [List.cons_append]]

/-- `varOpen 0` preserves typing: if `body` types in `[aty]`, then
`varOpen 0 (x, some aty) body` types in `[]`. -/
theorem varOpen_HasTypeA {T : LExprParams}
    {body : LExpr T.mono} {x : Identifier T.IDMeta}
    {aty τ : LMonoTy}
    (h : LExpr.HasTypeA [aty] body τ)
    : LExpr.HasTypeA [] (LExpr.varOpen 0 (x, some aty) body) τ := by
  unfold LExpr.varOpen
  apply LExpr.typeCheck_to_HasTypeA
  have h_eq := @substK_typeCheck T body (fun m => .fvar m x (some aty)) aty []
    (fun m => LExpr.typeCheck_to_HasTypeA (by simp [LExpr.typeCheck]))
  simp only [List.length_nil, List.nil_append] at h_eq
  rw [h_eq]
  exact LExpr.HasTypeA_to_typeCheck h

end -- public section

end Lambda
