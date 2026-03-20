/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExpr

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

end -- public section

end Lambda
