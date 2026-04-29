/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

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

/-- Declarative typing rules for annotated expressions.

The first argument (`List LMonoTy`) is the typing context for bound variables,
ordered by De Bruijn indices: the head of the list is the type of the most
recently bound variable (index 0), the next element is the type of the
variable at index 1, and so on. -/
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

/-- Weakening: a locally closed expression well-typed in `[]` is well-typed in any `Δ`. -/
theorem HasTypeA_weaken {T : LExprParams}
    {e : LExpr T.mono} {τ : LMonoTy} {Δ : List LMonoTy}
    (h : LExpr.HasTypeA [] e τ) (hlc : LExpr.lcAt 0 e = true)
    : LExpr.HasTypeA Δ e τ := by
  rw [LExpr.HasTypeA_iff_typeCheck] at h ⊢
  rw [typeCheck_of_lcAt hlc]; exact h

/-- Substitution preserves typeCheck results. -/
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

/-! ### Inversion lemmas for `HasTypeA`

These extract subexpression types and typing proofs from a `HasTypeA` proof,
using the computable `typeCheck` function. They live in `Type` (not `Prop`)
so their results can be used in the definition of `denote`. -/

/-- From `HasTypeA Δ (.const m c) τ`, conclude `τ = c.ty`. -/
@[expose]
def HasTypeA.const_inv {T : LExprParams} {Δ : List LMonoTy} {m c τ}
    (h : @LExpr.HasTypeA T Δ (.const m c) τ) : τ = c.ty := by
  cases h; rfl

/-- From `HasTypeA Δ (.op m o (some ty)) τ`, conclude `τ = ty`. -/
@[expose]
def HasTypeA.op_inv {T : LExprParams} {Δ : List LMonoTy} {m o ty τ}
    (h : @LExpr.HasTypeA T Δ (.op m o (some ty)) τ) : τ = ty := by
  cases h; rfl

/-- From `HasTypeA Δ (.fvar m x (some ty)) τ`, conclude `τ = ty`. -/
@[expose]
def HasTypeA.fvar_inv {T : LExprParams} {Δ : List LMonoTy} {m x ty τ}
    (h : @LExpr.HasTypeA T Δ (.fvar m x (some ty)) τ) : τ = ty := by
  cases h; rfl

/-- From `HasTypeA Δ (.bvar m i) τ`, conclude `Δ[i]? = some τ`. -/
@[expose]
def HasTypeA.bvar_inv {T : LExprParams} {Δ : List LMonoTy} {m i τ}
    (h : @LExpr.HasTypeA T Δ (.bvar m i) τ) : Δ[i]? = some τ := by
  cases h; assumption

/-- From `HasTypeA Δ (.abs m name (some aty) body) τ`, extract the return type
and body typing proof. -/
@[expose]
def HasTypeA.abs_inv {T : LExprParams} {Δ : List LMonoTy} {m name aty body τ}
    (h : @LExpr.HasTypeA T Δ (.abs m name (some aty) body) τ)
    : Σ' rty, (τ = LMonoTy.arrow aty rty) ∧ LExpr.HasTypeA (aty :: Δ) body rty :=
  let tc := LExpr.typeCheck (aty :: Δ) body
  match h_tc : tc with
  | some rty =>
    ⟨rty,
     by have h' := LExpr.HasTypeA_to_typeCheck h
        unfold tc at *
        simp [LExpr.typeCheck, h_tc, Option.bind] at h'
        exact h'.symm,
     LExpr.typeCheck_to_HasTypeA h_tc⟩
  | none =>
    absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc at *
          simp [LExpr.typeCheck, h_tc, Option.bind])

/-- From `HasTypeA Δ (.app m fn arg) τ`, extract the domain type and
sub-proofs. -/
@[expose]
def HasTypeA.app_inv {T : LExprParams} {Δ : List LMonoTy} {m fn arg τ}
    (h : @LExpr.HasTypeA T Δ (.app m fn arg) τ)
    : Σ' aty, LExpr.HasTypeA Δ fn (LMonoTy.arrow aty τ) ∧ LExpr.HasTypeA Δ arg aty :=
  let tcFn := LExpr.typeCheck Δ fn
  let tcArg := LExpr.typeCheck Δ arg
  match h_fn : tcFn, h_arg : tcArg with
  | some fty, some aty =>
    match h_arr : fty.isArrow with
    | some (dom, cod) =>
      if h_eq : dom == aty then
        ⟨aty,
         by have h' := LExpr.HasTypeA_to_typeCheck h
            unfold tcFn tcArg at *
            have h_eq' : dom = aty := by grind
            simp [LExpr.typeCheck, h_fn, h_arg, h_arr, h_eq', Option.bind, guard] at h'
            subst h'
            have h_arrow := LMonoTy.isArrow_some h_arr; subst h_arrow
            subst_vars
            exact LExpr.typeCheck_to_HasTypeA h_fn,
         LExpr.typeCheck_to_HasTypeA h_arg⟩
      else absurd (LExpr.HasTypeA_to_typeCheck h)
        (by unfold tcFn tcArg at *
            have h_eq' : ¬ dom = aty := by grind
            simp [LExpr.typeCheck, h_fn, h_arg, h_arr, h_eq', Option.bind, guard])
    | none => absurd (LExpr.HasTypeA_to_typeCheck h)
        (by unfold tcFn tcArg at *
            simp [LExpr.typeCheck, h_fn, h_arg, h_arr, Option.bind])
  | some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcFn tcArg at *
          simp [LExpr.typeCheck, h_fn, h_arg, Option.bind])
  | none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcFn tcArg at *
          simp [LExpr.typeCheck, h_fn, Option.bind])

/-- From `HasTypeA Δ (.ite m c t e) τ`, extract sub-proofs for condition,
then-branch, and else-branch. -/
@[expose]
def HasTypeA.ite_inv {T : LExprParams} {Δ : List LMonoTy} {m c t e τ}
    (h : @LExpr.HasTypeA T Δ (.ite m c t e) τ)
    : LExpr.HasTypeA Δ c .bool ∧ LExpr.HasTypeA Δ t τ ∧ LExpr.HasTypeA Δ e τ :=
  let tcC := LExpr.typeCheck Δ c
  let tcT := LExpr.typeCheck Δ t
  let tcE := LExpr.typeCheck Δ e
  match h_c : tcC, h_t : tcT, h_e : tcE with
  | some cty, some tty, some ety =>
    if h_cb : cty == .bool then
      if h_te : tty == ety then
        have h' := LExpr.HasTypeA_to_typeCheck h
        have hcb : cty = .bool := by grind
        have hte : tty = ety := by grind
        have hτ : tty = τ := by
          subst_vars
          unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind, guard] at h'
          exact h'
        ⟨hcb ▸ LExpr.typeCheck_to_HasTypeA h_c,
         hτ ▸ LExpr.typeCheck_to_HasTypeA h_t,
         (Eq.trans (hte.symm) hτ) ▸ LExpr.typeCheck_to_HasTypeA h_e⟩
      else absurd (LExpr.HasTypeA_to_typeCheck h)
        (by unfold tcC tcT tcE at *
            have h_ne : ¬ tty = ety := by grind
            simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind, guard, h_ne]
            grind)
    else absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          have h_nb : ¬ cty = .bool := by grind
          simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind, guard, h_nb])
  | some _, some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind])
  | some _, none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, h_t, Option.bind])
  | none, _, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, Option.bind])

/-- From `HasTypeA Δ (.eq m e1 e2) τ`, extract the common type and
sub-proofs. -/
@[expose]
def HasTypeA.eq_inv {T : LExprParams} {Δ : List LMonoTy} {m e1 e2 τ}
    (h : @LExpr.HasTypeA T Δ (.eq m e1 e2) τ)
    : Σ' ty, (τ = .bool) ∧ LExpr.HasTypeA Δ e1 ty ∧ LExpr.HasTypeA Δ e2 ty :=
  let tc1 := LExpr.typeCheck Δ e1
  let tc2 := LExpr.typeCheck Δ e2
  match h_1 : tc1, h_2 : tc2 with
  | some ty1, some ty2 =>
    if h_eq : ty1 == ty2 then
      have heq : ty1 = ty2 := by grind
      ⟨ty1,
       by have h' := LExpr.HasTypeA_to_typeCheck h
          unfold tc1 tc2 at *
          simp [LExpr.typeCheck, h_1, h_2, Option.bind, guard, heq] at h'
          exact h'.symm,
       LExpr.typeCheck_to_HasTypeA h_1,
       heq ▸ LExpr.typeCheck_to_HasTypeA h_2⟩
    else absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc1 tc2 at *
          have h_ne : ¬ ty1 = ty2 := by grind
          simp [LExpr.typeCheck, h_1, h_2, Option.bind, guard, h_ne])
  | some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc1 tc2 at *
          simp [LExpr.typeCheck, h_1, h_2, Option.bind])
  | none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc1 tc2 at *
          simp [LExpr.typeCheck, h_1, Option.bind])

/-- From `HasTypeA Δ (.quant m k name (some qty) tr body) τ`, extract the
trigger type and sub-proofs. -/
@[expose]
def HasTypeA.quant_inv {T : LExprParams} {Δ : List LMonoTy} {m k name qty tr body τ}
    (h : @LExpr.HasTypeA T Δ (.quant m k name (some qty) tr body) τ)
    : Σ' τ_tr, (τ = .bool) ∧ LExpr.HasTypeA (qty :: Δ) tr τ_tr ∧
               LExpr.HasTypeA (qty :: Δ) body .bool :=
  let tcTr := LExpr.typeCheck (qty :: Δ) tr
  let tcBody := LExpr.typeCheck (qty :: Δ) body
  match h_tr : tcTr, h_body : tcBody with
  | some τ_tr, some bty =>
    if h_bb : bty == .bool then
      have hbb : bty = .bool := by grind
      ⟨τ_tr,
       by have h' := LExpr.HasTypeA_to_typeCheck h
          unfold tcTr tcBody at *
          simp [LExpr.typeCheck, h_tr, h_body, Option.bind, guard, hbb] at h'
          exact h'.symm,
       LExpr.typeCheck_to_HasTypeA h_tr,
       hbb ▸ LExpr.typeCheck_to_HasTypeA h_body⟩
    else absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcTr tcBody at *
          have h_nb : ¬ bty = .bool := by grind
          simp [LExpr.typeCheck, h_tr, h_body, Option.bind, guard, h_nb])
  | some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcTr tcBody at *
          simp [LExpr.typeCheck, h_tr, h_body, Option.bind])
  | none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcTr tcBody at *
          simp [LExpr.typeCheck, h_tr, Option.bind])

end -- public section

end Lambda
