/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenoteSubst

/-! # Beta reduction keeps the annotated typing

Lifting the bound variables of an expression past inserted binders keeps its annotated typing
(`HasTypeA`) in the extended context (`HasTypeA_liftBVars`); substituting, for a bound variable,
an expression of its type keeps the typing (`HasTypeA_betaReduceK`); hence contracting the
redexes of an expression keeps its typing (`HasTypeA_betaReduceRedexesFuel`,
`HasTypeA_betaReduceRedexes`).

Key theorems: `Lambda.LExpr.HasTypeA_betaReduceRedexes`. -/

public section

namespace Lambda.LExpr

variable {T : LExprParams}

/-- Lifting the bound variables at or above `Δa.length` by `Δn.length` types an expression of
    `Δa ++ Δc` in the context with `Δn` inserted after `Δa`. -/
private theorem HasTypeA_liftBVars {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) : ∀ (Δa Δc Δn : List LMonoTy), Δ = Δa ++ Δc →
      (liftBVars Δn.length e Δa.length).HasTypeA (Δa ++ Δn ++ Δc) τ := by
  rintro Δa Δc Δn rfl
  rw [HasTypeA_iff_typeCheck] at h ⊢
  rwa [liftBVars_typeCheck]

/-- The root metadata does not affect the annotated typing. -/
private theorem HasTypeA_replaceMetadata1 {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (m : T.mono.base.Metadata) (h : e.HasTypeA Δ τ) :
    (replaceMetadata1 m e).HasTypeA Δ τ := by
  cases h <;> simp only [replaceMetadata1] <;> constructor <;> assumption

/-- Substituting, for the bound variable `Δa.length` of an expression of `Δa ++ aty :: Δ`,
    expressions of `aty` in `Δ` (lifted past `Δa`) types the result in `Δa ++ Δ`. -/
private theorem HasTypeA_betaReduceK {s : T.mono.base.Metadata → LExpr T.mono}
    {Δ : List LMonoTy} {aty : LMonoTy}
    (ha : ∀ m, (s m).HasTypeA Δ aty) {Γ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Γ τ) : ∀ (Δa : List LMonoTy), Γ = Δa ++ aty :: Δ →
      (betaReduceK Δa.length s e).HasTypeA (Δa ++ Δ) τ := by
  induction h with
  | const | op | fvar => intros; constructor <;> assumption
  | @bvar Γ i t m hi =>
    rintro Δa rfl
    simp only [betaReduceK]
    split
    · rename_i hik
      obtain rfl : i = Δa.length := by simpa using hik
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simpa using HasTypeA_liftBVars (ha m) [] Δ Δa rfl
    · split <;> refine .bvar ?_
      · rw [List.getElem?_append_right (by omega)] at hi ⊢
        rw [show i - Δa.length = (i - 1 - Δa.length) + 1 by omega] at hi
        simpa using hi
      · rw [List.getElem?_append_left (by simp_all; omega)] at hi ⊢
        exact hi
  | abs _ ih => exact fun Δa hΓ => .abs (ih (_ :: Δa) (hΓ ▸ rfl))
  | quant _ _ ih1 ih2 =>
    exact fun Δa hΓ => .quant (ih1 (_ :: Δa) (hΓ ▸ rfl)) (ih2 (_ :: Δa) (hΓ ▸ rfl))
  | app _ _ ih1 ih2 => exact fun Δa hΓ => .app (ih1 Δa hΓ) (ih2 Δa hΓ)
  | ite _ _ _ ih1 ih2 ih3 => exact fun Δa hΓ => .ite (ih1 Δa hΓ) (ih2 Δa hΓ) (ih3 Δa hΓ)
  | eq _ _ ih1 ih2 => exact fun Δa hΓ => .eq (ih1 Δa hΓ) (ih2 Δa hΓ)

/-- **Contracting redexes keeps the annotated typing**, at any fuel. -/
private theorem HasTypeA_betaReduceRedexesFuel
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata)
    (keep : Bool) (fuel : Nat) :
    ∀ {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}, e.HasTypeA Δ τ →
      (betaReduceRedexesFuel merge keep fuel e).HasTypeA Δ τ := by
  induction fuel with
  | zero => intro Δ e τ h; simpa [betaReduceRedexesFuel, betaReduceRedexesFuel?] using h
  | succ fuel ih =>
    simp only [betaReduceRedexesFuel] at ih
    intro Δ e τ h
    cases h with
    | const | op | fvar | bvar => constructor <;> assumption
    | abs hb =>
      simp only [betaReduceRedexesFuel, betaReduceRedexesFuel?]
      cases hbv : betaReduceRedexesFuel? merge keep fuel _ with
      | none => exact .abs hb
      | some b' => simpa [hbv] using HasTypeA.abs (by simpa [hbv] using ih hb)
    | quant h1 h2 =>
      simp only [betaReduceRedexesFuel, betaReduceRedexesFuel?]
      split <;> first | exact .quant h1 h2 | exact .quant (ih h1) (ih h2)
    | ite h1 h2 h3 =>
      simp only [betaReduceRedexesFuel, betaReduceRedexesFuel?]
      split <;> first | exact .ite h1 h2 h3 | exact .ite (ih h1) (ih h2) (ih h3)
    | eq h1 h2 =>
      simp only [betaReduceRedexesFuel, betaReduceRedexesFuel?]
      split <;> first | exact .eq h1 h2 | exact .eq (ih h1) (ih h2)
    | app hf ha =>
      simp only [betaReduceRedexesFuel, betaReduceRedexesFuel?]
      have hf' := ih hf
      have ha' := ih ha
      split
      · rename_i mAbs n t body hfn
        rw [hfn] at hf'
        cases hf' with
        | abs hb =>
          split
          · split <;> first | exact .app hf ha | exact .app (hfn ▸ ih hf) ha'
          · exact ih (by
              simpa [betaReduce, betaReduceWith] using
                HasTypeA_betaReduceK (fun _ => HasTypeA_replaceMetadata1 _ ha') hb [] rfl)
      · split <;> first | exact .app hf ha | exact .app hf' ha'


/-- **Contracting redexes keeps the annotated typing.** -/
theorem HasTypeA_betaReduceRedexes {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) : (betaReduceRedexes e).HasTypeA Δ τ :=
  HasTypeA_betaReduceRedexesFuel keepArgMetadata false _ h

/-- **Contracting redexes under a metadata combinator keeps the annotated typing**: the
    metadata each substituted copy carries does not affect its typing. -/
theorem HasTypeA_betaReduceRedexesWith
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata)
    {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) : (betaReduceRedexesWith merge e).HasTypeA Δ τ :=
  HasTypeA_betaReduceRedexesFuel merge false _ h

end Lambda.LExpr

end -- public section
