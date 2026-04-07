/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import all Strata.DL.Lambda.LExprEval

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

section
variable [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

/-! ## `eqModuloMeta` soundness -/

theorem eqModuloMeta_true_implies_denote_eq
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eqModuloMeta e₁ e₂ = true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
    unfold LExpr.eqModuloMeta at heql
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

/-! ## `denoteConst` injectivity -/

/-- For non-real constants of the same type, `denoteConst` is injective:
distinct constants of the same type have distinct denotations. -/
theorem denoteConst_injective
    (c1 c2 : LConst)
    (hty : c1.ty = c2.ty)
    (heq : (hty ▸ denoteConst tcInterp vt c1 : TyDenote tcInterp vt c2.ty) =
            denoteConst tcInterp vt c2)
    : c1 = c2 := by
  sorry

/-! ## `eqlCombine` helpers -/

/-- If folding `eqlCombine` over pairs returns `some true`, then every
individual `eql` call returned `some true`. -/
theorem eqlCombine_all_true
    {F : @Factory T}
    {pairs : List (LExpr T.mono × LExpr T.mono)}
    (h : pairs.foldl (fun acc (p : LExpr T.mono × LExpr T.mono) =>
      LExpr.eqlCombine acc (LExpr.eql F p.1 p.2)) (some true) = some true)
    : ∀ p ∈ pairs, LExpr.eql F p.1 p.2 = some true := by
  sorry

/-- If folding `eqlCombine` over pairs returns `some false`, then some
individual `eql` call returned `some false`. -/
theorem eqlCombine_some_false
    {F : @Factory T}
    {pairs : List (LExpr T.mono × LExpr T.mono)}
    (h : pairs.foldl (fun acc (p : LExpr T.mono × LExpr T.mono) =>
      LExpr.eqlCombine acc (LExpr.eql F p.1 p.2)) (some true) = some false)
    : ∃ p ∈ pairs, LExpr.eql F p.1 p.2 = some false := by
  sorry

/-! ## Main `eql` soundness theorems -/

/-- If `eql` returns `some true`, then the denotations are equal.
Generalized to arbitrary context `Δ` and `bvarVal` for the induction to
go through (the lambda/varOpen case recurses at the same context). -/
theorem eql_true_implies_denote_eq
    {F : @Factory T}
    {Δ : List LMonoTy}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h₁ : LExpr.HasTypeA Δ e₁ τ)
    (h₂ : LExpr.HasTypeA Δ e₂ τ)
    (heql : LExpr.eql F e₁ e₂ = some true)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₂ τ h₂ := by
    sorry

/-- If `eql` returns `some false`, then the denotations are not equal.
Generalized to arbitrary context `Δ` and `bvarVal` for the induction. -/
theorem eql_false_implies_denote_ne
    {F : @Factory T}
    {Δ : List LMonoTy}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h₁ : LExpr.HasTypeA Δ e₁ τ)
    (h₂ : LExpr.HasTypeA Δ e₂ τ)
    (heql : LExpr.eql F e₁ e₂ = some false)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₁ τ h₁ ≠
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₂ τ h₂ := by
  sorry

end

end Lambda
