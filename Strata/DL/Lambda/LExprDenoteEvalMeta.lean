/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Denote.LExprDenoteEq
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps

/-!
## Denotational evaluation ignores expression metadata

Two expressions equal up to metadata (`LExpr.eqModuloMeta`) evaluate alike in every store.

- `LExpr.annotateFvars_replaceMetadata` — annotating free variables commutes with replacing
  metadata
- `LExpr.eqModuloMeta_iff` — equality up to metadata is equality of the metadata-erased forms
- `LExpr.denoteEval_eqModuloMeta` — expressions equal up to metadata have the same value
-/

namespace Lambda

public section

variable {T : LExprParams}

/-- Annotating the free variables of `e` and then replacing its metadata by `f` gives the
    expression obtained by replacing the metadata first. -/
theorem LExpr.annotateFvars_replaceMetadata {NewMetadata : Type}
    (ann : Identifier T.IDMeta → Option LMonoTy) (e : LExpr T.mono)
    (f : T.Metadata → NewMetadata) :
    (e.annotateFvars ann).replaceMetadata f =
      LExpr.annotateFvars (T := ⟨NewMetadata, T.IDMeta⟩) ann (e.replaceMetadata f) := by
  induction e <;> simp_all [LExpr.annotateFvars, LExpr.replaceMetadata]

variable [DecidableEq T.IDMeta] [Inhabited T.IDMeta]

omit [Inhabited T.IDMeta] in
/-- Two expressions are equal up to metadata exactly when their metadata-erased forms are equal. -/
theorem LExpr.eqModuloMeta_iff {e₁ e₂ : LExpr T.mono} :
    LExpr.eqModuloMeta e₁ e₂ = true ↔ e₁.eraseMetadata = e₂.eraseMetadata := by
  unfold LExpr.eqModuloMeta BEq.beq instBEqLExprOfIdentifier
  simp only
  exact LExpr.beq_eq _ _

/-- Expressions equal up to metadata evaluate to the same value, or both fail to evaluate,
    in every store. -/
theorem LExpr.denoteEval_eqModuloMeta {M : ModeledFactory T} {σ : ValStore T}
    {e₁ e₂ : LExpr T.mono} (h : LExpr.eqModuloMeta e₁ e₂ = true) :
    e₁.denoteEval M σ = e₂.denoteEval M σ := by
  have heq : e₁.eraseMetadata = e₂.eraseMetadata := LExpr.eqModuloMeta_iff.1 h
  have hvars : LExpr.LExpr.getVars e₁ = LExpr.LExpr.getVars e₂ := by
    rw [getVars_eq_freeVars_idents, getVars_eq_freeVars_idents,
      freeVars_of_eraseMetadata_eq e₁ e₂ heq]
  have hann :
      (e₁.annotateFvars σ.ann).eraseMetadata = (e₂.annotateFvars σ.ann).eraseMetadata := by
    unfold LExpr.eraseMetadata at heq ⊢
    rw [LExpr.annotateFvars_replaceMetadata, LExpr.annotateFvars_replaceMetadata, heq]
  have hty : ∀ τ,
      (e₁.annotateFvars σ.ann).HasTypeA [] τ ↔ (e₂.annotateFvars σ.ann).HasTypeA [] τ := by
    intro τ
    rw [LExpr.HasTypeA_iff_typeCheck, LExpr.HasTypeA_iff_typeCheck,
      replaceMetadata_typeCheck (fun _ => ()),
      replaceMetadata_typeCheck (e := e₂.annotateFvars _) (fun _ => ())]
    unfold LExpr.eraseMetadata at hann
    rw [hann]
  have hval : ∀ τ h₁ h₂, e₁.denoteEvalResult M σ τ h₁ = e₂.denoteEvalResult M σ τ h₂ := by
    intro τ h₁ h₂
    unfold LExpr.denoteEvalResult
    congr 1
    exact eqModuloMeta_true_implies_denote_eq _ _ _ _ .nil h₁ h₂ (LExpr.eqModuloMeta_iff.2 hann)
  refine Option.ext fun v => ?_
  rw [
LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff, ValStore.Defines,
    ValStore.Defines, hvars]
  exact and_congr_right fun _ =>
    ⟨fun ⟨τ, h₁, hg, hv⟩ => ⟨τ, (hty τ).1 h₁, hg, hv.trans (hval τ h₁ _)⟩,
      fun ⟨τ, h₂, hg, hv⟩ => ⟨τ, (hty τ).2 h₂, hg, hv.trans (hval τ _ h₂).symm⟩⟩



end -- public section

end Lambda
