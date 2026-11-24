/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.LExprWFProps

/-!
## Substituting expressions holding the values

Key theorem: `LExpr.denoteEval_substFvarsBy_of_denoteEval` — substituting, for free variables
of `e`, expressions whose values are the variables' values preserves evaluation.
-/

namespace Lambda

public section

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-- **Substitution law for expressions.**  Substituting, for each substituted free variable `x`
of `e`, an expression `r` that evaluates in `σ'` to `x`'s value in `σ` (`x` bound in `σ`)
preserves evaluation, when the remaining free variables have the same values. -/
theorem LExpr.denoteEval_substFvarsBy_of_denoteEval {M : ModeledFactory T} {σ σ' : ValStore T}
    (look : Identifier T.IDMeta → Option (LExpr T.mono)) (e : LExpr T.mono)
    (hlook : ∀ x ty r, (x, ty) ∈ e.freeVars → look x = some r →
      (σ x).isSome ∧ r.denoteEval M σ' = σ x)
    (hrest : ∀ x ty, (x, ty) ∈ e.freeVars → look x = none → σ' x = σ x) :
    (e.substFvarsBy look).denoteEval M σ' = e.denoteEval M σ := by
  have hval : ∀ x ty r, (x, ty) ∈ e.freeVars → look x = some r →
      ∃ w, σ x = some w ∧ r.denoteEval M σ' = some w := fun x ty r hx hl =>
    (hlook x ty r hx hl).elim fun hs hr =>
      (Option.isSome_iff_exists.1 hs).imp fun _ hw => ⟨hw, hr.trans hw⟩
  have hdef : σ'.Defines M.model.tcInterp (e.substFvarsBy look) ↔ σ.Defines M.model.tcInterp e := by
    simp only [ValStore.Defines, getVars_eq_freeVars_idents, List.mem_map, Prod.exists,
      exists_and_right, exists_eq_right, forall_exists_index]
    refine ⟨fun hd x ty hx => ?_, fun hd x ty hx => ?_⟩
    · cases hl : look x with
      | none => exact hrest x ty hx hl ▸ hd x ty ((LExpr.mem_freeVars_substFvarsBy_of hx).1 hl)
      | some r => exact (hval x ty r hx hl).elim fun w ⟨hw, hr⟩ => ⟨w, hw, LExpr.denoteEval_tc hr⟩
    · rcases LExpr.mem_freeVars_substFvarsBy hx with ⟨hx', hl⟩ | ⟨y, tyy, r, hy, hl, hr⟩
      · exact hrest x ty hx' hl ▸ hd x ty hx'
      · obtain ⟨w, -, hrw⟩ := hval y tyy r hy hl
        exact LExpr.denoteEval_defines hrw x
          (getVars_eq_freeVars_idents r ▸ List.mem_map.2 ⟨_, hr, rfl⟩)
  refine Option.ext fun v => ?_
  rw [LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff, hdef]
  refine and_congr_right fun _ => ?_
  let look' : Identifier T.IDMeta → Option (LExpr T.mono) :=
    fun x => (look x).map (·.annotateFvars σ'.ann)
  have hann :
      (e.substFvarsBy look).annotateFvars σ'.ann = (e.annotateFvars σ.ann).substFvarsBy look' :=
    LExpr.annotateFvars_substFvarsBy look σ.ann σ'.ann e fun x ty hx hl => by
      simp [ValStore.ann, hrest x ty hx hl]
  letI := M.model.allInhabited
  have hheq : ∀ {e₁ e₂ : LExpr T.mono} {τ} (he : e₁ = e₂) (h₁ : e₁.HasTypeA [] τ)
      (h₂ : e₂.HasTypeA [] τ), HEq (LExpr.denote M.model.tcInterp M.model.opInterp
        (σ'.fvarVal M.model.tcInterp) M.tyVarVal .nil e₁ τ h₁) (LExpr.denote M.model.tcInterp
          M.model.opInterp (σ'.fvarVal M.model.tcInterp) M.tyVarVal .nil e₂ τ h₂) :=
    fun he _ _ => by subst he; rfl
  have hocc : ∀ x tyo r', (x, tyo) ∈ (e.annotateFvars σ.ann).freeVars → look' x = some r' →
      ∃ τ, ∃ h0 : r'.HasTypeA [] τ, tyo = some τ ∧ σ x = some ⟨M.model.tcInterp,
        τ.substTyVars M.tyVarVal, LExpr.denote M.model.tcInterp M.model.opInterp
          (σ'.fvarVal M.model.tcInterp) M.tyVarVal .nil r' τ h0⟩ := by
    intro x tyo r' hx hl'
    obtain ⟨⟨ty', hx'⟩, hann'⟩ := LExpr.mem_freeVars_annotateFvars hx
    obtain ⟨r, hl, rfl⟩ := Option.map_eq_some_iff.1 hl'
    obtain ⟨w, hw, hr⟩ := hval x ty' r hx' hl
    obtain ⟨-, τ, h0, hg, rfl⟩ := LExpr.denoteEval_eq_some_iff.1 hr
    have hτ : (τ.substTyVars M.tyVarVal).toMonoTy = τ := hg.substTyVars_eq _ refTyVarVal ▸ hg
    exact ⟨τ, h0, hann' τ (by simp [ValStore.ann, hw, LExpr.denoteEvalResult, hτ]), hw⟩
  have htc : ∀ x tyo r', (x, tyo) ∈ (e.annotateFvars σ.ann).freeVars → look' x = some r' →
      ∀ Δ', LExpr.typeCheck Δ' r' = tyo := by
    intro x tyo r' hx hl Δ'
    obtain ⟨τ, h0, rfl, -⟩ := hocc x tyo r' hx hl
    rw [typeCheck_of_lcAt (HasTypeA_nil_lcAt h0)]
    exact LExpr.HasTypeA_to_typeCheck h0
  have htyeq : LExpr.typeCheck [] ((e.substFvarsBy look).annotateFvars σ'.ann) =
      LExpr.typeCheck [] (e.annotateFvars σ.ann) :=
    hann ▸ LExpr.typeCheck_substFvarsBy look' _ [] htc
  have hden : ∀ x ty r', (x, some ty) ∈ (e.annotateFvars σ.ann).freeVars → look' x = some r' →
      ∀ Δ' (bv' : BVarVal M.model.tcInterp M.tyVarVal Δ') (hr : r'.HasTypeA Δ' ty),
        LExpr.denote M.model.tcInterp M.model.opInterp (σ'.fvarVal M.model.tcInterp) M.tyVarVal
          bv' r' ty hr = σ.fvarVal M.model.tcInterp x (ty.substTyVars M.tyVarVal) := by
    intro x ty r' hx hl Δ' bv' hr
    obtain ⟨τ, h0, hty, hw⟩ := hocc x _ r' hx hl
    cases hty
    rw [denote_irrel_of_lcAt _ _ _ _ (HasTypeA_nil_lcAt h0) hr h0 bv' .nil]
    simp [ValStore.fvarVal, hw, SemValue.read]
  have hfv : ∀ x ty, (x, some ty) ∈ (e.annotateFvars σ.ann).freeVars → look' x = none →
      σ'.fvarVal M.model.tcInterp x (ty.substTyVars M.tyVarVal) =
        σ.fvarVal M.model.tcInterp x (ty.substTyVars M.tyVarVal) := by
    intro x ty hx hl
    obtain ⟨⟨ty', hx'⟩, -⟩ := LExpr.mem_freeVars_annotateFvars hx
    simp [ValStore.fvarVal, hrest x ty' hx' (Option.map_eq_none_iff.1 hl)]
  constructor
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : (e.annotateFvars σ.ann).HasTypeA [] τ := LExpr.typeCheck_to_HasTypeA
      (htyeq ▸ LExpr.HasTypeA_to_typeCheck hτ)
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    exact eq_of_heq ((hheq hann hτ (LExpr.HasTypeA_substFvarsBy htc hτ')).trans
      (heq_of_eq (denote_substFvarsBy look' .nil htc hden hfv hτ' _)))
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : ((e.substFvarsBy look).annotateFvars σ'.ann).HasTypeA [] τ :=
      LExpr.typeCheck_to_HasTypeA (htyeq.symm ▸ LExpr.HasTypeA_to_typeCheck hτ)
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    exact (eq_of_heq ((hheq hann hτ' (LExpr.HasTypeA_substFvarsBy htc hτ)).trans
      (heq_of_eq (denote_substFvarsBy look' .nil htc hden hfv hτ _)))).symm


end -- public section

end Lambda
