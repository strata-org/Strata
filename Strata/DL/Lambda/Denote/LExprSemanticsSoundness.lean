/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.Denote.HList
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### Helper lemmas -/

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

/-! ### Weakening and context-irrelevance for lcAt 0 expressions -/

-- omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] in
-- theorem eql_rewrite
--   {F : @Factory T}
--   {e₁ e₂ : LExpr T.mono}
--   (hv₁ : LExpr.isCanonicalValue F e₁)
--   (hv₂ : LExpr.isCanonicalValue F e₂):
--   LExpr.eql F e₁ e₂ hv₁ hv₂ = LExpr.eqModuloTypes e₁ e₂ := by
--   unfold LExpr.eql; split <;> grind
section -- [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
variable [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

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

theorem zip_map_fst_eq {α β: Type} (l1: List α) (l2: List β) :
  List.length l1 = List.length l2 →
  (l1.zip l2).map Prod.fst = l1 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp_all

theorem zip_map_snd_eq{α β: Type} (l1: List α) (l2: List β) :
  List.length l1 = List.length l2 →
  (l1.zip l2).map Prod.snd = l2 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp_all


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
    (hOps : OpsConsistent F e₁)
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
        rw[ih h_arg h_arg' hOps.2]
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
        rw[ih h_fn h_fn' hOps.1]
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
        rw [ih h_c h_c' hOps.1]
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_t h_t' hOps.2.1]
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_e h_e' hOps.2.2]
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
        have ih_eq := ih h_1 h_1' hOps.1
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
        have ih_eq := ih h_2 h_2' hOps.2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | expand_fn e callee fnbody new_body args fn hcall hbody heq =>
    sorry
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    sorry

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

end -- section [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

end Lambda
