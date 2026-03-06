/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Subst

/-! ## Declarative Typing Rules for Hindley-Milner -/

namespace HM

def constTy : Const → Ty
  | .bool _ => .bool
  | .int _  => .int

inductive HasType : Ctx → Expr → Scheme → Prop where
  | fvar  : Γ.vars.find? x = some σ →
            HasType Γ (.fvar x) σ

  | op    : Γ.ops.find? f = some σ →
            HasType Γ (.op f) σ

  | const : HasType Γ (.const c) (Scheme.mono (constTy c))

  | abs   : Expr.fresh x e →
            Scheme.isMono σ_x →
            Scheme.isMono σ_body →
            HasType (Γ.addVar x σ_x) (Expr.varOpen 0 x e) σ_body →
            HasType Γ (.abs e) (Scheme.mono (Ty.arrow σ_x.body σ_body.body))

  | app   : Scheme.isMono σ₁ →
            Scheme.isMono σ₂ →
            HasType Γ e₁ (Scheme.mono (Ty.arrow σ₂.body σ₁.body)) →
            HasType Γ e₂ σ₂ →
            HasType Γ (.app e₁ e₂) σ₁

  | ite   : HasType Γ c (Scheme.mono Ty.bool) →
            HasType Γ t σ →
            HasType Γ f σ →
            HasType Γ (.ite c t f) σ

  | eq    : HasType Γ e₁ σ →
            HasType Γ e₂ σ →
            HasType Γ (.eq e₁ e₂) (Scheme.mono Ty.bool)

  | quant : Expr.fresh x e →
            Scheme.isMono σ_x →
            HasType (Γ.addVar x σ_x) (Expr.varOpen 0 x e) (Scheme.mono Ty.bool) →
            HasType Γ (.quant k e) (Scheme.mono Ty.bool)

  | inst  : HasType Γ e σ →
            σ' = Scheme.open α τ σ →
            HasType Γ e σ'

  | gen   : HasType Γ e σ →
            α ∉ Scheme.freeVarsCtx Γ →
            α ∈ σ.freeVars →
            HasType Γ e (σ.close α)

end HM
