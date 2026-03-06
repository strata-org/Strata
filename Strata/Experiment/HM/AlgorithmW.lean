/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Subst
import Strata.Experiment.HM.Unify

/-! ## Algorithm W for Hindley-Milner -/

namespace HM

/-- Instantiate a scheme by replacing each bound var with a fresh type variable.
    Returns the resulting monotype and the updated counter. -/
def Scheme.instantiate (σ : Scheme) (n : Nat) : Ty × Nat :=
  let S : Subst := σ.vars.mapIdx fun i α => (α, Ty.var (n + i))
  (S.apply σ.body, n + σ.vars.length)

/-- Fresh term variable name from counter. -/
def freshVar (n : Nat) : String := s!"_w{n}"

/-- Algorithm W: infer a type for `e` in context `Γ`, returning
    `(S, ae, n')` where `S` is the accumulated substitution,
    `ae` is the annotated expression, and `n'` is the updated counter. -/
def W (Γ : Ctx) (e : Expr) (n : Nat) : Except String (Subst × AExpr × Nat) :=
  match e with
  | .fvar x => do
    let σ ← Γ.vars.find? x |>.elim (.error s!"unbound variable: {x}") .ok
    let (τ, n₁) := σ.instantiate n
    .ok (Subst.id, .fvar τ x, n₁)

  | .op f => do
    let σ ← Γ.ops.find? f |>.elim (.error s!"unknown operator: {f}") .ok
    let (τ, n₁) := σ.instantiate n
    .ok (Subst.id, .op τ f, n₁)

  | .const c =>
    .ok (Subst.id, .const c, n)

  | .abs body => do
    let α := Ty.var n
    let x := body.freshFor
    let (S₁, ae₁, n₁) ← W (Γ.addVar x (.mono α)) (body.varOpen 0 x) (n + 1)
    let arrTy := Ty.arrow (S₁.apply α) ae₁.tyOf
    .ok (S₁, .abs arrTy (ae₁.varClose 0 x), n₁)

  | .app e₁ e₂ => do
    let (S₁, ae₁, n₁) ← W Γ e₁ n
    let (S₂, ae₂, n₂) ← W (S₁.applyCtx Γ) e₂ n₁
    let α := Ty.var n₂
    let S₃ ← unify (S₂.apply ae₁.tyOf) (.arrow ae₂.tyOf α)
    let fnTy := S₃.apply (S₂.apply ae₁.tyOf)
    let argTy := S₃.apply ae₂.tyOf
    .ok (S₃.compose (S₂.compose S₁),
         .app fnTy argTy (S₃.applyAExpr (S₂.applyAExpr ae₁)) (S₃.applyAExpr ae₂),
         n₂ + 1)

  | .ite c t f => do
    let (S₁, aec, n₁) ← W Γ c n
    let S₂ ← unify aec.tyOf .bool
    let (S₃, aet, n₂) ← W ((S₂.compose S₁).applyCtx Γ) t n₁
    let (S₄, aef, n₃) ← W ((S₃.compose (S₂.compose S₁)).applyCtx Γ) f n₂
    let S₅ ← unify (S₄.apply aet.tyOf) aef.tyOf
    let τ := S₅.apply aef.tyOf
    let acc := S₅.compose (S₄.compose (S₃.compose (S₂.compose S₁)))
    .ok (acc,
         .ite τ (S₅.applyAExpr (S₄.applyAExpr (S₃.applyAExpr (S₂.applyAExpr aec))))
               (S₅.applyAExpr (S₄.applyAExpr aet))
               (S₅.applyAExpr aef),
         n₃)

  | .eq e₁ e₂ => do
    let (S₁, ae₁, n₁) ← W Γ e₁ n
    let (S₂, ae₂, n₂) ← W (S₁.applyCtx Γ) e₂ n₁
    let S₃ ← unify (S₂.apply ae₁.tyOf) ae₂.tyOf
    let τ := S₃.apply ae₂.tyOf
    .ok (S₃.compose (S₂.compose S₁),
         .eq τ (S₃.applyAExpr (S₂.applyAExpr ae₁)) (S₃.applyAExpr ae₂),
         n₂)

  | .quant k body => do
    let α := Ty.var n
    let x := body.freshFor
    let (S₁, ae₁, n₁) ← W (Γ.addVar x (.mono α)) (body.varOpen 0 x) (n + 1)
    let S₂ ← unify ae₁.tyOf .bool
    let acc := S₂.compose S₁
    .ok (acc,
         .quant k (acc.apply α) (S₂.applyAExpr ae₁ |>.varClose 0 x),
         n₁)

  | .bvar _ => .error "unexpected bound variable in W"
termination_by e.size
decreasing_by all_goals simp [Expr.size, Expr.size_varOpen]<;> try omega

end HM
