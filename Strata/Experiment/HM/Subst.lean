/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AExpr
import Strata.DL.Util.Map

/-! ## Type Substitution for Hindley-Milner -/

namespace HM

---------------------------------------------------------------------
-- Context (needed here for applyCtx)
---------------------------------------------------------------------

structure Ctx where
  vars : Map String Scheme
  ops  : Map String Scheme
  deriving Inhabited, Repr

def Ctx.addVar (Γ : Ctx) (x : String) (σ : Scheme) : Ctx :=
  { Γ with vars := Γ.vars.insert x σ }

/-- Free type vars of an entire context. -/
def Scheme.freeVarsCtx (Γ : Ctx) : List Nat :=
  (Γ.vars.values.flatMap Scheme.freeVars) ++ (Γ.ops.values.flatMap Scheme.freeVars)

---------------------------------------------------------------------
-- Substitution
---------------------------------------------------------------------

abbrev Subst := Map Nat Ty

def Subst.id : Subst := []

/-- Variables appearing in the range (values) of a substitution. -/
def substFreeVars (S : Subst) : List Nat :=
  S.values.flatMap Ty.freeVars

def Subst.apply (S : Subst) : Ty → Ty
  | .var n => match S.find? n with
    | some τ => τ
    | none   => .var n
  | .con name args => .con name (args.attach.map fun ⟨t, _⟩ => S.apply t)
termination_by t => t
decreasing_by term_by_mem

/-- `(compose S₂ S₁)(τ) = S₂(S₁(τ))` -/
def Subst.compose (S₂ S₁ : Subst) : Subst :=
  (S₁.fmap (S₂.apply ·)) ++ S₂

def Subst.applyScheme (S : Subst) (σ : Scheme) : Scheme :=
  let S' : Subst := S.filter (fun (v, _) => v ∉ σ.vars)
  ⟨σ.vars, S'.apply σ.body⟩

def Subst.applyCtx (S : Subst) (Γ : Ctx) : Ctx :=
  { vars := Γ.vars.fmap (S.applyScheme ·)
    ops  := Γ.ops.fmap (S.applyScheme ·) }

def Subst.applyAExpr (S : Subst) : AExpr → AExpr
  | .bvar n         => .bvar n
  | .fvar t x       => .fvar (S.apply t) x
  | .app t₁ t₂ f a => .app (S.apply t₁) (S.apply t₂) (S.applyAExpr f) (S.applyAExpr a)
  | .abs t e        => .abs (S.apply t) (S.applyAExpr e)
  | .op t s         => .op (S.apply t) s
  | .const c        => .const c
  | .ite t c th el  => .ite (S.apply t) (S.applyAExpr c) (S.applyAExpr th) (S.applyAExpr el)
  | .eq t a b       => .eq (S.apply t) (S.applyAExpr a) (S.applyAExpr b)
  | .quant q τ e    => .quant q (S.apply τ) (S.applyAExpr e)

/-- Extract the monotype from an annotated expression. -/
def AExpr.tyOf : AExpr → Ty
  | .bvar _           => .var 0  -- should not occur in well-typed output
  | .fvar t _         => t
  | .app t₁ _ _ _     => match t₁ with
    | .con "→" [_, r] => r
    | t                => t  -- ill-formed, fallback
  | .abs t _          => t
  | .op t _           => t
  | .const (.bool _)  => .bool
  | .const (.int _)   => .int
  | .ite t _ _ _      => t
  | .eq _ _ _         => .bool
  | .quant _ _ _      => .bool

end HM
