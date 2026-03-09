/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Checker
import Strata.Experiment.HM.Typing
import Strata.Experiment.HM.Soundness

/-! ## Erasure theorem: HasTypeA implies HasType on the erased expression

If an annotated expression is well-typed (`HasTypeA`), then its erasure
is well-typed in the declarative system (`HasType`), given a compatible
named context.
-/

namespace HM

/-! ### Compatibility: a named context agrees with the annotations -/

/-- Every `fvar t x` in `ae` satisfies `Γ.vars.find? x = some (Scheme.mono t)`,
    and every `op t f` satisfies `Γ.ops.find? f = some (Scheme.mono t)`. -/
def AExpr.ctxCompat (Γ : Ctx) : AExpr → Prop
  | .bvar _         => True
  | .fvar t x       => Γ.vars.find? x = some (Scheme.mono t)
  | .op t f         => Γ.ops.find? f = some (Scheme.mono t)
  | .const _        => True
  | .app _ _ f a    => f.ctxCompat Γ ∧ a.ctxCompat Γ
  | .abs _ e        => e.ctxCompat Γ
  | .ite _ c th el  => c.ctxCompat Γ ∧ th.ctxCompat Γ ∧ el.ctxCompat Γ
  | .eq _ a b       => a.ctxCompat Γ ∧ b.ctxCompat Γ
  | .quant _ _ e    => e.ctxCompat Γ

/-! ### HasTypeA varOpen: opening a binder preserves typing -/

theorem HasTypeA_varOpen (Δ : List Ty) (t : Ty) (x : String) (ae : AExpr) (τ : Ty)
    (h : HasTypeA (Δ ++ [t]) ae τ) :
    HasTypeA Δ (ae.varOpen Δ.length t x) τ := by
  generalize hΔ' : Δ ++ [t] = Δ' at h
  induction h generalizing Δ with
  | @bvar Δ' n ty hlookup =>
    subst hΔ'
    simp [AExpr.varOpen]
    split
    · -- n = Δ.length
      rename_i heq; subst heq
      simp [] at hlookup
      subst hlookup; exact .fvar
    · -- n ≠ Δ.length
      rename_i hne
      rw [List.getElem?_append] at hlookup
      split at hlookup
      · -- n < Δ.length: index into Δ
        exact .bvar hlookup
      · -- n ≥ Δ.length and n ≠ Δ.length, so n > Δ.length
        rename_i hge
        have hgt : n > Δ.length := by omega
        grind
  | fvar => subst hΔ'; simp [AExpr.varOpen]; exact .fvar
  | op => subst hΔ'; simp [AExpr.varOpen]; exact .op
  | boolc => subst hΔ'; simp [AExpr.varOpen]; exact .boolc
  | intc => subst hΔ'; simp [AExpr.varOpen]; exact .intc
  | @abs Δ' dom body cod hbody ih =>
    subst hΔ'; simp [AExpr.varOpen]
    exact .abs (ih (Δ' :: Δ) (by simp))
  | app _ _ ihf iha =>
    subst hΔ'; simp [AExpr.varOpen]
    exact .app (ihf Δ rfl) (iha Δ rfl)
  | ite _ _ _ ihc iht ihf =>
    subst hΔ'; simp [AExpr.varOpen]
    exact .ite (ihc Δ rfl) (iht Δ rfl) (ihf Δ rfl)
  | eq _ _ iha ihb =>
    subst hΔ'; simp [AExpr.varOpen]
    exact .eq (iha Δ rfl) (ihb Δ rfl)
  | @quant Δ' boundTy body k hbody ih =>
    subst hΔ'; simp [AExpr.varOpen]
    exact .quant (ih (Δ' :: Δ) (by simp))

/-! ### ctxCompat is preserved by varOpen when we extend Γ -/

theorem AExpr.ctxCompat_varOpen (Γ : Ctx) (ae : AExpr) (k : Nat) (t : Ty) (x : String)
    (hc : ae.ctxCompat Γ) (hx : Γ.vars.find? x = some (Scheme.mono t)) :
    (ae.varOpen k t x).ctxCompat Γ := by
  induction ae generalizing k with
  | bvar n => simp [AExpr.varOpen]; split <;> simp [ctxCompat, *]
  | fvar _ _ => exact hc
  | op _ _ => exact hc
  | const _ => trivial
  | app _ _ _ _ ihf iha => exact ⟨ihf k hc.1, iha k hc.2⟩
  | abs _ _ ih => exact ih (k + 1) hc
  | ite _ _ _ _ ihc iht ihf => exact ⟨ihc k hc.1, iht k hc.2.1, ihf k hc.2.2⟩
  | eq _ _ _ iha ihb => exact ⟨iha k hc.1, ihb k hc.2⟩
  | quant _ _ _ ih => exact ih (k + 1) hc

/-! ### Map helper -/

theorem Map.find?_insert_self [DecidableEq α] (m : Map α β) (k : α) (v : β) :
    (m.insert k v).find? k = some v := by
  induction m with
  | nil => simp [Map.insert, Map.find?]
  | cons p m ih =>
    simp [Map.insert]
    split <;> simp [Map.find?, *]

theorem Map.find?_insert_ne [DecidableEq α] (m : Map α β) (k k' : α) (v : β) (h : k' ≠ k) :
    (m.insert k v).find? k' = m.find? k' := by
  induction m with
  | nil => simp [Map.insert, Map.find?]; grind
  | cons p m ih =>
    obtain ⟨a, b⟩ := p
    simp [Map.insert]
    split <;> simp [Map.find?, *]
    grind

theorem AExpr.ctxCompat_addVar (Γ : Ctx) (x : String) (σ : Scheme) (ae : AExpr)
    (hc : ae.ctxCompat Γ) (hfresh : Expr.fresh x ae.erase) :
    ae.ctxCompat (Γ.addVar x σ) := by
  induction ae with
  | bvar _ => trivial
  | fvar t y =>
    simp [ctxCompat, Ctx.addVar, AExpr.erase, Expr.fresh] at *
    rw [Map.find?_insert_ne _ x y _ hfresh]
    exact hc
  | op _ _ => exact hc
  | const _ => trivial
  | app _ _ _ _ ihf iha =>
    simp [ctxCompat, AExpr.erase, Expr.fresh] at *
    exact ⟨ihf hc.1 hfresh.1, iha hc.2 hfresh.2⟩
  | abs _ _ ih =>
    simp [ctxCompat, AExpr.erase, Expr.fresh] at *
    exact ih hc hfresh
  | ite _ _ _ _ ihc iht ihf =>
    simp [ctxCompat, AExpr.erase, Expr.fresh] at *
    exact ⟨ihc hc.1 hfresh.1, iht hc.2.1 hfresh.2.1, ihf hc.2.2 hfresh.2.2⟩
  | eq _ _ _ iha ihb =>
    simp [ctxCompat, AExpr.erase, Expr.fresh] at *
    exact ⟨iha hc.1 hfresh.1, ihb hc.2 hfresh.2⟩
  | quant _ _ _ ih =>
    simp [ctxCompat, AExpr.erase, Expr.fresh] at *
    exact ih hc hfresh

/-! ### Main erasure theorem -/

/-! ### AExpr.size and varOpen preservation -/

def AExpr.size : AExpr → Nat
  | .bvar _         => 1
  | .fvar _ _       => 1
  | .app _ _ f a    => 1 + f.size + a.size
  | .abs _ e        => 1 + e.size
  | .op _ _         => 1
  | .const _        => 1
  | .ite _ c t f    => 1 + c.size + t.size + f.size
  | .eq _ a b       => 1 + a.size + b.size
  | .quant _ _ e    => 1 + e.size

@[simp] theorem AExpr.size_varOpen (k : Nat) (ty : Ty) (x : String) (ae : AExpr) :
    (ae.varOpen k ty x).size = ae.size := by
  induction ae generalizing k with
  | bvar n => simp [varOpen, size]; split <;> simp [size]
  | fvar _ _ => rfl
  | app _ _ _ _ ih₁ ih₂ => simp [varOpen, size, ih₁, ih₂]
  | abs _ _ ih => simp [varOpen, size, ih]
  | op _ _ => rfl
  | const _ => rfl
  | ite _ _ _ _ ihc iht ihf => simp [varOpen, size, ihc, iht, ihf]
  | eq _ _ _ ih₁ ih₂ => simp [varOpen, size, ih₁, ih₂]
  | quant _ _ _ ih => simp [varOpen, size, ih]

/-! ### Main erasure theorem -/

theorem HasTypeA_implies_HasType (ae : AExpr) (τ : Ty) (Γ : Ctx)
    (h : HasTypeA [] ae τ) (hc : ae.ctxCompat Γ) :
    HasType Γ ae.erase (Scheme.mono τ) := by
  have : ∀ n (ae : AExpr), ae.size = n → ∀ τ Γ,
      HasTypeA [] ae τ → ae.ctxCompat Γ → HasType Γ ae.erase (Scheme.mono τ) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro ae hsize τ Γ h hc
      match ae with
      | .bvar n => cases h; simp at *
      | .fvar t x => cases h; simp [AExpr.erase]; exact .fvar hc
      | .op t f => cases h; simp [AExpr.erase]; exact .op hc
      | .const (.bool b) => cases h; simp [AExpr.erase]; exact .const
      | .const (.int i) => cases h; simp [AExpr.erase]; exact .const
      | .app fnTy argTy f a =>
        cases h with
        | app hf ha =>
          simp [AExpr.erase]
          have hsf : f.size < n := by simp [AExpr.size] at hsize; omega
          have hsa : a.size < n := by simp [AExpr.size] at hsize; omega
          have hf' : HasType Γ f.erase (Scheme.mono (Ty.arrow argTy τ)) :=
            ih f.size hsf f rfl (Ty.arrow argTy τ) Γ hf hc.1
          have ha' : HasType Γ a.erase (Scheme.mono argTy) :=
            ih a.size hsa a rfl argTy Γ ha hc.2
          have hm1 : Scheme.isMono (Scheme.mono τ) := rfl
          have hm2 : Scheme.isMono (Scheme.mono argTy) := rfl
          exact .app hm1 hm2 hf' ha'
      | .ite resTy c t f =>
        cases h with
        | ite hc' ht hf =>
          simp [AExpr.erase]
          have hsc : c.size < n := by simp [AExpr.size] at hsize; omega
          have hst : t.size < n := by simp [AExpr.size] at hsize; omega
          have hsf : f.size < n := by simp [AExpr.size] at hsize; omega
          have hc'' : HasType Γ c.erase (Scheme.mono Ty.bool) :=
            ih c.size hsc c rfl Ty.bool Γ hc' hc.1
          have ht' : HasType Γ t.erase (Scheme.mono τ) :=
            ih t.size hst t rfl τ Γ ht hc.2.1
          have hf' : HasType Γ f.erase (Scheme.mono τ) :=
            ih f.size hsf f rfl τ Γ hf hc.2.2
          exact .ite hc'' ht' hf'
      | .eq subTy a b =>
        cases h with
        | eq ha hb =>
          simp [AExpr.erase]
          have hsa : a.size < n := by simp [AExpr.size] at hsize; omega
          have hsb : b.size < n := by simp [AExpr.size] at hsize; omega
          have ha' : HasType Γ a.erase (Scheme.mono subTy) :=
            ih a.size hsa a rfl subTy Γ ha hc.1
          have hb' : HasType Γ b.erase (Scheme.mono subTy) :=
            ih b.size hsb b rfl subTy Γ hb hc.2
          exact .eq ha' hb'
      | .abs arrTy body =>
        cases h with
        | abs hbody =>
          -- hbody : HasTypeA [dom] body cod, τ = Ty.arrow dom cod
          -- Need: HasType Γ body.erase.abs (Scheme.mono (Ty.arrow dom cod))
          rename_i dom cod
          simp [AExpr.erase]
          let x := body.erase.freshFor
          have hfresh : Expr.fresh x body.erase := freshFor_fresh body.erase
          -- Open the body to remove the bvar
          have hopen : HasTypeA [] (body.varOpen 0 dom x) cod :=
            HasTypeA_varOpen [] dom x body cod hbody
          -- body.varOpen has same size as body
          have hszlt : (body.varOpen 0 dom x).size < n := by
            simp [AExpr.size_varOpen, AExpr.size] at hsize ⊢; omega
          -- ctxCompat for the opened body in the extended context
          have hxfind : (Γ.addVar x (Scheme.mono dom)).vars.find? x = some (Scheme.mono dom) := by
            simp [Ctx.addVar]
            exact Map.find?_insert_self Γ.vars x (Scheme.mono dom)
          have hcompat : AExpr.ctxCompat (Γ.addVar x (Scheme.mono dom)) (body.varOpen 0 dom x) :=
            AExpr.ctxCompat_varOpen (Γ.addVar x (Scheme.mono dom)) body 0 dom x
              (AExpr.ctxCompat_addVar Γ x (Scheme.mono dom) body hc hfresh)
              hxfind
          -- Apply IH
          have ih' : HasType (Γ.addVar x (Scheme.mono dom)) (body.varOpen 0 dom x).erase (Scheme.mono cod) :=
            ih (body.varOpen 0 dom x).size hszlt (body.varOpen 0 dom x) rfl cod
              (Γ.addVar x (Scheme.mono dom)) hopen hcompat
          rw [AExpr.erase_varOpen] at ih'
          have hm1 : Scheme.isMono (Scheme.mono dom) := rfl
          have hm2 : Scheme.isMono (Scheme.mono cod) := rfl
          exact .abs hfresh hm1 hm2 ih'
      | .quant k boundTy body =>
        cases h with
        | quant hbody =>
          simp [AExpr.erase]
          let x := body.erase.freshFor
          have hfresh : Expr.fresh x body.erase := freshFor_fresh body.erase
          have hopen : HasTypeA [] (body.varOpen 0 boundTy x) Ty.bool :=
            HasTypeA_varOpen [] boundTy x body Ty.bool hbody
          have hszlt : (body.varOpen 0 boundTy x).size < n := by
            simp [AExpr.size_varOpen, AExpr.size] at hsize ⊢; omega
          have hxfind : (Γ.addVar x (Scheme.mono boundTy)).vars.find? x = some (Scheme.mono boundTy) :=
            Map.find?_insert_self Γ.vars x (Scheme.mono boundTy)
          have hcompat : AExpr.ctxCompat (Γ.addVar x (Scheme.mono boundTy)) (body.varOpen 0 boundTy x) :=
            AExpr.ctxCompat_varOpen (Γ.addVar x (Scheme.mono boundTy)) body 0 boundTy x
              (AExpr.ctxCompat_addVar Γ x (Scheme.mono boundTy) body hc hfresh)
              hxfind
          have ih' : HasType (Γ.addVar x (Scheme.mono boundTy)) (body.varOpen 0 boundTy x).erase (Scheme.mono Ty.bool) :=
            ih (body.varOpen 0 boundTy x).size hszlt (body.varOpen 0 boundTy x) rfl Ty.bool
              (Γ.addVar x (Scheme.mono boundTy)) hopen hcompat
          rw [AExpr.erase_varOpen] at ih'
          have hm : Scheme.isMono (Scheme.mono boundTy) := rfl
          exact .quant hfresh hm ih'
  exact this ae.size ae rfl τ Γ h hc

#print axioms HasTypeA_implies_HasType

end HM
