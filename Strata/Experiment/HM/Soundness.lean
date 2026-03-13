/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AlgorithmW
import Strata.Experiment.HM.Erasure
import Strata.Experiment.HM.WellTyped

/-! ## Alternative Soundness via W_well_typed + HasTypeA_implies_HasType

Proves `W_ctxCompat`: if `W Γ e n = .ok (S, ae, n')` then
`ae.ctxCompat (S.applyCtx Γ)`.
-/

namespace HM

---------------------------------------------------------------------
-- Helper: substVar α τ is the same as applying the singleton subst [(α, τ)]
---------------------------------------------------------------------

private theorem substVar_eq_apply_singleton (α : Nat) (τ : Ty) (t : Ty) :
    t.substVar α τ = Subst.apply [(α, τ)] t := by
  induction t using Ty.ind' with
  | hvar n =>
    simp [Ty.substVar, Subst.apply, Map.find?]
    split
    · simp_all
    · grind
  | hcon name args ih =>
    simp only [Ty.substVar, Subst.apply, List.attach_map_val]
    congr 1
    induction args <;> simp_all

---------------------------------------------------------------------
-- Helper: Scheme.open α τ on a scheme with α at the head of vars
---------------------------------------------------------------------

private theorem Scheme.open_head (α : Nat) (τ : Ty) (rest : List Nat) (body : Ty) :
    Scheme.open α τ ⟨α :: rest, body⟩ = ⟨(α :: rest).removeAll [α], body.substVar α τ⟩ := by
  simp [Scheme.open]

---------------------------------------------------------------------
-- Helper: openAll on a scheme whose vars are already empty is id
---------------------------------------------------------------------

private theorem Scheme.openAll_mono (subst : List (Nat × Ty)) (τ : Ty) :
    Scheme.openAll subst (Scheme.mono τ) = Scheme.mono τ := by
  simp [Scheme.mono]
  induction subst with
  | nil => simp [Scheme.openAll, List.foldl]
  | cons p rest ih =>
    simp [Scheme.openAll, List.foldl] at *
    rw [show (List.foldl (fun acc x => Scheme.open x.1 x.2 acc) (Scheme.open p.1 p.2 ⟨[], τ⟩) rest)
        = Scheme.openAll rest (Scheme.open p.1 p.2 ⟨[], τ⟩) from rfl]
    simp [Scheme.open]
    exact ih


---------------------------------------------------------------------
-- varClose into a weaker context: after varClose k x, no fvar x
-- remains, so addVar x can be dropped
---------------------------------------------------------------------

theorem AExpr.ctxCompat_varClose_addVar (Γ : Ctx) (x : String) (σ : Scheme)
    (ae : AExpr) (k : Nat)
    (h : ae.ctxCompat (Γ.addVar x σ)) :
    (ae.varClose k x).ctxCompat Γ := by
  induction ae generalizing k with
  | bvar _ => trivial
  | fvar t y =>
    simp [AExpr.varClose, ctxCompat, Ctx.addVar] at *
    split
    · trivial
    · rename_i hne
      obtain ⟨σ', hfind, hinst⟩ := h
      rw [Map.find?_insert_ne _ _ _ _ (Ne.symm hne)] at hfind
      exact ⟨σ', hfind, hinst⟩
  | op _ _ => exact h
  | const _ => trivial
  | app _ _ _ _ ihf iha => exact ⟨ihf k h.1, iha k h.2⟩
  | abs _ _ ih => exact ih (k + 1) h
  | ite _ _ _ _ ihc iht ihf => exact ⟨ihc k h.1, iht k h.2.1, ihf k h.2.2⟩
  | eq _ _ _ iha ihb => exact ⟨iha k h.1, ihb k h.2⟩
  | quant _ _ _ ih => exact ih (k + 1) h

---------------------------------------------------------------------
-- Main theorem
---------------------------------------------------------------------

theorem W_ctxCompat (h : W Γ e n = .ok (S, ae, n')):
    ae.ctxCompat (S.applyCtx Γ) := by
  fun_induction W Γ e n generalizing S ae n' with
  | case1 Γ n x => -- fvar
    sorry
  | case2 Γ n f => -- op
    sorry
  | case3 Γ n c => -- const
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.ctxCompat]
  | case4 Γ n body α => -- abs
    sorry
  | case5 Γ n e₁ e₂ ih₁ ih₂ => -- app
    sorry
  | case6 Γ n c t f ihc iht ihf => -- ite
    sorry
  | case7 Γ n e₁ e₂ ih₁ ih₂ => -- eq
    sorry
  | case8 Γ n k body => -- quant
    sorry
  | case9 => contradiction

---------------------------------------------------------------------
-- Erasure: W produces an annotated expression that erases to the input
---------------------------------------------------------------------

theorem W_erase (h : W Γ e n = .ok (S, ae, n')) :
    ae.erase = e := by
  fun_induction W Γ e n generalizing S ae n' with
  | case1 Γ n x => -- fvar
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | case2 Γ n f => -- op
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | case3 Γ n c => -- const
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | case4 Γ n body α => -- abs
    rename_i x ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i _ v₁ hv₁; obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.erase, AExpr.erase_varClose, ih hv₁]
    exact Expr.varClose_varOpen _ _ _ (freshFor_fresh body)
  | case5 Γ n e₁ e₂ ih₁ ih₂ => -- app
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
    obtain ⟨S₁, ae₁, n₁⟩ := v₁; obtain ⟨S₂, ae₂, n₂⟩ := v₂
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.erase, AExpr.erase_applyAExpr, ih₁ hv₁, ih₂ _ _ hv₂]
  | case6 Γ n c t f ihc iht ihf => -- ite
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ vc hvc _ S₂ hS₂ _ vt hvt _ vf hvf _ S₅ hS₅
    obtain ⟨S₁, aec, n₁⟩ := vc; obtain ⟨S₃, aet, n₂⟩ := vt; obtain ⟨S₄, aef, n₃⟩ := vf
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.erase, AExpr.erase_applyAExpr, ihc hvc, iht _ _ _ hvt, ihf _ _ _ _ hvf]
  | case7 Γ n e₁ e₂ ih₁ ih₂ => -- eq
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
    obtain ⟨S₁, ae₁, n₁⟩ := v₁; obtain ⟨S₂, ae₂, n₂⟩ := v₂
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.erase, AExpr.erase_applyAExpr, ih₁ hv₁, ih₂ _ _ hv₂]
  | case8 Γ n k body => -- quant
    rename_i ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ S₂ hS₂; obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.erase, AExpr.erase_applyAExpr, AExpr.erase_varClose, ih hv₁]
    exact Expr.varClose_varOpen _ _ _ (freshFor_fresh body)
  | case9 => contradiction

---------------------------------------------------------------------
-- Alternative soundness: composing W_well_typed, W_ctxCompat,
-- and HasTypeA_implies_HasType
---------------------------------------------------------------------

/-
Theorem: If `W Γ e n = .ok (S, ae, n')`, then
  `ae.erase = e ∧ HasType (S.applyCtx Γ) e (Scheme.mono ae.tyOf)`.

Proof:
  1. `W_well_typed h` gives `HasTypeA [] ae ae.tyOf`.
  2. `W_ctxCompat h` gives `ae.ctxCompat (S.applyCtx Γ)`.
  3. `HasTypeA_implies_HasType ae ae.tyOf (S.applyCtx Γ)` applied to 1 and 2
     gives `HasType (S.applyCtx Γ) ae.erase (Scheme.mono ae.tyOf)`.
  4. `W_erase h` gives `ae.erase = e`.
  5. Rewrite 4 in 3 to conclude.
-/

theorem W_sound_alt (h : W Γ e n = .ok (S, ae, n')):
    ae.erase = e ∧ HasType (S.applyCtx Γ) e (Scheme.mono ae.tyOf) := by
  have herase := W_erase h
  have htyA   := W_well_typed h
  have hcompat := W_ctxCompat h
  have hty    := HasTypeA_implies_HasType ae ae.tyOf (S.applyCtx Γ) htyA hcompat
  exact ⟨herase, herase ▸ hty⟩

end HM
