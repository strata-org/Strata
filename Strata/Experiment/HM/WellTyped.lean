/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AlgorithmW
import Strata.Experiment.HM.Checker
import Strata.Experiment.HM.Soundness

/-! ## Algorithm W produces well-typed annotated terms

Main theorem: if `W Γ e n` succeeds with `(S, ae, n')`,
then `HasTypeA [] ae ae.tyOf`.
-/

namespace HM

/-! ### Map.find? after insert -/

theorem Map.find?_insert_self [DecidableEq α] (m : Map α β) (a : α) (b : β) :
    (m.insert a b).find? a = some b := by
  induction m with
  | nil => simp [Map.insert, Map.find?]
  | cons hd tl ih =>
    simp only [Map.insert]
    split <;> simp [Map.find?, *]

theorem Map.find?_insert_ne [DecidableEq α] (m : Map α β) (a a' : α) (b : β) (h : a ≠ a') :
    (m.insert a b).find? a' = m.find? a' := by
  induction m with
  | nil => simp [Map.insert, Map.find?, h]
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [Map.insert]
    split
    · simp [Map.find?, *]
    · simp only [Map.find?]; split <;> simp [ih]

theorem Map.find?_fmap [DecidableEq α] (f : β → γ) (m : Map α β) (a : α) :
    (m.fmap f).find? a = (m.find? a).map f := by
  induction m with
  | nil => simp [Map.fmap, Map.find?]
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [Map.fmap, List.map_cons, Map.find?]
    split
    · simp
    · exact ih

theorem Map.find?_append [DecidableEq α] (m₁ m₂ : Map α β) (a : α) :
    (m₁ ++ m₂).find? a = (m₁.find? a).or (m₂.find? a) := by
  induction m₁ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [Map.find?]
    rw [Map.find?.eq_def]
    split <;> try contradiction
    rename_i heq; cases heq
    split <;> try assumption
    simp[Option.or]

theorem Subst.id_apply (τ : Ty) : Subst.id.apply τ = τ := by
  induction τ using Ty.ind' with
  | hvar n => simp [Subst.id, Subst.apply, Map.find?]
  | hcon name args ih =>
    simp only [Subst.apply, List.attach_map_val]
    congr 1
    rw[@List.map_congr_left _ _ _ _ (fun (x: Ty) => x)] <;> try assumption
    apply List.map_id'

theorem Scheme.instantiate_mono (τ : Ty) (n : Nat) :
    (Scheme.mono τ).instantiate n = (τ, n) := by
  simp [Scheme.mono, Scheme.instantiate]
  exact Subst.id_apply τ

theorem Subst.applyCtx_vars_find? (S : Subst) (Γ : Ctx) (x : String) :
    (S.applyCtx Γ).vars.find? x = (Γ.vars.find? x).map (S.applyScheme ·) := by
  simp [Subst.applyCtx, Map.find?_fmap]

/-! ### Predicate: every free occurrence of `x` carries annotation `t` -/

def AExpr.allFvarTy (x : String) (t : Ty) : AExpr → Prop
  | .bvar _         => True
  | .fvar t' y      => y = x → t' = t
  | .app _ _ f a    => f.allFvarTy x t ∧ a.allFvarTy x t
  | .abs _ e        => e.allFvarTy x t
  | .op _ _         => True
  | .const _        => True
  | .ite _ c th el  => c.allFvarTy x t ∧ th.allFvarTy x t ∧ el.allFvarTy x t
  | .eq _ a b       => a.allFvarTy x t ∧ b.allFvarTy x t
  | .quant _ _ e    => e.allFvarTy x t

/-! ### varClose preserves HasTypeA

Theorem: If `HasTypeA Δ ae ty` and every free occurrence of `x` in `ae`
carries annotation `t`, then
  `HasTypeA (Δ.take k ++ [t] ++ Δ.drop k) (ae.varClose k x) ty`.

Proof: By induction on `HasTypeA Δ ae ty`.

  Case bvar n (Δ[n]? = some ty):
    1. n < Δ.length (since Δ[n]? = some ty), so n < k (since Δ.length ≤ k).
    2. varClose k x (.bvar n) = .bvar n   by definition
    3. n < k ≤ Δ.length means n < min k Δ.length, so index n falls in Δ.take k.
       (Δ.take k ++ [t] ++ Δ.drop k)[n]? = (Δ.take k)[n]? = Δ[n]? = some ty
    4. done by HasTypeA.bvar

  Case fvar t' y:
    Subcase y ≠ x:
      1. varClose k x (.fvar t' y) = .fvar t' y
      2. done by HasTypeA.fvar
    Subcase y = x:
      1. allFvarTy gives t' = t
      2. varClose k x (.fvar t x) = .bvar k
      3. (Δ.take k ++ [t] ++ Δ.drop k)[k]? = some t
         since Δ.take k has length min k Δ.length = Δ.length (since Δ.length ≤ k),
         index k falls at position k - Δ.length in [t] ++ Δ.drop k.
         When Δ.length = k: index 0 in [t] ++ ... = some t. ✓
         When Δ.length < k: Δ.take k = Δ, so index k in Δ ++ [t] ++ [] with
         Δ.length < k means index k - Δ.length in [t] ++ Δ.drop k.
         But Δ.drop k = [] (since k ≥ Δ.length), so [t] ++ [] = [t].
         k - Δ.length ≥ 1 when Δ.length < k, so [t][k - Δ.length]? could be none.
         Actually this fails when Δ.length < k. Need Δ.length = k? No — when
         Δ.length ≤ k, Δ.take k = Δ and Δ.drop k = [].
         So the spliced list is Δ ++ [t]. Index k in Δ ++ [t]:
         since Δ.length ≤ k, index k - Δ.length in [t] = [t][k - Δ.length]?.
         This is some t only when k - Δ.length = 0, i.e., k = Δ.length.
         So we need k = Δ.length, not just Δ.length ≤ k.

  Revised: precondition should be Δ.length = k (not ≤).

  With Δ.length = k:
    bvar case: n < Δ.length = k, so n < k. Δ.take k = Δ. Index n in Δ ++ [t] = Δ[n]?. ✓
    fvar x case: index k in Δ ++ [t] = [t][0]? = some t. ✓
    abs case: context is dom :: Δ with length Δ.length + 1 = k + 1. IH at k+1. ✓
    quant case: same as abs. ✓
-/

theorem HasTypeA_varClose (h : HasTypeA Δ ae ty) (hall : ae.allFvarTy x t)
    (k : Nat) (hk : Δ.length = k) :
    HasTypeA (Δ ++ [t]) (ae.varClose k x) ty := by
  induction h generalizing k with
  | bvar hlook =>
    simp [AExpr.varClose]
    have hn := (List.getElem?_eq_some_iff.mp hlook).1
    exact .bvar (by simp [List.getElem?_append_left (by omega)]; assumption)
  | fvar =>
    simp [AExpr.varClose, AExpr.allFvarTy] at hall ⊢
    split
    · subst_vars; specialize hall rfl; subst_vars;
      exact .bvar (by simp)
    · exact .fvar
  | op => simp [AExpr.varClose]; exact .op
  | boolc => simp [AExpr.varClose]; exact .boolc
  | intc => simp [AExpr.varClose]; exact .intc
  | abs _ ih =>
    simp [AExpr.varClose, AExpr.allFvarTy] at hall ⊢
    exact .abs (by rw [←List.cons_append]; exact ih hall (k + 1) (by simp; omega))
  | app _ _ ihf iha =>
    simp [AExpr.varClose, AExpr.allFvarTy] at hall ⊢
    exact .app (ihf hall.1 k hk) (iha hall.2 k hk)
  | ite _ _ _ ihc iht ihf =>
    simp [AExpr.varClose, AExpr.allFvarTy] at hall ⊢
    exact .ite (ihc hall.1 k hk) (iht hall.2.1 k hk) (ihf hall.2.2 k hk)
  | eq _ _ iha ihb =>
    simp [AExpr.varClose, AExpr.allFvarTy] at hall ⊢
    exact .eq (iha hall.1 k hk) (ihb hall.2 k hk)
  | quant _ ih =>
    simp [AExpr.varClose, AExpr.allFvarTy] at hall ⊢
    exact .quant (by rw [←List.cons_append]; exact ih hall (k + 1) (by simp; omega))

/-! ### Corollary for the case used by W: Δ = [], k = 0 -/

theorem HasTypeA_varClose_zero (h : HasTypeA [] ae ty) (hall : ae.allFvarTy x t) :
    HasTypeA [t] (ae.varClose 0 x) ty := by
  exact HasTypeA_varClose h hall 0 rfl

/-! ### applyAExpr preserves HasTypeA -/

/-
Theorem: If `HasTypeA Δ ae ty`, then
  `HasTypeA (Δ.map S.apply) (S.applyAExpr ae) (S.apply ty)`.

Proof: By induction on `HasTypeA Δ ae ty`.
  Each case follows by applying S to all type annotations and using the IH.
  The key observations:
  - S.apply preserves arrow structure: S.apply (arrow a b) = arrow (S.apply a) (S.apply b)
  - S.apply preserves bool: S.apply .bool = .bool
  - bvar: (Δ.map S.apply)[n]? = (Δ[n]?).map S.apply, so some t maps to some (S.apply t)
  - applyAExpr leaves bvar indices unchanged
-/

theorem HasTypeA_applyAExpr (S : Subst) (h : HasTypeA Δ ae ty) :
    HasTypeA (Δ.map S.apply) (S.applyAExpr ae) (S.apply ty) := by
  induction h with
  | bvar hlook =>
    exact .bvar (by simp [List.getElem?_map, hlook])
  | fvar => exact .fvar
  | op => exact .op
  | boolc => simp [Subst.applyAExpr, Ty.bool, Subst.apply]; exact .boolc
  | intc => simp [Subst.applyAExpr, Ty.int, Subst.apply]; exact .intc
  | abs _ ih =>
    simp [Subst.applyAExpr, Subst.apply_arrow]
    exact .abs ih
  | app _ _ ihf iha =>
    simp [Subst.applyAExpr, Subst.apply_arrow]
    simp at ihf
    exact .app ihf iha
  | ite _ _ _ ihc iht ihf =>
    simp [Subst.applyAExpr]
    simp[Subst.apply, Ty.bool] at ihc
    exact .ite ihc iht ihf
  | eq _ _ iha ihb =>
    simp [Subst.applyAExpr, Ty.bool, Subst.apply]
    exact .eq iha ihb
  | quant _ ih =>
    simp [Subst.applyAExpr, Ty.bool, Subst.apply]
    simp[Subst.apply, Ty.bool] at ih
    exact .quant ih

/-! ### allFvarTy is preserved by applyAExpr -/

theorem AExpr.allFvarTy_applyAExpr (S : Subst) (h : ae.allFvarTy x t) :
    (S.applyAExpr ae).allFvarTy x (S.apply t) := by
  induction ae with
  | bvar _ => trivial
  | fvar t' y => simp [Subst.applyAExpr, allFvarTy] at *; intro heq; exact congrArg S.apply (h heq)
  | app _ _ f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | abs _ e ih => exact ih h
  | op _ _ => trivial
  | const _ => trivial
  | ite _ c th el ihc ihth ihel => exact ⟨ihc h.1, ihth h.2.1, ihel h.2.2⟩
  | eq _ a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | quant _ _ e ih => exact ih h

/-! ### allFvarTy preserved by varClose -/

theorem AExpr.allFvarTy_varClose_other (ae : AExpr) (h : ae.allFvarTy x t) (k : Nat) :
    (ae.varClose k z).allFvarTy x t := by
  induction ae generalizing k with
  | bvar _ => trivial
  | fvar t' y =>
    simp [varClose]; split
    · trivial
    · exact h
  | app _ _ f a ihf iha => exact ⟨ihf h.1 k, iha h.2 k⟩
  | abs _ e ih => exact ih h (k + 1)
  | op _ _ => trivial
  | const _ => trivial
  | ite _ c th el ihc ihth ihel => exact ⟨ihc h.1 k, ihth h.2.1 k, ihel h.2.2 k⟩
  | eq _ a b iha ihb => exact ⟨iha h.1 k, ihb h.2 k⟩
  | quant _ _ e ih => exact ih h (k + 1)

theorem AExpr.allFvarTy_varClose_same (ae : AExpr) (k : Nat) (x : String) (t : Ty) :
    (ae.varClose k x).allFvarTy x t := by
  induction ae generalizing k with
  | bvar _ => trivial
  | fvar t' y => simp [varClose]; split <;> simp_all [allFvarTy]
  | app _ _ f a ihf iha => exact ⟨ihf k, iha k⟩
  | abs _ e ih => exact ih (k + 1)
  | op _ _ => trivial
  | const _ => trivial
  | ite _ c th el ihc ihth ihel => exact ⟨ihc k, ihth k, ihel k⟩
  | eq _ a b iha ihb => exact ⟨iha k, ihb k⟩
  | quant _ _ e ih => exact ih (k + 1)

/-! ### Substitution compose applies -/

theorem Subst.apply_compose (S₂ S₁ : Subst) (τ : Ty) :
    (S₂.compose S₁).apply τ = S₂.apply (S₁.apply τ) := by
  induction τ using Ty.ind' with
  | hvar n =>
    simp only [Subst.apply, Subst.compose, Map.find?_append, Map.find?_fmap]
    cases S₁.find? n with
    | none =>
      simp [Option.or, Option.map, Subst.apply]
    | some τ => simp [Option.or, Option.map]
  | hcon name args ih =>
    simp only [Subst.apply, List.attach_map_val]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro t ht
    exact ih t ht

/-! ### W produces terms where the fresh variable has the right annotation

Theorem: If `W Γ e n = .ok (S, ae, n')` and `Γ.vars.find? x = some (.mono α)`,
  then `ae.allFvarTy x (S.apply α)`.

Proof: By `fun_induction` on `W`, generalizing `x` and `α`.

  Case fvar y:
    W returns `(Subst.id, .fvar τ y, n₁)` where `τ` comes from instantiating `Γ.vars.find? y`.
    If `y = x`: lookup gives `σ = .mono α`, instantiate_mono gives `τ = α`,
      and `Subst.id.apply α = α`.
    If `y ≠ x`: `allFvarTy x _ (.fvar τ y)` holds vacuously.

  Case op/const/bvar: no fvars in output. Trivial.

  Case abs body:
    W picks `z = body.freshFor`, recurses with `Γ.addVar z (.mono β)`.
    If `z = x`: `varClose 0 x` eliminates all `fvar x`, so `allFvarTy_varClose_same`
      gives the result vacuously.
    If `z ≠ x`: `find?_insert_ne` gives `(Γ.addVar z _).vars.find? x = some (.mono α)`.
      IH gives `ae₁.allFvarTy x (S₁.apply α)`.
      `allFvarTy_varClose_other` preserves this through `varClose 0 z`.

  Case app e₁ e₂:
    IH on `e₁`: `ae₁.allFvarTy x (S₁.apply α)`.
    For `e₂`: `applyCtx_vars_find?` + `applyScheme_mono` give
      `(S₁.applyCtx Γ).vars.find? x = some (.mono (S₁.apply α))`.
    IH on `e₂`: `ae₂.allFvarTy x (S₂.apply (S₁.apply α))`.
    Lift `ae₁` through `S₂`, `S₃` and `ae₂` through `S₃` via `allFvarTy_applyAExpr`.
    Reconcile composed substitutions via `apply_compose`.

  Case ite c t f:
    Same pattern. IH on `c` with `Γ`, on `t` with `(S₂ ∘ S₁).applyCtx Γ`,
    on `f` with `(S₃ ∘ S₂ ∘ S₁).applyCtx Γ`.
    Lift `c` through S₂–S₅, `t` through S₄–S₅, `f` through S₅.

  Case eq e₁ e₂: same as app.

  Case quant body:
    Same as abs: if `z = x`, `allFvarTy_varClose_same` after `S₂.applyAExpr`;
    if `z ≠ x`, IH + `allFvarTy_applyAExpr S₂` + `allFvarTy_varClose_other`.
-/

theorem W_allFvarTy (hW : W Γ e n = .ok (S, ae, n'))
    (hlookup : Γ.vars.find? x = some (.mono α)) :
    ae.allFvarTy x (S.apply α) := by
  fun_induction W Γ e n generalizing S ae n' x α with
  | case1 Γ n y => -- fvar
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    rename_i σ hσ
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    simp [AExpr.allFvarTy]
    intro heq; subst heq
    rw [hlookup] at hσ; simp at hσ; subst hσ
    simp [Scheme.instantiate_mono, Subst.id_apply]
  | case2 => -- op
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    simp [AExpr.allFvarTy]
  | case3 => -- const
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    simp [AExpr.allFvarTy]
  | case4 Γ n body α' => -- abs
    rename_i z ih
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    rename_i _ v₁ hv₁
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    simp [AExpr.allFvarTy]
    by_cases hzx : z = x
    · subst hzx
      exact AExpr.allFvarTy_varClose_same ae₁ 0 _ _
    · have hlookup' : (Γ.addVar z (.mono α')).vars.find? x = some (.mono α) := by
        simp [Ctx.addVar, Map.find?_insert_ne _ _ _ _ hzx, hlookup]
      exact AExpr.allFvarTy_varClose_other ae₁ (ih hv₁ hlookup') 0
  | case5 Γ n e₁ e₂ ih₁ ih₂ => -- app
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    obtain ⟨S₂, ae₂, n₂⟩ := v₂
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    dsimp only at hv₂ hS₃
    have h₁ := ih₁ hv₁ hlookup
    have hlookup₂ : (S₁.applyCtx Γ).vars.find? x = some (.mono (S₁.apply α)) := by
      rw [Subst.applyCtx_vars_find?, hlookup]; simp [Subst.applyScheme_mono]
    have h₂ := ih₂ _ _ hv₂ hlookup₂
    simp [AExpr.allFvarTy]
    constructor
    · -- S₃.applyAExpr (S₂.applyAExpr ae₁) has allFvarTy x (S₃.compose (S₂.compose S₁)).apply α
      rw [Subst.apply_compose, Subst.apply_compose]
      exact AExpr.allFvarTy_applyAExpr S₃ (AExpr.allFvarTy_applyAExpr S₂ h₁)
    · -- S₃.applyAExpr ae₂
      rw [Subst.apply_compose, Subst.apply_compose]
      exact AExpr.allFvarTy_applyAExpr S₃ h₂
  | case6 Γ n c t f ih_c ih_t ih_f => -- ite
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    rename_i _ vc hvc _ S₂ hS₂ _ vt hvt _ vf hvf _ S₅ hS₅
    obtain ⟨S₁, aec, n₁⟩ := vc
    obtain ⟨S₃, aet, n₂⟩ := vt
    obtain ⟨S₄, aef, n₃⟩ := vf
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    dsimp only at hvc hS₂ hvt hvf hS₅
    have hc := ih_c hvc hlookup
    have hlookup_t : ((S₂.compose S₁).applyCtx Γ).vars.find? x
        = some (.mono ((S₂.compose S₁).apply α)) := by
      rw [Subst.applyCtx_vars_find?, hlookup]; simp [Subst.applyScheme_mono]
    have ht := ih_t _ _ _ hvt hlookup_t
    have hlookup_f : ((S₃.compose (S₂.compose S₁)).applyCtx Γ).vars.find? x
        = some (.mono ((S₃.compose (S₂.compose S₁)).apply α)) := by
      rw [Subst.applyCtx_vars_find?, hlookup]; simp [Subst.applyScheme_mono]
    have hf := ih_f _ _ _ _ hvf hlookup_f
    simp [AExpr.allFvarTy]
    refine ⟨?_, ?_, ?_⟩
    · -- condition: lift through S₂, S₃, S₄, S₅
      conv => rw [show (S₅.compose (S₄.compose (S₃.compose (S₂.compose S₁)))).apply α
        = S₅.apply (S₄.apply (S₃.apply (S₂.apply (S₁.apply α)))) from by
          simp [Subst.apply_compose]]
      exact AExpr.allFvarTy_applyAExpr S₅ (AExpr.allFvarTy_applyAExpr S₄
        (AExpr.allFvarTy_applyAExpr S₃ (AExpr.allFvarTy_applyAExpr S₂ hc)))
    · -- then: lift through S₄, S₅
      conv => rw [show (S₅.compose (S₄.compose (S₃.compose (S₂.compose S₁)))).apply α
        = S₅.apply (S₄.apply (S₃.apply ((S₂.compose S₁).apply α))) from by
          simp [Subst.apply_compose]]
      exact AExpr.allFvarTy_applyAExpr S₅ (AExpr.allFvarTy_applyAExpr S₄ ht)
    · -- else: lift through S₅
      conv => rw [show (S₅.compose (S₄.compose (S₃.compose (S₂.compose S₁)))).apply α
        = S₅.apply (S₄.apply ((S₃.compose (S₂.compose S₁)).apply α)) from by
          simp [Subst.apply_compose]]
      exact AExpr.allFvarTy_applyAExpr S₅ hf
  | case7 Γ n e₁ e₂ ih₁ ih₂ => -- eq
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    obtain ⟨S₂, ae₂, n₂⟩ := v₂
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    dsimp only at hv₂ hS₃
    have h₁ := ih₁ hv₁ hlookup
    have hlookup₂ : (S₁.applyCtx Γ).vars.find? x = some (.mono (S₁.apply α)) := by
      rw [Subst.applyCtx_vars_find?, hlookup]; simp [Subst.applyScheme_mono]
    have h₂ := ih₂ _ _ hv₂ hlookup₂
    simp [AExpr.allFvarTy]
    constructor
    · rw [Subst.apply_compose, Subst.apply_compose]
      exact AExpr.allFvarTy_applyAExpr S₃ (AExpr.allFvarTy_applyAExpr S₂ h₁)
    · rw [Subst.apply_compose, Subst.apply_compose]
      exact AExpr.allFvarTy_applyAExpr S₃ h₂
  | case8 Γ n k body => -- quant
    rename_i ih
    simp only [bind, Except.bind] at hW
    split at hW <;> try contradiction
    split at hW <;> try contradiction
    rename_i _ v₁ hv₁ _ S₂ hS₂
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    dsimp only at hv₁ hS₂
    simp [AExpr.allFvarTy]
    by_cases hzx : body.freshFor = x
    · subst hzx
      exact AExpr.allFvarTy_varClose_same (S₂.applyAExpr ae₁) 0 _ _
    · have hlookup' : (Γ.addVar body.freshFor (.mono (Ty.var n))).vars.find? x
          = some (.mono α) := by
        simp [Ctx.addVar, Map.find?_insert_ne _ _ _ _ hzx, hlookup]
      have h₁ := ih hv₁ hlookup'
      have h₁' := AExpr.allFvarTy_applyAExpr S₂ h₁
      rw [Subst.apply_compose]
      exact AExpr.allFvarTy_varClose_other (S₂.applyAExpr ae₁) h₁' 0
  | case9 => contradiction

/-! ### Main theorem -/

/-
Theorem: If `W Γ e n = .ok (S, ae, n')`, then `HasTypeA [] ae ae.tyOf`.

Proof: By induction on `e` (via `fun_induction` on `W`).

  Case fvar/op: W returns `.fvar τ x` or `.op τ f`. Immediate by `HasTypeA.fvar`/`.op`.

  Case const: W returns `.const c`. Immediate by `HasTypeA.boolc`/`.intc`.

  Case abs body:
    W opens `body` with fresh `x` at type `α`, recurses to get `(S₁, ae₁, n₁)`,
    then returns `.abs (arrow (S₁.apply α) ae₁.tyOf) (ae₁.varClose 0 x)`.
    By IH, `HasTypeA [] ae₁ ae₁.tyOf`.
    By `W_allFvarTy`, every `fvar _ x` in `ae₁` carries annotation `S₁.apply α`.
    By `HasTypeA_varClose_zero`, `HasTypeA [S₁.apply α] (ae₁.varClose 0 x) ae₁.tyOf`.
    Conclude by `HasTypeA.abs`.

  Case app e₁ e₂:
    W infers `e₁ → (S₁, ae₁, n₁)`, `e₂ → (S₂, ae₂, n₂)`, unifies → `S₃`.
    By IH, `HasTypeA [] ae₁ ae₁.tyOf` and `HasTypeA [] ae₂ ae₂.tyOf`.
    Lift through substitutions via `HasTypeA_applyAExpr`:
      `HasTypeA [] (S₃.applyAExpr (S₂.applyAExpr ae₁)) (S₃.apply (S₂.apply ae₁.tyOf))`
      `HasTypeA [] (S₃.applyAExpr ae₂) (S₃.apply ae₂.tyOf)`
    By `unify_sound`, `S₃(S₂(ae₁.tyOf)) = arrow (S₃(ae₂.tyOf)) (S₃(Ty.var n₂))`.
    Rewrite the function type and conclude by `HasTypeA.app`.

  Case ite c t f:
    Lift condition through S₂–S₅ via `HasTypeA_applyAExpr`.
    `unify_sound` on S₂ gives condition type = bool; on S₅ gives then = else type.
    Conclude by `HasTypeA.ite`.

  Case eq e₁ e₂:
    Lift both sides through substitutions. `unify_sound` equates their types.
    Conclude by `HasTypeA.eq`.

  Case quant k body:
    Same pattern as abs: open, recurse, lift through S₂, use `unify_sound`
    to get body type = bool, close with `HasTypeA_varClose_zero`,
    use `apply_compose` to reconcile `S₂(S₁(α))` with `(S₂ ∘ S₁)(α)`.
    Conclude by `HasTypeA.quant`.

  Case bvar: contradiction (W returns error).
-/

theorem W_well_typed (h : W Γ e n = .ok (S, ae, n')) :
    HasTypeA [] ae ae.tyOf := by
  fun_induction W Γ e n generalizing S ae n' with
  | case1 Γ n x => -- fvar
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i σ hlookup
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.tyOf]; exact .fvar
  | case2 Γ n f => -- op
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i σ hlookup
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.tyOf]; exact .op
  | case3 Γ n c => -- const
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases c with
    | bool b => simp [AExpr.tyOf]; exact .boolc
    | int i => simp [AExpr.tyOf]; exact .intc
  | case4 Γ n body α => -- abs
    rename_i x ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i _ v₁ hv₁
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hty₁ := ih hv₁
    have hlookup : (Γ.addVar x (.mono α)).vars.find? x = some (.mono α) := by
      simp [Ctx.addVar, Map.find?_insert_self]
    have hall₁ := W_allFvarTy hv₁ hlookup
    have hclose := HasTypeA_varClose_zero hty₁ hall₁
    simp [AExpr.tyOf]
    exact .abs hclose
  | case5 Γ n e₁ e₂ ih₁ ih₂ => -- app
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    obtain ⟨S₂, ae₂, n₂⟩ := v₂
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only at hv₂ hS₃
    have hty₁ := ih₁ hv₁
    have hty₂ := ih₂ _ _ hv₂
    have hunif := unify_sound hS₃
    -- Lift ae₁ through S₂ then S₃
    have hty₁' := HasTypeA_applyAExpr S₃ (HasTypeA_applyAExpr S₂ hty₁)
    rw [List.map_nil, List.map_nil] at hty₁'
    -- Lift ae₂ through S₃
    have hty₂' := HasTypeA_applyAExpr S₃ hty₂
    rw [List.map_nil] at hty₂'
    -- unify_sound: S₃(S₂(ae₁.tyOf)) = arrow (S₃(ae₂.tyOf)) (S₃(Ty.var n₂))
    rw [Subst.apply_arrow] at hunif
    -- rewrite the fnTy annotation in the goal
    have htyOf : (AExpr.app (S₃.apply (S₂.apply ae₁.tyOf)) (S₃.apply ae₂.tyOf)
                  (S₃.applyAExpr (S₂.applyAExpr ae₁)) (S₃.applyAExpr ae₂)).tyOf =
                 S₃.apply (Ty.var n₂) := by
      show (match S₃.apply (S₂.apply ae₁.tyOf) with
            | .con "→" [_, r] => r | t => t) = _
      rw [hunif]; simp [Ty.arrow]
    rw [htyOf]
    conv in AExpr.app _ _ _ _ => rw [hunif]
    rw [hunif] at hty₁'
    exact .app hty₁' hty₂'
  | case6 Γ n c t f ihc iht ihf => -- ite
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ S₂ hS₂ _ v₃ hv₃ _ v₄ hv₄ _ S₅ hS₅
    obtain ⟨S₁, aec, n₁⟩ := v₁
    obtain ⟨S₃, aet, n₂⟩ := v₃
    obtain ⟨S₄, aef, n₃⟩ := v₄
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only at hv₃ hv₄ hS₂ hS₅
    have htyc := ihc hv₁
    have htyt := iht _ _ _ hv₃
    have htyf := ihf _ _ _ _ hv₄
    have hunif₂ := unify_sound hS₂
    have hunif₅ := unify_sound hS₅
    -- Lift condition through S₂, S₃, S₄, S₅
    have htyc' := HasTypeA_applyAExpr S₅ (HasTypeA_applyAExpr S₄
                    (HasTypeA_applyAExpr S₃ (HasTypeA_applyAExpr S₂ htyc)))
    simp only [List.map_nil] at htyc'
    rw [hunif₂] at htyc'
    simp [Subst.apply, Ty.bool] at htyc'
    -- Lift then through S₄, S₅
    have htyt' := HasTypeA_applyAExpr S₅ (HasTypeA_applyAExpr S₄ htyt)
    simp only [List.map_nil] at htyt'
    rw [hunif₅] at htyt'
    -- Lift else through S₅
    have htyf' := HasTypeA_applyAExpr S₅ htyf
    simp only [List.map_nil] at htyf'
    exact .ite htyc' htyt' htyf'
  | case7 Γ n e₁ e₂ ih₁ ih₂ => -- eq
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    obtain ⟨S₂, ae₂, n₂⟩ := v₂
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only at hv₂ hS₃
    have hty₁ := ih₁ hv₁
    have hty₂ := ih₂ _ _ hv₂
    have hunif := unify_sound hS₃
    -- Lift ae₁ through S₂, S₃
    have hty₁' := HasTypeA_applyAExpr S₃ (HasTypeA_applyAExpr S₂ hty₁)
    simp only [List.map_nil] at hty₁'
    rw [hunif] at hty₁'
    -- Lift ae₂ through S₃
    have hty₂' := HasTypeA_applyAExpr S₃ hty₂
    simp only [List.map_nil] at hty₂'
    exact .eq hty₁' hty₂'
  | case8 Γ n k body => -- quant
    rename_i ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ S₂ hS₂
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only at hv₁ hS₂
    have hty₁ := ih hv₁
    have hunif := unify_sound hS₂
    have hlookup : (Γ.addVar body.freshFor (.mono (Ty.var n))).vars.find? body.freshFor
        = some (.mono (Ty.var n)) := by
      simp [Ctx.addVar, Map.find?_insert_self]
    have hall₁ := W_allFvarTy hv₁ hlookup
    -- Lift through S₂
    have hty₁' := HasTypeA_applyAExpr S₂ hty₁
    simp only [List.map_nil] at hty₁'
    rw [hunif] at hty₁'
    simp [Subst.apply, Ty.bool] at hty₁'
    -- allFvarTy preserved by S₂
    have hall₁' := AExpr.allFvarTy_applyAExpr S₂ hall₁
    -- varClose
    have hclose := HasTypeA_varClose_zero hty₁' hall₁'
    simp [AExpr.tyOf]
    rw [Subst.apply_compose]
    exact .quant hclose
  | case9 => contradiction

#print axioms W_well_typed

end HM
