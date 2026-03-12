/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AlgorithmW
import Strata.Experiment.HM.Erasure
import Strata.Experiment.HM.Freshness
import Strata.Experiment.HM.WellTyped

/-! ## Alternative Soundness via W_well_typed + HasTypeA_implies_HasType

Proves `W_ctxCompat`: if `W Γ e n = .ok (S, ae, n')` then
`ae.ctxCompat (S.applyCtx Γ)`.
-/

namespace HM

---------------------------------------------------------------------
-- Core lemmas: sequential openAll = simultaneous Subst.apply
---------------------------------------------------------------------

-- /-- substVar α r t = t when α ∉ t.freeVars -/
-- private theorem Ty.substVar_not_free (α : Nat) (r : Ty) (t : Ty)
--     (h : α ∉ t.freeVars) : t.substVar α r = t := by
--   induction t using Ty.ind' with
--   | hvar n => simp [Ty.freeVars, Ty.substVar] at *; omega
--   | hcon name args ih =>
--     simp only [Ty.substVar]; congr 1
--     induction args with
--     | nil => rfl
--     | cons a rest ihr =>
--       simp
--       constructor
--       · exact ih a (.head rest) (by
--           intro hmem; apply h; simp [Ty.freeVars]; grind)
--       · specialize (ihr (by grind))
--         simp[Ty.freeVars] at h
--         cases h
--         refine ihr (fun t hm => ih t (.tail a hm)) ?_
--         simp [Ty.freeVars]
--         intro hmem
--         exact h hmem

-- /-- substVar commutes with Subst.apply when α ∉ dom(S) and α ∉ range(S). -/
-- private theorem substVar_apply_comm (α : Nat) (t : Ty) (body : Ty) (S : Subst)
--     (hα_dom : S.find? α = none)
--     (hα_range : α ∉ substFreeVars S) :
--     (S.apply body).substVar α (S.apply t) = S.apply (body.substVar α t) := by
--   sorry

-- /-- Sequential openAll equals simultaneous Subst.apply when:
--     - the subst keys cover all bound vars
--     - the subst keys are exactly the bound vars (each key ∈ vars)
--     - the subst values don't mention any bound var -/
-- private theorem openAll_eq_apply (σ : Scheme) (S : List (Nat × Ty))
--     (hcover : ∀ α ∈ σ.vars, α ∈ S.map Prod.fst)
--     (hkeys : ∀ p ∈ S, p.1 ∈ σ.vars)
--     (hfresh_vals : ∀ p ∈ S, ∀ β ∈ σ.vars, β ∉ (p.2 : Ty).freeVars) :
--     σ.openAll S = Scheme.mono (Subst.apply S σ.body) := by
--   sorry

---------------------------------------------------------------------
-- Instantiation produces an instance
---------------------------------------------------------------------

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
-- Instantiation produces an instance
---------------------------------------------------------------------

/-- `open` either removes the var from vars or is a no-op. -/
private theorem Scheme.vars_open (α : Nat) (τ : Ty) (σ : Scheme) :
    (σ.open α τ).vars = if α ∈ σ.vars then σ.vars.removeAll [α] else σ.vars := by
  simp [Scheme.open]; split <;> simp_all

/-- After `openAll`, any remaining var was in the original and not in the subst keys. -/
private theorem Scheme.openAll_vars_sub (subst : List (Nat × Ty)) (σ : Scheme) :
    ∀ α, α ∈ (σ.openAll subst).vars → α ∈ σ.vars ∧ α ∉ subst.map Prod.fst := by
  induction subst generalizing σ with
  | nil => simp [Scheme.openAll, List.foldl]
  | cons p rest ih =>
    intro α hmem
    simp only [Scheme.openAll, List.foldl] at hmem
    have ⟨h1, h2⟩ := ih _ _ hmem
    simp only [Scheme.vars_open] at h1
    split at h1
    · constructor
      · grind
      · grind
    grind
/-- The mapIdx substitution covers all vars. -/
private theorem mapIdx_covers_vars (vars : List Nat) (n : Nat) :
    ∀ α, α ∈ vars → α ∈ (vars.mapIdx fun i a => (a, Ty.var (n + i))).map Prod.fst := by
  intro α hmem
  simp_all
  have := List.getElem?_of_mem hmem
  grind

theorem instantiate_isInstanceOf (σ : Scheme) (n : Nat) :
    σ.isInstanceOf (σ.instantiate n).1 := by
    sorry
  -- simp only [Scheme.isInstanceOf, Scheme.instantiate]
  -- refine ⟨σ.vars.mapIdx fun i α => (α, Ty.var (n + i)), ?_⟩
  -- apply openAll_eq_apply
  -- · exact mapIdx_covers_vars σ.vars n
  -- · intro p hp; sorry
  -- · intro p hp β hβ; sorry

---------------------------------------------------------------------
-- Substitution preserves isInstanceOf
---------------------------------------------------------------------

-- Subst.freshForScheme is now defined in Freshness.lean

theorem isInstanceOf_applyScheme (S : Subst) (σ : Scheme) (τ : Ty)
    (h : σ.isInstanceOf τ) (hfresh : S.freshForScheme σ) :
    (S.applyScheme σ).isInstanceOf (S.apply τ) := by
  sorry

---------------------------------------------------------------------
-- ctxCompat preserved by applyAExpr + applyCtx
---------------------------------------------------------------------

theorem Subst.applyCtx_ops_find? (S : Subst) (Γ : Ctx) (f : String) :
    (S.applyCtx Γ).ops.find? f = (Γ.ops.find? f).map (S.applyScheme ·) := by
  simp [Subst.applyCtx, Map.find?_fmap]

theorem AExpr.ctxCompat_applyAExpr (S : Subst) (Γ : Ctx) (ae : AExpr)
    (h : ae.ctxCompat Γ)
    (hfresh : ∀ σ, σ ∈ Γ.vars.values ∨ σ ∈ Γ.ops.values → S.freshForScheme σ) :
    (S.applyAExpr ae).ctxCompat (S.applyCtx Γ) := by
  induction ae with
  | bvar _ => trivial
  | fvar t x =>
    simp [Subst.applyAExpr, ctxCompat] at *
    obtain ⟨σ, hfind, hinst⟩ := h
    exact ⟨S.applyScheme σ, by rw [Subst.applyCtx_vars_find?, hfind]; rfl,
           isInstanceOf_applyScheme S σ t hinst
             (hfresh σ (.inl (Map.find?_mem_values _ hfind)))⟩
  | op t f =>
    simp [Subst.applyAExpr, ctxCompat] at *
    obtain ⟨σ, hfind, hinst⟩ := h
    exact ⟨S.applyScheme σ, by rw [Subst.applyCtx_ops_find?, hfind]; rfl,
           isInstanceOf_applyScheme S σ t hinst
             (hfresh σ (.inr (Map.find?_mem_values _ hfind)))⟩
  | const _ => trivial
  | app _ _ _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | abs _ _ ih => exact ih h
  | ite _ _ _ _ ihc iht ihf => exact ⟨ihc h.1, iht h.2.1, ihf h.2.2⟩
  | eq _ _ _ iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | quant _ _ _ ih => exact ih h

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

theorem W_ctxCompat (h : W Γ e n = .ok (S, ae, n'))
    (hbound : Γ.boundVarsBelow n) :
    ae.ctxCompat (S.applyCtx Γ) := by
  fun_induction W Γ e n generalizing S ae n' with
  | case1 Γ n x => -- fvar
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i σ hσ
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.ctxCompat, Subst.applyCtx_id]
    have hfind : Γ.vars.find? x = some σ := by
      revert hσ; simp [Option.elim]; intro h; grind
    exact ⟨σ, hfind, instantiate_isInstanceOf σ n⟩
  | case2 Γ n f => -- op
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i σ hσ
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.ctxCompat, Subst.applyCtx_id]
    have hfind : Γ.ops.find? f = some σ := by
      revert hσ; simp [Option.elim]; intro h; grind
    exact ⟨σ, hfind, instantiate_isInstanceOf σ n⟩
  | case3 Γ n c => -- const
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.ctxCompat]
  | case4 Γ n body α => -- abs
    rename_i x ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i _ v₁ hv₁
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [AExpr.ctxCompat]
    have hbound' : (Γ.addVar x (.mono α)).boundVarsBelow (n + 1) :=
      Ctx.boundVarsBelow_addVar_mono Γ x _ α
        (Ctx.boundVarsBelow_mono Γ n _ hbound (by omega))
    have hcompat₁ := ih hv₁ hbound'
    rw [Subst.applyCtx_addVar, Subst.applyScheme_mono] at hcompat₁
    exact AExpr.ctxCompat_varClose_addVar (Subst.applyCtx S Γ) x _ ae₁ 0 hcompat₁
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
    have hc₁ := ih₁ hv₁ hbound
    have hbound₁ : (S₁.applyCtx Γ).boundVarsBelow n₁ :=
      Ctx.boundVarsBelow_mono _ n n₁
        (Ctx.boundVarsBelow_applyCtx S₁ Γ n hbound) (W_counter_le hv₁)
    have hc₂ := ih₂ _ _ hv₂ hbound₁
    -- Freshness for intermediate substitutions
    have hfresh₂ : S₂.freshForCtx (S₁.applyCtx Γ) := W_freshForCtx hv₂ hbound₁
    have hfreshAll : (S₃.compose (S₂.compose S₁)).freshForCtx Γ := W_freshForCtx h hbound
    have hfresh₃ : S₃.freshForCtx Γ :=
      Subst.freshForCtx_of_compose_right S₃ (S₂.compose S₁) Γ hfreshAll
    simp [AExpr.ctxCompat]
    constructor
    · have := AExpr.ctxCompat_applyAExpr S₃ _ _
        (AExpr.ctxCompat_applyAExpr S₂ _ _ hc₁ hfresh₂)
        (Subst.freshForCtx_applyCtx S₂ S₃ (S₁.applyCtx Γ)
          (Subst.freshForCtx_applyCtx S₁ S₃ Γ hfresh₃))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.compose_assoc] at this
    · have := AExpr.ctxCompat_applyAExpr S₃ _ _ hc₂
        (Subst.freshForCtx_applyCtx S₂ S₃ (S₁.applyCtx Γ)
          (Subst.freshForCtx_applyCtx S₁ S₃ Γ hfresh₃))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.compose_assoc] at this
  | case6 Γ n c t f ihc iht ihf => -- ite
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ vc hvc _ S₂ hS₂ _ vt hvt _ vf hvf _ S₅ hS₅
    obtain ⟨S₁, aec, n₁⟩ := vc
    obtain ⟨S₃, aet, n₂⟩ := vt
    obtain ⟨S₄, aef, n₃⟩ := vf
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only at hvc hS₂ hvt hvf hS₅
    -- boundVarsBelow for intermediate contexts
    have hbS₂S₁ : ((S₂.compose S₁).applyCtx Γ).boundVarsBelow n₁ :=
      Ctx.boundVarsBelow_mono _ n n₁
        (Ctx.boundVarsBelow_applyCtx _ Γ n hbound) (W_counter_le hvc)
    have hbS₃S₂S₁ : ((S₃.compose (S₂.compose S₁)).applyCtx Γ).boundVarsBelow n₂ :=
      Ctx.boundVarsBelow_mono _ n n₂
        (Ctx.boundVarsBelow_applyCtx _ Γ n hbound)
        (Nat.le_trans (W_counter_le hvc) (W_counter_le hvt))
    have hcc := ihc hvc hbound
    have hct := iht _ _ _ hvt hbS₂S₁
    have hcf := ihf _ _ _ _ hvf hbS₃S₂S₁
    -- Overall freshness and decomposition
    have hfreshAll := W_freshForCtx h hbound
    have hfresh₅ : S₅.freshForCtx Γ :=
      Subst.freshForCtx_of_compose_right S₅ _ Γ hfreshAll
    have hfresh₄ : S₄.freshForCtx Γ :=
      Subst.freshForCtx_of_compose_right S₄ _ Γ
        (Subst.freshForCtx_of_compose_right (S₅.compose S₄) _ Γ hfreshAll)
    have hfresh₃ : S₃.freshForCtx Γ := W_freshForCtx hvt hbS₂S₁
    have hfresh₂ : S₂.freshForCtx Γ :=
      Subst.freshForCtx_of_compose_right S₂ S₁ Γ
        (Subst.freshForCtx_of_compose_right (S₂.compose S₁) _ Γ
          (Subst.freshForCtx_of_compose_right (S₃.compose (S₂.compose S₁)) _ Γ
            (Subst.freshForCtx_of_compose_right (S₄.compose (S₃.compose (S₂.compose S₁))) _ Γ
              hfreshAll)))
    -- Helper: lift freshForCtx through applyCtx chains
    have fc₂ := Subst.freshForCtx_applyCtx S₁ S₂ Γ hfresh₂
    have fc₃ := Subst.freshForCtx_applyCtx S₁ S₃ Γ hfresh₃
    have fc₄ := Subst.freshForCtx_applyCtx S₁ S₄ Γ hfresh₄
    have fc₅ := Subst.freshForCtx_applyCtx S₁ S₅ Γ hfresh₅
    simp [AExpr.ctxCompat]
    refine ⟨?_, ?_, ?_⟩
    · have := AExpr.ctxCompat_applyAExpr S₅ _ _
        (AExpr.ctxCompat_applyAExpr S₄ _ _
          (AExpr.ctxCompat_applyAExpr S₃ _ _
            (AExpr.ctxCompat_applyAExpr S₂ _ _ hcc fc₂)
            (Subst.freshForCtx_applyCtx S₂ S₃ _ fc₃))
          (Subst.freshForCtx_applyCtx S₃ S₄ _ (Subst.freshForCtx_applyCtx S₂ S₄ _ fc₄)))
        (Subst.freshForCtx_applyCtx S₄ S₅ _
          (Subst.freshForCtx_applyCtx S₃ S₅ _
            (Subst.freshForCtx_applyCtx S₂ S₅ _ fc₅)))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.applyCtx_compose,
           Subst.applyCtx_compose, Subst.compose_assoc, Subst.compose_assoc,
           Subst.compose_assoc] at this
    · have := AExpr.ctxCompat_applyAExpr S₅ _ _
        (AExpr.ctxCompat_applyAExpr S₄ _ _ hct
          (Subst.freshForCtx_applyCtx S₃ S₄ _
            (Subst.freshForCtx_applyCtx S₂ S₄ _ fc₄)))
        (Subst.freshForCtx_applyCtx S₄ S₅ _
          (Subst.freshForCtx_applyCtx S₃ S₅ _
            (Subst.freshForCtx_applyCtx S₂ S₅ _ fc₅)))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.applyCtx_compose,
           Subst.compose_assoc, Subst.compose_assoc] at this
    · have := AExpr.ctxCompat_applyAExpr S₅ _ _ hcf
        (Subst.freshForCtx_applyCtx S₄ S₅ _
          (Subst.freshForCtx_applyCtx S₃ S₅ _
            (Subst.freshForCtx_applyCtx S₂ S₅ _ fc₅)))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.compose_assoc] at this
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
    have hc₁ := ih₁ hv₁ hbound
    have hbound₁ : (S₁.applyCtx Γ).boundVarsBelow n₁ :=
      Ctx.boundVarsBelow_mono _ n n₁
        (Ctx.boundVarsBelow_applyCtx S₁ Γ n hbound) (W_counter_le hv₁)
    have hc₂ := ih₂ _ _ hv₂ hbound₁
    have hfresh₂ : S₂.freshForCtx (S₁.applyCtx Γ) := W_freshForCtx hv₂ hbound₁
    have hfreshAll : (S₃.compose (S₂.compose S₁)).freshForCtx Γ := W_freshForCtx h hbound
    have hfresh₃ : S₃.freshForCtx Γ :=
      Subst.freshForCtx_of_compose_right S₃ (S₂.compose S₁) Γ hfreshAll
    simp [AExpr.ctxCompat]
    constructor
    · have := AExpr.ctxCompat_applyAExpr S₃ _ _
        (AExpr.ctxCompat_applyAExpr S₂ _ _ hc₁ hfresh₂)
        (Subst.freshForCtx_applyCtx S₂ S₃ (S₁.applyCtx Γ)
          (Subst.freshForCtx_applyCtx S₁ S₃ Γ hfresh₃))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.compose_assoc] at this
    · have := AExpr.ctxCompat_applyAExpr S₃ _ _ hc₂
        (Subst.freshForCtx_applyCtx S₂ S₃ (S₁.applyCtx Γ)
          (Subst.freshForCtx_applyCtx S₁ S₃ Γ hfresh₃))
      rwa [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.compose_assoc] at this
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
    simp [AExpr.ctxCompat]
    have hbound' : (Γ.addVar body.freshFor (.mono (Ty.var n))).boundVarsBelow (n + 1) :=
      Ctx.boundVarsBelow_addVar_mono Γ body.freshFor _ _
        (Ctx.boundVarsBelow_mono Γ n _ hbound (by omega))
    have hcompat₁ := ih hv₁ hbound'
    rw [Subst.applyCtx_addVar, Subst.applyScheme_mono] at hcompat₁
    -- Freshness for S₂
    have hfreshAll : (S₂.compose S₁).freshForCtx Γ := W_freshForCtx h hbound
    have hfresh₂ : S₂.freshForCtx Γ :=
      Subst.freshForCtx_of_compose_right S₂ S₁ Γ hfreshAll
    have hfresh₂' : S₂.freshForCtx (S₁.applyCtx (Γ.addVar body.freshFor (.mono (Ty.var n)))) :=
      Subst.freshForCtx_applyCtx S₁ S₂ _
        (Subst.freshForCtx_addVar_mono S₂ Γ body.freshFor _ hfresh₂)
    have hcompat₁' := AExpr.ctxCompat_applyAExpr S₂ _ _ hcompat₁ hfresh₂'
    rw [Subst.applyCtx_addVar, Subst.applyScheme_mono, Subst.applyCtx_compose] at hcompat₁'
    exact AExpr.ctxCompat_varClose_addVar _ body.freshFor _ _ 0 hcompat₁'
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

theorem W_sound_alt (h : W Γ e n = .ok (S, ae, n'))
    (hbound : Γ.boundVarsBelow n) :
    ae.erase = e ∧ HasType (S.applyCtx Γ) e (Scheme.mono ae.tyOf) := by
  have herase := W_erase h
  have htyA   := W_well_typed h
  have hcompat := W_ctxCompat h hbound
  have hty    := HasTypeA_implies_HasType ae ae.tyOf (S.applyCtx Γ) htyA hcompat
  exact ⟨herase, herase ▸ hty⟩

end HM
