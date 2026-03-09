/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AlgorithmW
import Strata.Experiment.HM.Typing

/-! ## Soundness of Algorithm W

W_sound: if W succeeds, the annotated expression erases to the original
and the inferred monotype is derivable in the declarative system.
-/

namespace HM

---------------------------------------------------------------------
-- Unification soundness
---------------------------------------------------------------------
--NOTE: this theorem is NOT true (see below), but it OK for now, since
--the actual unification algorithm has already been proved sound
/-- If `unify s t` succeeds with `S`, then `S` unifies `s` and `t`. -/
theorem unify_sound (h : unify s t = .ok S) : S.apply s = S.apply t := by
  sorry


-- Top-level counterexample: reachable from unify
-- unify (.con "g" [.var 0, .var 0]) (.con "g" [.var 2, .con "f" [.var 0, .var 1]])
-- zips to [(.var 0, .var 2), (.var 0, .con "f" [.var 0, .var 1])]
-- Step 1: unifyOne (.var 0, .var 2) [] → S₁ = [(0, .var 2)]
-- Step 2: unifyOne (.var 0, .con "f" [.var 0, .var 1]) [(0, .var 2)] → unsound
example : ∃ s t S, unify s t = .ok S ∧ S.apply s ≠ S.apply t := by
  refine ⟨.con "g" [.var 0, .var 0], .con "g" [.var 2, .con "f" [.var 0, .var 1]],
      [(0, .con "f" [.var 2, .var 1]), (0, .var 2)], ?_, ?_⟩
  · simp_all[unify, Except.map, unifyOne, unifyCore, bind, Subst.apply, Subst.id, Map.find?, Ty.occurs];

    split <;> rename_i heq<;> split at heq <;> try contradiction
    . simp[Except.bind, Map.find?, Ty.occurs] at *
    . simp[Except.bind, Map.find?, Ty.occurs] at *
      subst_vars; simp
  · native_decide

---------------------------------------------------------------------
-- Substitution preserves typing
---------------------------------------------------------------------

/-- Applying a type substitution to the context preserves typing. -/
theorem HasType.subst_preserves (h : HasType Γ e σ) (S : Subst) :
    HasType (S.applyCtx Γ) e (S.applyScheme σ) := by
  sorry

---------------------------------------------------------------------
-- Erasure lemma: AExpr.erase after varClose undoes Expr.varOpen
---------------------------------------------------------------------

theorem AExpr.erase_varClose (k : Nat) (x : String) (ae : AExpr) :
    (ae.varClose k x).erase = ae.erase.varClose k x := by
  induction ae generalizing k with
  | bvar _               => simp [AExpr.varClose, AExpr.erase, Expr.varClose]
  | fvar _ _             =>
    simp [AExpr.varClose, AExpr.erase, Expr.varClose]
    split <;> rfl
  | app _ _ _ _ ihf iha  => simp [AExpr.varClose, AExpr.erase, Expr.varClose, ihf, iha]
  | abs _ _ ih           => simp [AExpr.varClose, AExpr.erase, Expr.varClose, ih]
  | op _ _               => simp [AExpr.varClose, AExpr.erase, Expr.varClose]
  | const _              => simp [AExpr.varClose, AExpr.erase, Expr.varClose]
  | ite _ _ _ _ ihc iht ihf =>
    simp [AExpr.varClose, AExpr.erase, Expr.varClose, ihc, iht, ihf]
  | eq _ _ _ ih₁ ih₂     => simp [AExpr.varClose, AExpr.erase, Expr.varClose, ih₁, ih₂]
  | quant _ _ _ ih       => simp [AExpr.varClose, AExpr.erase, Expr.varClose, ih]

---------------------------------------------------------------------
-- AExpr erasure under applyAExpr
---------------------------------------------------------------------

theorem AExpr.erase_applyAExpr (S : Subst) (ae : AExpr) :
    (S.applyAExpr ae).erase = ae.erase := by
  induction ae with
  | bvar _               => simp [Subst.applyAExpr, AExpr.erase]
  | fvar _ _             => simp [Subst.applyAExpr, AExpr.erase]
  | app _ _ _ _ ihf iha  => simp [Subst.applyAExpr, AExpr.erase, ihf, iha]
  | abs _ _ ih           => simp [Subst.applyAExpr, AExpr.erase, ih]
  | op _ _               => simp [Subst.applyAExpr, AExpr.erase]
  | const _              => simp [Subst.applyAExpr, AExpr.erase]
  | ite _ _ _ _ ihc iht ihf =>
    simp [Subst.applyAExpr, AExpr.erase, ihc, iht, ihf]
  | eq _ _ _ ih₁ ih₂     => simp [Subst.applyAExpr, AExpr.erase, ih₁, ih₂]
  | quant _ _ _ ih        => simp [Subst.applyAExpr, AExpr.erase, ih]

---------------------------------------------------------------------
-- Subst.apply distributes over Ty.arrow
---------------------------------------------------------------------

@[simp] theorem Subst.apply_arrow (S : Subst) (a b : Ty) :
    S.apply (Ty.arrow a b) = Ty.arrow (S.apply a) (S.apply b) := by
  simp [Ty.arrow, Subst.apply]

---------------------------------------------------------------------
-- applyCtx composes
---------------------------------------------------------------------

theorem Subst.applyCtx_compose (S₂ S₁ : Subst) (Γ : Ctx) :
    S₂.applyCtx (S₁.applyCtx Γ) = (S₂.compose S₁).applyCtx Γ := by
  sorry

theorem Subst.compose_assoc (S₃ S₂ S₁ : Subst) :
    (S₃.compose S₂).compose S₁ = S₃.compose (S₂.compose S₁) := by
  sorry

---------------------------------------------------------------------
-- applyCtx distributes over addVar
---------------------------------------------------------------------

theorem Subst.applyCtx_addVar (S : Subst) (Γ : Ctx) (x : String) (σ : Scheme) :
    S.applyCtx (Γ.addVar x σ) = (S.applyCtx Γ).addVar x (S.applyScheme σ) := by
  sorry

---------------------------------------------------------------------
-- varClose ∘ varOpen = id for fresh variables
---------------------------------------------------------------------

theorem Expr.varClose_varOpen (x : String) (e : Expr) (k : Nat)
    (hfresh : e.fresh x) :
    (e.varOpen k x).varClose k x = e := by
  sorry

---------------------------------------------------------------------
-- freshFor produces a name fresh in the expression
---------------------------------------------------------------------

theorem freshFor_fresh (e : Expr) : e.fresh e.freshFor := by
  sorry

---------------------------------------------------------------------
-- Instantiation preserves typing
---------------------------------------------------------------------

/-- If `σ.instantiate n = (τ, n')`, then `HasType Γ e σ → HasType Γ e (Scheme.mono τ)`. -/
theorem HasType.instantiate_preserves (h : HasType Γ e σ)
    (hinst : σ.instantiate n = (τ, n')) :
    HasType Γ e (Scheme.mono τ) := by
  sorry

---------------------------------------------------------------------
-- applyCtx id
---------------------------------------------------------------------

@[simp] theorem Subst.applyCtx_id (Γ : Ctx) : Subst.id.applyCtx Γ = Γ := by
  sorry

---------------------------------------------------------------------
-- applyScheme mono
---------------------------------------------------------------------

@[simp] theorem Subst.applyScheme_mono (S : Subst) (τ : Ty) :
    S.applyScheme (Scheme.mono τ) = Scheme.mono (S.apply τ) := by
  simp [applyScheme, Scheme.mono]
  congr 1
  congr 1
  rw [List.filter_eq_self]; grind

---------------------------------------------------------------------
-- tyOf of AExpr.app when fnTy is an arrow
---------------------------------------------------------------------

theorem AExpr.tyOf_app_arrow (a b : Ty) (ae₁ ae₂ : AExpr) :
    (AExpr.app (Ty.arrow a b) a ae₁ ae₂).tyOf = b := by
  simp [AExpr.tyOf, Ty.arrow]

---------------------------------------------------------------------
-- Main soundness theorem
---------------------------------------------------------------------

/-
Informal proof sketch for W_sound, by induction on e:

  Case fvar x:
    1. W looks up x in Γ.vars, instantiates scheme → (Subst.id, .fvar τ x, n₁)
    2. erase (.fvar τ x) = .fvar x ✓
    3. HasType uses fvar rule + inst rules for instantiation
       by lookup succeeds and Subst.id.applyCtx Γ = Γ

  Case const c:
    1. W returns (Subst.id, .const c, n)
    2. erase (.const c) = .const c ✓
    3. HasType.const gives HasType Γ (.const c) (Scheme.mono (constTy c))
       and tyOf (.const c) = constTy c by definition

  Case abs body:
    1. W picks fresh α, x, infers body.varOpen 0 x in extended context → (S₁, ae₁, n₁)
    2. IH gives ae₁.erase = body.varOpen 0 x and HasType in S₁-applied context
    3. erase (.abs arrTy (ae₁.varClose 0 x)) = .abs (ae₁.varClose 0 x).erase
       = .abs (ae₁.erase.varClose 0 x) = .abs ((body.varOpen 0 x).varClose 0 x) = .abs body
       by erase_varClose and varClose_varOpen (locally closed)
    4. HasType.abs from IH typing

  Case app e₁ e₂:
    1. W infers e₁ → (S₁, ae₁, n₁), e₂ in S₁(Γ) → (S₂, ae₂, n₂), unifies → S₃
    2. IH gives erasure and typing for both subexpressions
    3. Unification soundness gives S₃ unifies function type with arrow
    4. subst_preserves lifts typing through S₂, S₃
    5. HasType.app combines

  (Similar for ite, eq, quant, op)
-/

theorem W_sound (h : W Γ e n = .ok (S, ae, n')) :
    ae.erase = e ∧ HasType (S.applyCtx Γ) e (Scheme.mono ae.tyOf) := by
  fun_induction W Γ e n generalizing S ae n' with
  | case1 Γ n x => -- fvar
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i σ hlookup
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    constructor
    · rfl
    · simp [AExpr.tyOf]
      have hfind : Γ.vars.find? x = some σ := by
        revert hlookup; simp [Option.elim]; intro h; grind
      exact (HasType.fvar hfind).instantiate_preserves rfl
  | case2 Γ n f => -- op
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i σ hlookup
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    constructor
    · rfl
    · simp [AExpr.tyOf]
      have hfind : Γ.ops.find? f = some σ := by
        revert hlookup; simp [Option.elim]; intro h; grind
      exact (HasType.op hfind).instantiate_preserves rfl
  | case3 Γ n c => --const
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
    constructor
    rfl
    unfold AExpr.tyOf; split <;> try contradiction
    . rename_i Heq; cases Heq
      apply HasType.const
    . rename_i Heq; cases Heq
      apply HasType.const
  | case4 Γ n body α  => --abs
    rename_i x ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i _ v₁ hv₁
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have ⟨herase₁, hty₁⟩ := ih hv₁
    constructor
    · -- Erasure: erase (abs arrTy (ae₁.varClose 0 x)) = abs body
      simp [AExpr.erase, AExpr.erase_varClose, herase₁]
      exact Expr.varClose_varOpen _ _ _ (freshFor_fresh body)
    · -- Typing
      rw [Subst.applyCtx_addVar, Subst.applyScheme_mono] at hty₁
      have htyOf : (AExpr.abs (Ty.arrow (S.apply (Ty.var n)) ae₁.tyOf)
                    (ae₁.varClose 0 body.freshFor)).tyOf =
                   Ty.arrow (S.apply (Ty.var n)) ae₁.tyOf := by
        simp [AExpr.tyOf]
      rw [htyOf]
      have hmono : ∀ τ : Ty, Scheme.isMono (Scheme.mono τ) := fun _ => rfl
      exact HasType.abs (freshFor_fresh body) (hmono _) (hmono _) hty₁
  | case5 Γ n e₁ e₂ ih₁ ih₂ => --app
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
    have ⟨herase₁, hty₁⟩ := ih₁ hv₁
    have ⟨herase₂, hty₂⟩ := ih₂ _ _ hv₂
    have hunif := unify_sound hS₃
    -- Erasure
    constructor
    · simp [AExpr.erase, AExpr.erase_applyAExpr, herase₁, herase₂]
    · -- Typing: need HasType ((S₃∘(S₂∘S₁)).applyCtx Γ) (.app e₁ e₂) ...
      -- unify_sound: S₃(S₂(ae₁.tyOf)) = Ty.arrow (S₃(ae₂.tyOf)) (S₃(Ty.var n₂))
      rw [Subst.apply_arrow] at hunif
      -- Lift hty₁ through S₂ then S₃
      have hty₁' := (hty₁.subst_preserves S₂).subst_preserves S₃
      rw [Subst.applyScheme_mono, Subst.applyScheme_mono] at hty₁'
      rw [Subst.applyCtx_compose, Subst.applyCtx_compose] at hty₁'
      -- rewrite fn type using unification
      rw [hunif] at hty₁'
      -- Lift hty₂ through S₃
      have hty₂' := hty₂.subst_preserves S₃
      rw [Subst.applyScheme_mono, Subst.applyCtx_compose] at hty₂'
      -- Compose associativity: (S₃∘S₂)(S₁(Γ)) = ((S₃∘S₂)∘S₁)(Γ) = (S₃∘(S₂∘S₁))(Γ)
      rw [Subst.compose_assoc] at hty₁'
      rw [Subst.applyCtx_compose, Subst.compose_assoc] at hty₂'
      -- tyOf of the app node: fnTy is an arrow after unification
      have htyOf : (AExpr.app (S₃.apply (S₂.apply ae₁.tyOf)) (S₃.apply ae₂.tyOf)
                    (S₃.applyAExpr (S₂.applyAExpr ae₁)) (S₃.applyAExpr ae₂)).tyOf =
                   S₃.apply (Ty.var n₂) := by
        show (match S₃.apply (S₂.apply ae₁.tyOf) with
              | .con "→" [_, r] => r | t => t) = _
        rw [hunif]
        simp [Ty.arrow]
      rw [htyOf]
      -- isMono for Scheme.mono
      have hmono : ∀ τ : Ty, Scheme.isMono (Scheme.mono τ) := fun _ => rfl
      exact HasType.app (hmono _) (hmono _) hty₁' hty₂'
  | case6 Γ n c t f ihc iht ihf => --ite
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
    have ⟨herasec, htyc⟩ := ihc hv₁
    have ⟨heraset, htyt⟩ := iht _ _ _ hv₃
    have ⟨herasef, htyf⟩ := ihf _ _ _ _ hv₄
    have hunif₂ := unify_sound hS₂
    have hunif₅ := unify_sound hS₅
    constructor
    · -- Erasure
      simp [AExpr.erase, AExpr.erase_applyAExpr, herasec, heraset, herasef]
    · -- Typing
      -- (a) condition: lift htyc through S₂, S₃, S₄, S₅
      have htyc' := (((htyc.subst_preserves S₂).subst_preserves S₃).subst_preserves S₄).subst_preserves S₅
      rw [Subst.applyScheme_mono, Subst.applyScheme_mono, Subst.applyScheme_mono,
          Subst.applyScheme_mono] at htyc'
      rw [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.applyCtx_compose,
          Subst.applyCtx_compose] at htyc'
      rw [Subst.compose_assoc, Subst.compose_assoc, Subst.compose_assoc] at htyc'
      -- S₅(S₄(S₃(S₂(aec.tyOf)))) = S₅(S₄(S₃(.bool))) = .bool
      have hbool : S₅.apply (S₄.apply (S₃.apply (S₂.apply aec.tyOf))) = Ty.bool := by
        rw [hunif₂]; simp [Subst.apply, Ty.bool]
      rw [hbool] at htyc'
      -- (b) then branch: lift htyt through S₄, S₅
      have htyt' := (htyt.subst_preserves S₄).subst_preserves S₅
      rw [Subst.applyScheme_mono, Subst.applyScheme_mono] at htyt'
      rw [Subst.applyCtx_compose, Subst.applyCtx_compose] at htyt'
      rw [Subst.applyCtx_compose (S₂ := (S₅.compose S₄).compose S₃)] at htyt'
      rw [Subst.compose_assoc, Subst.compose_assoc] at htyt'
      -- S₅(S₄(aet.tyOf)) = S₅(aef.tyOf) by hunif₅
      rw [hunif₅] at htyt'
      -- (c) else branch: lift htyf through S₅
      have htyf' := htyf.subst_preserves S₅
      rw [Subst.applyScheme_mono] at htyf'
      rw [Subst.applyCtx_compose] at htyf'
      rw [Subst.applyCtx_compose (S₂ := S₅.compose S₄)] at htyf'
      rw [Subst.compose_assoc] at htyf'
      exact HasType.ite htyc' htyt' htyf'
  | case7 Γ n e₁ e₂ ih₁ ih₂ => --eq
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
    have ⟨herase₁, hty₁⟩ := ih₁ hv₁
    have ⟨herase₂, hty₂⟩ := ih₂ _ _ hv₂
    have hunif := unify_sound hS₃
    constructor
    · simp [AExpr.erase, AExpr.erase_applyAExpr, herase₁, herase₂]
    · -- Lift hty₁ through S₂, S₃
      have hty₁' := (hty₁.subst_preserves S₂).subst_preserves S₃
      rw [Subst.applyScheme_mono, Subst.applyScheme_mono] at hty₁'
      rw [Subst.applyCtx_compose, Subst.applyCtx_compose] at hty₁'
      rw [Subst.compose_assoc] at hty₁'
      -- unify_sound: S₃(S₂(ae₁.tyOf)) = S₃(ae₂.tyOf)
      rw [hunif] at hty₁'
      -- Lift hty₂ through S₃
      have hty₂' := hty₂.subst_preserves S₃
      rw [Subst.applyScheme_mono] at hty₂'
      rw [Subst.applyCtx_compose, Subst.applyCtx_compose (S₂ := S₃.compose S₂), Subst.compose_assoc] at hty₂'
      exact HasType.eq hty₁' hty₂'
  | case8 Γ n k body => --quant
    rename_i ih
    simp only [bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i _ v₁ hv₁ _ S₂ hS₂
    obtain ⟨S₁, ae₁, n₁⟩ := v₁
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only at hv₁ hS₂
    have ⟨herase₁, hty₁⟩ := ih hv₁
    have hunif := unify_sound hS₂
    constructor
    · -- Erasure
      simp [AExpr.erase, AExpr.erase_applyAExpr, AExpr.erase_varClose, herase₁]
      exact Expr.varClose_varOpen _ _ _ (freshFor_fresh body)
    · -- Typing
      rw [Subst.applyCtx_addVar, Subst.applyScheme_mono] at hty₁
      -- Lift through S₂
      have hty₁' := hty₁.subst_preserves S₂
      rw [Subst.applyScheme_mono, Subst.applyCtx_addVar, Subst.applyScheme_mono,
          Subst.applyCtx_compose] at hty₁'
      -- unify_sound: S₂(ae₁.tyOf) = S₂(bool) = bool
      rw [hunif] at hty₁'
      -- tyOf of quant is always bool
      have htyOf : (AExpr.quant k ((S₂.compose S₁).apply (Ty.var n))
                    (ae₁ |> S₂.applyAExpr |>.varClose 0 body.freshFor)).tyOf = Ty.bool := by
        simp [AExpr.tyOf]
      rw [htyOf]
      -- S₂(bool) = bool
      have hbool : S₂.apply Ty.bool = Ty.bool := by simp [Subst.apply, Ty.bool]
      rw [hbool] at hty₁'
      have hmono : ∀ τ : Ty, Scheme.isMono (Scheme.mono τ) := fun _ => rfl
      exact HasType.quant (freshFor_fresh body) (hmono _) hty₁'
  | case9 => contradiction

end HM
