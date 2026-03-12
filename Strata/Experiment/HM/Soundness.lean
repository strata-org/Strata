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
-- Substitution preserves typing
---------------------------------------------------------------------

-- /-- Applying a type substitution to the context preserves typing. -/
-- theorem HasType.subst_preserves (h : HasType Γ e σ) (S : Subst) :
--     HasType (S.applyCtx Γ) e (S.applyScheme σ) := by
--   sorry

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

theorem AExpr.erase_varOpen (k : Nat) (ty : Ty) (x : String) (ae : AExpr) :
    (ae.varOpen k ty x).erase = ae.erase.varOpen k x := by
  induction ae generalizing k with
  | bvar n               => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen]; split <;> rfl
  | fvar _ _             => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen]
  | app _ _ _ _ ihf iha  => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen, ihf, iha]
  | abs _ _ ih           => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen, ih]
  | op _ _               => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen]
  | const _              => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen]
  | ite _ _ _ _ ihc iht ihf =>
    simp [AExpr.varOpen, AExpr.erase, Expr.varOpen, ihc, iht, ihf]
  | eq _ _ _ ih₁ ih₂     => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen, ih₁, ih₂]
  | quant _ _ _ ih       => simp [AExpr.varOpen, AExpr.erase, Expr.varOpen, ih]

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

theorem Map.find?_app [DecidableEq k] { l1 l2: Map k v}: Map.find? ( @HAppend.hAppend (List (k × v)) (List (k × v)) _ _ l1 l2) x =
  match (Map.find? l1 x) with
  | some y => some y
  | none => Map.find? l2 x := by
  induction l1 with
  | nil =>
    simp[Map.find?]
  | cons h t IH =>
    -- have : (@HAppend.hAppend (Map k v) (Map k v) _ _ (h :: t) l2) = h ::  (@HAppend.hAppend (Map k v) (Map k v) _ _ t l2) := by
    --   rfl
    -- rw[this]
    simp[Map.find?]
    split
    . subst_vars; rfl
    . apply IH

-- If S is fresh for σ, then applying S (filtered) to σ.body
-- produces a type with no free vars in σ.vars
theorem Subst.apply_freeVars_fresh (S : Subst) (σ : Scheme)
    (hfresh : ∀ α ∈ σ.vars, α ∉ substFreeVars S) :
    ∀ v, v ∈ (Subst.apply (S.filter (fun (p: Nat × Ty) => decide (p.fst ∉ σ.vars))) σ.body).freeVars →
         v ∉ σ.vars := by
  sorry

-- General case with freshness precondition
theorem Subst.applyScheme_compose' (S₂ S₁ : Subst) (σ : Scheme) :
    S₂.applyScheme (S₁.applyScheme σ) = (S₂.compose S₁).applyScheme σ := by
  sorry

theorem Map.fmap_fmap (f : β → γ) (g : γ → δ) (m : Map α β) :
    (m.fmap f).fmap g = m.fmap (g ∘ f) := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    exact congrArg ((hd.fst, g (f hd.snd)) :: ·) ih

theorem Subst.applyCtx_compose (S₂ S₁ : Subst) (Γ : Ctx) :
    S₂.applyCtx (S₁.applyCtx Γ) = (S₂.compose S₁).applyCtx Γ := by
  simp only [Subst.applyCtx]
  have h := fun σ => Subst.applyScheme_compose' S₂ S₁ σ
  have hv : (Map.fmap (S₂.applyScheme ·) (Map.fmap (S₁.applyScheme ·) Γ.vars)) =
            Map.fmap ((S₂.compose S₁).applyScheme ·) Γ.vars := by
    rw [Map.fmap_fmap]; exact congrArg (Map.fmap · Γ.vars) (funext h)
  have ho : (Map.fmap (S₂.applyScheme ·) (Map.fmap (S₁.applyScheme ·) Γ.ops)) =
            Map.fmap ((S₂.compose S₁).applyScheme ·) Γ.ops := by
    rw [Map.fmap_fmap]; exact congrArg (Map.fmap · Γ.ops) (funext h)
  exact Ctx.mk.injEq .. |>.mpr ⟨hv, ho⟩


theorem Map.fmap_append (f : β → γ) (m₁ m₂ : Map α β) :
    (m₁ ++ m₂).fmap f = m₁.fmap f ++ m₂.fmap f := by
  induction m₁ with
  | nil => rfl
  | cons hd tl ih =>
    exact congrArg ((hd.fst, f hd.snd) :: ·) ih

theorem Map.find?_fmap' [DecidableEq α] (f : β → γ) (m : Map α β) (a : α) :
    (m.fmap f).find? a = (m.find? a).map f := by
  induction m with
  | nil => simp [Map.fmap, Map.find?]
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [Map.fmap, List.map_cons, Map.find?]
    split
    · simp
    · exact ih

theorem Map.find?_append' [DecidableEq α] (m₁ m₂ : Map α β) (a : α) :
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
    simp [Option.or]

theorem Subst.apply_compose (S₂ S₁ : Subst) (τ : Ty) :
    (S₂.compose S₁).apply τ = S₂.apply (S₁.apply τ) := by
  induction τ using Ty.ind' with
  | hvar n =>
    simp only [Subst.apply, Subst.compose, Map.find?_append', Map.find?_fmap']
    cases S₁.find? n with
    | none => simp [Option.or, Option.map, Subst.apply]
    | some τ => simp [Option.or, Option.map]
  | hcon name args ih =>
    simp only [Subst.apply, List.attach_map_val]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro t ht
    exact ih t ht

theorem Subst.compose_assoc (S₃ S₂ S₁ : Subst) :
    (S₃.compose S₂).compose S₁ = S₃.compose (S₂.compose S₁) := by
  simp only [Subst.compose]
  rw [Map.fmap_append]
  have : Map.fmap (S₃.apply ·) (Map.fmap (S₂.apply ·) S₁) =
         Map.fmap ((S₃.apply ·) ∘ (S₂.apply ·)) S₁ := Map.fmap_fmap _ _ _
  rw [this, List.append_assoc]
  congr 1
  apply List.map_congr_left
  intro ⟨k, v⟩ _
  simp [Function.comp, ←Subst.apply_compose]
  rfl

---------------------------------------------------------------------
-- applyCtx distributes over addVar
---------------------------------------------------------------------

theorem Map.fmap_insert [DecidableEq α] (f : β → γ) (m : Map α β) (k : α) (v : β) :
    (m.insert k v).fmap f = (m.fmap f).insert k (f v) := by
  induction m with
  | nil => simp [Map.insert, Map.fmap]
  | cons hd tl ih =>
    simp [Map.insert, Map.fmap]
    split <;> simp
    congr

theorem Subst.applyCtx_addVar (S : Subst) (Γ : Ctx) (x : String) (σ : Scheme) :
    S.applyCtx (Γ.addVar x σ) = (S.applyCtx Γ).addVar x (S.applyScheme σ) := by
    simp [Subst.applyCtx, Ctx.addVar, Map.fmap_insert]

---------------------------------------------------------------------
-- varClose ∘ varOpen = id for fresh variables
---------------------------------------------------------------------

theorem Expr.varClose_varOpen (x : String) (e : Expr) (k : Nat)
    (hfresh : e.fresh x) :
    (e.varOpen k x).varClose k x = e := by
  induction e generalizing k with
  | bvar n =>
    simp [Expr.varOpen]
    split <;> simp_all [Expr.varClose]
  | fvar y =>
    simp [Expr.fresh] at hfresh
    simp [Expr.varOpen, Expr.varClose, hfresh]
  | app e₁ e₂ ih₁ ih₂ =>
    simp [Expr.fresh] at hfresh
    simp [Expr.varOpen, Expr.varClose]
    grind
  | abs e ih =>
    simp [Expr.fresh] at hfresh
    simp [Expr.varOpen, Expr.varClose]
    grind
  | op _ => rfl
  | const _ => rfl
  | ite c t f ihc iht ihf =>
    simp [Expr.fresh] at hfresh
    simp [Expr.varOpen, Expr.varClose]
    grind
  | eq e₁ e₂ ih₁ ih₂ =>
    simp [Expr.fresh] at hfresh
    simp [Expr.varOpen, Expr.varClose]
    grind
  | quant _ e ih =>
    simp [Expr.fresh] at hfresh
    simp [Expr.varOpen, Expr.varClose]
    grind

---------------------------------------------------------------------
-- Instantiation preserves typing
---------------------------------------------------------------------

/-- If `σ.instantiate n = (τ, n')`, then `HasType Γ e σ → HasType Γ e (Scheme.mono τ)`. -/
-- theorem HasType.instantiate_preserves (h : HasType Γ e σ)
--     (hinst : σ.instantiate n = (τ, n')) :
--     HasType Γ e (Scheme.mono τ) := by
--   sorry

---------------------------------------------------------------------
-- applyCtx id
---------------------------------------------------------------------

theorem Subst.id_apply (τ : Ty) : Subst.id.apply τ = τ := by
  induction τ using Ty.ind' with
  | hvar n => simp [Subst.id, Subst.apply, Map.find?]
  | hcon name args ih =>
    simp only [Subst.apply, List.attach_map_val]
    congr 1
    rw[@List.map_congr_left _ _ _ _ (fun (x: Ty) => x)] <;> try assumption
    apply List.map_id'


@[simp] theorem Subst.applyScheme_id (σ : Scheme) : Subst.id.applyScheme σ = σ := by
  simp [Subst.applyScheme, Subst.id]
  cases σ; simp
  apply Subst.id_apply

@[simp] theorem Map.fmap_id' {f : β → β} (hf : ∀ x, f x = x) (m : Map α β) :
    m.fmap f = m := by
  induction m with
  | nil => rfl
  | cons hd tl ih => simp [Map.fmap, hf]

@[simp] theorem Subst.applyCtx_id (Γ : Ctx) : Subst.id.applyCtx Γ = Γ := by
  simp [Subst.applyCtx]

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

-- theorem W_sound (h : W Γ e n = .ok (S, ae, n')) :
--     ae.erase = e ∧ HasType (S.applyCtx Γ) e (Scheme.mono ae.tyOf) := by
--   fun_induction W Γ e n generalizing S ae n' with
--   | case1 Γ n x => -- fvar
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     rename_i σ hlookup
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     constructor
--     · rfl
--     · simp [AExpr.tyOf]
--       have hfind : Γ.vars.find? x = some σ := by
--         revert hlookup; simp [Option.elim]; intro h; grind
--       exact (HasType.fvar hfind).instantiate_preserves rfl
--   | case2 Γ n f => -- op
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     rename_i σ hlookup
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     constructor
--     · rfl
--     · simp [AExpr.tyOf]
--       have hfind : Γ.ops.find? f = some σ := by
--         revert hlookup; simp [Option.elim]; intro h; grind
--       exact (HasType.op hfind).instantiate_preserves rfl
--   | case3 Γ n c => --const
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     simp
--     constructor
--     rfl
--     unfold AExpr.tyOf; split <;> try contradiction
--     . rename_i Heq; cases Heq
--       apply HasType.const
--     . rename_i Heq; cases Heq
--       apply HasType.const
--   | case4 Γ n body α  => --abs
--     rename_i x ih
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     rename_i _ v₁ hv₁
--     obtain ⟨S₁, ae₁, n₁⟩ := v₁
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     have ⟨herase₁, hty₁⟩ := ih hv₁
--     constructor
--     · -- Erasure: erase (abs arrTy (ae₁.varClose 0 x)) = abs body
--       simp [AExpr.erase, AExpr.erase_varClose, herase₁]
--       exact Expr.varClose_varOpen _ _ _ (freshFor_fresh body)
--     · -- Typing
--       rw [Subst.applyCtx_addVar, Subst.applyScheme_mono] at hty₁
--       have htyOf : (AExpr.abs (Ty.arrow (S.apply (Ty.var n)) ae₁.tyOf)
--                     (ae₁.varClose 0 body.freshFor)).tyOf =
--                    Ty.arrow (S.apply (Ty.var n)) ae₁.tyOf := by
--         simp [AExpr.tyOf]
--       rw [htyOf]
--       have hmono : ∀ τ : Ty, Scheme.isMono (Scheme.mono τ) := fun _ => rfl
--       exact HasType.abs (freshFor_fresh body) (hmono _) (hmono _) hty₁
--   | case5 Γ n e₁ e₂ ih₁ ih₂ => --app
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
--     obtain ⟨S₁, ae₁, n₁⟩ := v₁
--     obtain ⟨S₂, ae₂, n₂⟩ := v₂
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     dsimp only at hv₂ hS₃
--     have ⟨herase₁, hty₁⟩ := ih₁ hv₁
--     have ⟨herase₂, hty₂⟩ := ih₂ _ _ hv₂
--     have hunif := unify_sound hS₃
--     -- Erasure
--     constructor
--     · simp [AExpr.erase, AExpr.erase_applyAExpr, herase₁, herase₂]
--     · -- Typing: need HasType ((S₃∘(S₂∘S₁)).applyCtx Γ) (.app e₁ e₂) ...
--       -- unify_sound: S₃(S₂(ae₁.tyOf)) = Ty.arrow (S₃(ae₂.tyOf)) (S₃(Ty.var n₂))
--       rw [Subst.apply_arrow] at hunif
--       -- Lift hty₁ through S₂ then S₃
--       have hty₁' := (hty₁.subst_preserves S₂).subst_preserves S₃
--       rw [Subst.applyScheme_mono, Subst.applyScheme_mono] at hty₁'
--       rw [Subst.applyCtx_compose, Subst.applyCtx_compose] at hty₁'
--       -- rewrite fn type using unification
--       rw [hunif] at hty₁'
--       -- Lift hty₂ through S₃
--       have hty₂' := hty₂.subst_preserves S₃
--       rw [Subst.applyScheme_mono, Subst.applyCtx_compose] at hty₂'
--       -- Compose associativity: (S₃∘S₂)(S₁(Γ)) = ((S₃∘S₂)∘S₁)(Γ) = (S₃∘(S₂∘S₁))(Γ)
--       rw [Subst.compose_assoc] at hty₁'
--       rw [Subst.applyCtx_compose, Subst.compose_assoc] at hty₂'
--       -- tyOf of the app node: fnTy is an arrow after unification
--       have htyOf : (AExpr.app (S₃.apply (S₂.apply ae₁.tyOf)) (S₃.apply ae₂.tyOf)
--                     (S₃.applyAExpr (S₂.applyAExpr ae₁)) (S₃.applyAExpr ae₂)).tyOf =
--                    S₃.apply (Ty.var n₂) := by
--         show (match S₃.apply (S₂.apply ae₁.tyOf) with
--               | .con "→" [_, r] => r | t => t) = _
--         rw [hunif]
--         simp [Ty.arrow]
--       rw [htyOf]
--       -- isMono for Scheme.mono
--       have hmono : ∀ τ : Ty, Scheme.isMono (Scheme.mono τ) := fun _ => rfl
--       exact HasType.app (hmono _) (hmono _) hty₁' hty₂'
--   | case6 Γ n c t f ihc iht ihf => --ite
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     rename_i _ v₁ hv₁ _ S₂ hS₂ _ v₃ hv₃ _ v₄ hv₄ _ S₅ hS₅
--     obtain ⟨S₁, aec, n₁⟩ := v₁
--     obtain ⟨S₃, aet, n₂⟩ := v₃
--     obtain ⟨S₄, aef, n₃⟩ := v₄
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     dsimp only at hv₃ hv₄ hS₂ hS₅
--     have ⟨herasec, htyc⟩ := ihc hv₁
--     have ⟨heraset, htyt⟩ := iht _ _ _ hv₃
--     have ⟨herasef, htyf⟩ := ihf _ _ _ _ hv₄
--     have hunif₂ := unify_sound hS₂
--     have hunif₅ := unify_sound hS₅
--     constructor
--     · -- Erasure
--       simp [AExpr.erase, AExpr.erase_applyAExpr, herasec, heraset, herasef]
--     · -- Typing
--       -- (a) condition: lift htyc through S₂, S₃, S₄, S₅
--       have htyc' := (((htyc.subst_preserves S₂).subst_preserves S₃).subst_preserves S₄).subst_preserves S₅
--       rw [Subst.applyScheme_mono, Subst.applyScheme_mono, Subst.applyScheme_mono,
--           Subst.applyScheme_mono] at htyc'
--       rw [Subst.applyCtx_compose, Subst.applyCtx_compose, Subst.applyCtx_compose,
--           Subst.applyCtx_compose] at htyc'
--       rw [Subst.compose_assoc, Subst.compose_assoc, Subst.compose_assoc] at htyc'
--       -- S₅(S₄(S₃(S₂(aec.tyOf)))) = S₅(S₄(S₃(.bool))) = .bool
--       have hbool : S₅.apply (S₄.apply (S₃.apply (S₂.apply aec.tyOf))) = Ty.bool := by
--         rw [hunif₂]; simp [Subst.apply, Ty.bool]
--       rw [hbool] at htyc'
--       -- (b) then branch: lift htyt through S₄, S₅
--       have htyt' := (htyt.subst_preserves S₄).subst_preserves S₅
--       rw [Subst.applyScheme_mono, Subst.applyScheme_mono] at htyt'
--       rw [Subst.applyCtx_compose, Subst.applyCtx_compose] at htyt'
--       rw [Subst.applyCtx_compose (S₂ := (S₅.compose S₄).compose S₃)] at htyt'
--       rw [Subst.compose_assoc, Subst.compose_assoc] at htyt'
--       -- S₅(S₄(aet.tyOf)) = S₅(aef.tyOf) by hunif₅
--       rw [hunif₅] at htyt'
--       -- (c) else branch: lift htyf through S₅
--       have htyf' := htyf.subst_preserves S₅
--       rw [Subst.applyScheme_mono] at htyf'
--       rw [Subst.applyCtx_compose] at htyf'
--       rw [Subst.applyCtx_compose (S₂ := S₅.compose S₄)] at htyf'
--       rw [Subst.compose_assoc] at htyf'
--       exact HasType.ite htyc' htyt' htyf'
--   | case7 Γ n e₁ e₂ ih₁ ih₂ => --eq
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     rename_i _ v₁ hv₁ _ v₂ hv₂ _ S₃ hS₃
--     obtain ⟨S₁, ae₁, n₁⟩ := v₁
--     obtain ⟨S₂, ae₂, n₂⟩ := v₂
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     dsimp only at hv₂ hS₃
--     have ⟨herase₁, hty₁⟩ := ih₁ hv₁
--     have ⟨herase₂, hty₂⟩ := ih₂ _ _ hv₂
--     have hunif := unify_sound hS₃
--     constructor
--     · simp [AExpr.erase, AExpr.erase_applyAExpr, herase₁, herase₂]
--     · -- Lift hty₁ through S₂, S₃
--       have hty₁' := (hty₁.subst_preserves S₂).subst_preserves S₃
--       rw [Subst.applyScheme_mono, Subst.applyScheme_mono] at hty₁'
--       rw [Subst.applyCtx_compose, Subst.applyCtx_compose] at hty₁'
--       rw [Subst.compose_assoc] at hty₁'
--       -- unify_sound: S₃(S₂(ae₁.tyOf)) = S₃(ae₂.tyOf)
--       rw [hunif] at hty₁'
--       -- Lift hty₂ through S₃
--       have hty₂' := hty₂.subst_preserves S₃
--       rw [Subst.applyScheme_mono] at hty₂'
--       rw [Subst.applyCtx_compose, Subst.applyCtx_compose (S₂ := S₃.compose S₂), Subst.compose_assoc] at hty₂'
--       exact HasType.eq hty₁' hty₂'
--   | case8 Γ n k body => --quant
--     rename_i ih
--     simp only [bind, Except.bind] at h
--     split at h <;> try contradiction
--     split at h <;> try contradiction
--     rename_i _ v₁ hv₁ _ S₂ hS₂
--     obtain ⟨S₁, ae₁, n₁⟩ := v₁
--     simp only [Except.ok.injEq] at h
--     obtain ⟨rfl, rfl, rfl⟩ := h
--     dsimp only at hv₁ hS₂
--     have ⟨herase₁, hty₁⟩ := ih hv₁
--     have hunif := unify_sound hS₂
--     constructor
--     · -- Erasure
--       simp [AExpr.erase, AExpr.erase_applyAExpr, AExpr.erase_varClose, herase₁]
--       exact Expr.varClose_varOpen _ _ _ (freshFor_fresh body)
--     · -- Typing
--       rw [Subst.applyCtx_addVar, Subst.applyScheme_mono] at hty₁
--       -- Lift through S₂
--       have hty₁' := hty₁.subst_preserves S₂
--       rw [Subst.applyScheme_mono, Subst.applyCtx_addVar, Subst.applyScheme_mono,
--           Subst.applyCtx_compose] at hty₁'
--       -- unify_sound: S₂(ae₁.tyOf) = S₂(bool) = bool
--       rw [hunif] at hty₁'
--       -- tyOf of quant is always bool
--       have htyOf : (AExpr.quant k ((S₂.compose S₁).apply (Ty.var n))
--                     (ae₁ |> S₂.applyAExpr |>.varClose 0 body.freshFor)).tyOf = Ty.bool := by
--         simp [AExpr.tyOf]
--       rw [htyOf]
--       -- S₂(bool) = bool
--       have hbool : S₂.apply Ty.bool = Ty.bool := by simp [Subst.apply, Ty.bool]
--       rw [hbool] at hty₁'
--       have hmono : ∀ τ : Ty, Scheme.isMono (Scheme.mono τ) := fun _ => rfl
--       exact HasType.quant (freshFor_fresh body) (hmono _) hty₁'
--   | case9 => contradiction

end HM
