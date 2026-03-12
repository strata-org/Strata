/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AlgorithmW
import Strata.Experiment.HM.Typing

namespace HM

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
    simp[Map.find?]
    split
    . subst_vars; rfl
    . apply IH

theorem Map.fmap_fmap (f : β → γ) (g : γ → δ) (m : Map α β) :
    (m.fmap f).fmap g = m.fmap (g ∘ f) := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    exact congrArg ((hd.fst, g (f hd.snd)) :: ·) ih

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

end HM
