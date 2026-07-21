/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.FactoryWF

/-!
## Basic `LExpr.getVars` properties

Structural lemmas relating `LExpr.getVars` (the free variables of an expression)
to the various substitution and decomposition operations on `LExpr`. These are
factored out of `LExprEvalProps` so they can be reused independently of the
evaluator.
-/

namespace Lambda
open Strata

variable {Tbase : LExprParams}
  [DecidableEq Tbase.IDMeta]

omit [DecidableEq Tbase.IDMeta] in
/-- `liftBVars` does not change the free variables (only shifts de Bruijn indices). -/
theorem getVars_liftBVars (k : Nat) (e : LExpr Tbase.mono) (c : Nat) :
    LExpr.LExpr.getVars (LExpr.liftBVars k e c) = LExpr.LExpr.getVars e := by
  induction e generalizing c with
  | const | op | fvar => rfl
  | bvar m i => simp only [LExpr.liftBVars]; split <;> rfl
  | abs _ _ _ _ ih => simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; exact ih (c + 1)
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [iht (c + 1), ihb (c + 1)]
  | app _ _ _ ih1 ih2 => simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [ih1 c, ih2 c]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [ih1 c, ih2 c, ih3 c]
  | eq _ _ _ ih1 ih2 => simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [ih1 c, ih2 c]

omit [DecidableEq Tbase.IDMeta] in
/-- `replaceUserProvidedType` does not change the free variables. -/
theorem getVars_replaceUserProvidedType (e : LExpr Tbase.mono)
    (f : LMonoTy → LMonoTy) :
    LExpr.LExpr.getVars (LExpr.replaceUserProvidedType e f) = LExpr.LExpr.getVars e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs _ _ _ _ ih => simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; exact ih
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [iht, ihb]
  | app _ _ _ ih1 ih2 => simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [ih1, ih2]

omit [DecidableEq Tbase.IDMeta] in
/-- `applySubst` does not change the free variables (only type annotations). -/
theorem getVars_applySubst (e : LExpr Tbase.mono) (S : Subst) :
    LExpr.LExpr.getVars (e.applySubst S) = LExpr.LExpr.getVars e := by
  unfold LExpr.applySubst
  split
  · rfl
  · exact getVars_replaceUserProvidedType e _

omit [DecidableEq Tbase.IDMeta] in
/-- `replaceMetadata1` does not change the free variables. -/
theorem getVars_replaceMetadata1 (r : Tbase.Metadata) (e : LExpr Tbase.mono) :
    LExpr.LExpr.getVars (LExpr.replaceMetadata1 r e) = LExpr.LExpr.getVars e := by
  cases e <;> rfl

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables introduced by `substK` come from the base expression or the
    substituted term. -/
theorem getVars_substK_mem (k : Nat) (s : Tbase.mono.base.Metadata → LExpr Tbase.mono)
    (e : LExpr Tbase.mono) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.substK k s e)) :
    y ∈ LExpr.LExpr.getVars e ∨ ∃ m, y ∈ LExpr.LExpr.getVars (s m) := by
  induction e generalizing k with
  | const | op => simp [LExpr.substK, LExpr.LExpr.getVars] at hy
  | bvar m i =>
    simp only [LExpr.substK] at hy
    split at hy
    · exact Or.inr ⟨m, hy⟩
    · simp [LExpr.LExpr.getVars] at hy
  | fvar m x ty => simp only [LExpr.substK] at hy; exact Or.inl hy
  | abs _ _ _ _ ih =>
    simp only [LExpr.substK, LExpr.LExpr.getVars] at hy
    exact ih (k + 1) hy
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.substK, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases iht (k + 1) h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hl)
      · exact Or.inr hr
    · rcases ihb (k + 1) h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hl)
      · exact Or.inr hr
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substK, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases ih1 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hl)
      · exact Or.inr hr
    · rcases ih2 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hl)
      · exact Or.inr hr
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substK, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with (h | h) | h
    · rcases ih1 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl hl))
      · exact Or.inr hr
    · rcases ih2 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hl))
      · exact Or.inr hr
    · rcases ih3 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hl)
      · exact Or.inr hr
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substK, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases ih1 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hl)
      · exact Or.inr hr
    · rcases ih2 k h with hl | hr
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hl)
      · exact Or.inr hr

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables introduced by `mkApp` come from the head or an argument. -/
theorem getVars_mkApp_mem (m : Tbase.Metadata) (op : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono)) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.mkApp m op args)) :
    y ∈ LExpr.LExpr.getVars op ∨ ∃ a ∈ args, y ∈ LExpr.LExpr.getVars a := by
  induction args generalizing op with
  | nil => simp only [LExpr.mkApp] at hy; exact Or.inl hy
  | cons a rest ih =>
    simp only [LExpr.mkApp] at hy
    rcases ih (.app m op a) hy with h | ⟨b, hb, hby⟩
    · simp only [LExpr.LExpr.getVars, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hby⟩

/-- Characterize the free variables introduced by `substFvarsLifting.go`. -/
private theorem getVars_substFvarsLifting_go_mem
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (depth : Nat) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.substFvarsLifting.go sm e depth)) :
    (y ∈ LExpr.LExpr.getVars e ∧ Map.find? sm y = none) ∨
    (∃ k v, Map.find? sm k = some v ∧ y ∈ LExpr.LExpr.getVars v) := by
  induction e generalizing depth with
  | const | op | bvar =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars] at hy
    simp at hy
  | fvar m x ty =>
    simp only [LExpr.substFvarsLifting.go] at hy
    cases hf : Map.find? sm x with
    | none =>
      rw [hf] at hy
      simp only [LExpr.LExpr.getVars, List.mem_singleton] at hy
      subst hy
      exact Or.inl ⟨by simp [LExpr.LExpr.getVars], hf⟩
    | some v =>
      rw [hf] at hy
      rw [getVars_liftBVars] at hy
      exact Or.inr ⟨x, v, hf, hy⟩
  | abs _ _ _ _ ih =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars] at hy
    exact ih (depth + 1) hy
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases iht (depth + 1) h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hin, hn⟩
      · exact Or.inr hr
    · rcases ihb (depth + 1) h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases ih1 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hin, hn⟩
      · exact Or.inr hr
    · rcases ih2 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with (h | h) | h
    · rcases ih1 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl hin), hn⟩
      · exact Or.inr hr
    · rcases ih2 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hin), hn⟩
      · exact Or.inr hr
    · rcases ih3 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases ih1 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hin, hn⟩
      · exact Or.inr hr
    · rcases ih2 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr

/-- `substFvarsLifting.go` depends only on the substitution map's values at the
    free variables of `e`. -/
theorem substFvarsLifting_go_congr
    (sm₁ sm₂ : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (depth : Nat)
    (h : ∀ x ∈ LExpr.LExpr.getVars e, Map.find? sm₁ x = Map.find? sm₂ x) :
    LExpr.substFvarsLifting.go sm₁ e depth = LExpr.substFvarsLifting.go sm₂ e depth := by
  suffices H : ∀ (e : LExpr Tbase.mono) (depth : Nat),
      (∀ x ∈ LExpr.LExpr.getVars e, Map.find? sm₁ x = Map.find? sm₂ x) →
      LExpr.substFvarsLifting.go sm₁ e depth = LExpr.substFvarsLifting.go sm₂ e depth from
    H e depth h
  intro e
  induction e with
  | const _ _ => intro depth _; rfl
  | op _ _ _ => intro depth _; rfl
  | bvar _ _ => intro depth _; rfl
  | fvar m name ty =>
    intro depth hh
    simp only [LExpr.substFvarsLifting.go]
    rw [hh name (by simp [LExpr.LExpr.getVars])]
  | abs m nm ty body ih =>
    intro depth hh
    simp only [LExpr.substFvarsLifting.go]
    rw [ih (depth+1) (by intro x hx; exact hh x hx)]
  | quant m qk nm ty tr body iht ihb =>
    intro depth hh
    simp only [LExpr.substFvarsLifting.go]
    rw [iht (depth+1) (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx)),
        ihb (depth+1) (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))]
  | app m fn e' ihf ihe =>
    intro depth hh
    simp only [LExpr.substFvarsLifting.go]
    rw [ihf depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx)),
        ihe depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))]
  | eq m e1 e2 ih1 ih2 =>
    intro depth hh
    simp only [LExpr.substFvarsLifting.go]
    rw [ih1 depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx)),
        ih2 depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))]
  | ite m c t f ihc iht ihf =>
    intro depth hh
    simp only [LExpr.substFvarsLifting.go]
    rw [ihc depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl hx))),
        iht depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hx))),
        ihf depth (by intro x hx; exact hh x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))]

/-- `substFvarsLifting` depends only on the substitution map's values at the free
    variables of `e` (given the maps are simultaneously empty or not). -/
theorem substFvarsLifting_congr
    (sm₁ sm₂ : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono)
    (hempty : sm₁.isEmpty = sm₂.isEmpty)
    (h : ∀ x ∈ LExpr.LExpr.getVars e, Map.find? sm₁ x = Map.find? sm₂ x) :
    LExpr.substFvarsLifting e sm₁ = LExpr.substFvarsLifting e sm₂ := by
  unfold LExpr.substFvarsLifting
  rw [hempty]
  split
  · rfl
  · exact substFvarsLifting_go_congr sm₁ sm₂ e 0 h

/-- Characterize the free variables introduced by `substFvarsLifting`. -/
theorem getVars_substFvarsLifting_mem
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.substFvarsLifting e sm)) :
    (y ∈ LExpr.LExpr.getVars e ∧ Map.find? sm y = none) ∨
    (∃ k v, Map.find? sm k = some v ∧ y ∈ LExpr.LExpr.getVars v) := by
  unfold LExpr.substFvarsLifting at hy
  split at hy
  · rename_i h_empty
    refine Or.inl ⟨hy, ?_⟩
    cases sm with
    | nil => rfl
    | cons p m => simp [Map.isEmpty] at h_empty
  · exact getVars_substFvarsLifting_go_mem sm e 0 y hy

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables of the arguments extracted by `getLFuncCall.go` are contained
    in the free variables of the whole expression together with the accumulator. -/
private theorem getLFuncCall_go_getVars_mem
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (op, args))
    (a : LExpr Tbase.mono) (ha : a ∈ args)
    (y : Tbase.Identifier) (hy : y ∈ LExpr.LExpr.getVars a) :
    y ∈ LExpr.LExpr.getVars e ∨ (∃ b ∈ acc, y ∈ LExpr.LExpr.getVars b) := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [getLFuncCall.go] at h
    rcases getLFuncCall_go_getVars_mem e' ([arg1, arg2] ++ acc) op args h a ha y hy with h1 | ⟨b, hb, hby⟩
    · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl h1))
    · simp only [List.cons_append, List.nil_append, List.mem_cons] at hb
      rcases hb with rfl | rfl | hb'
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hby))
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hby)
      · exact Or.inr ⟨b, hb', hby⟩
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | ha'
    · exact Or.inl (by
        simp only [LExpr.LExpr.getVars, List.mem_append, List.not_mem_nil, false_or]; exact hy)
    · exact Or.inr ⟨a, ha', hy⟩
  | .app m1 (.const _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.bvar _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.fvar _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.abs _ _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.quant _ _ _ _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.ite _ _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.eq _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .const _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .op _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .bvar _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  termination_by e.sizeOf

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables of a `callOfLFunc` argument are contained in the whole
    expression's free variables. -/
theorem callOfLFunc_getVars_args (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (h : F.callOfLFunc e = some (op, args, f))
    (a : LExpr Tbase.mono) (ha : a ∈ args)
    (y : Tbase.Identifier) (hy : y ∈ LExpr.LExpr.getVars a) :
    y ∈ LExpr.LExpr.getVars e := by
  have hget : getLFuncCall e = (op, args) := callOfLFunc_getLFuncCall h
  unfold getLFuncCall at hget
  rcases getLFuncCall_go_getVars_mem e [] op args hget a ha y hy with h1 | ⟨b, hb, _⟩
  · exact h1
  · simp at hb

omit [DecidableEq Tbase.IDMeta] in
/-- The free variables of a well-formed function body are among its inputs. -/
theorem lfunc_body_getVars_subset_keys
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (lfunc : LFunc Tbase) (hwf : LFuncWF lfunc)
    (body : LExpr Tbase.mono) (hbody : lfunc.body = some body)
    (y : Tbase.Identifier) (hy : y ∈ LExpr.LExpr.getVars body) :
    y ∈ lfunc.inputs.keys := by
  rw [getVars_eq_freeVars_idents, List.mem_map] at hy
  obtain ⟨p, hp_mem, hp_eq⟩ := hy
  have hbf := hwf.toFuncWF.body_freevars body hbody
  have hname : y.name ∈ lfunc.inputs.map (fun q => q.1.name) := by
    apply hbf
    rw [List.mem_map]
    exact ⟨p, hp_mem, by rw [hp_eq]⟩
  rw [List.mem_map] at hname
  obtain ⟨q, hq_mem, hq_eq⟩ := hname
  have hyq : y = q.fst := (hIdent q.1 y hq_eq).symm
  rw [hyq, ListMap.keys_eq_map_fst]
  exact List.mem_map_of_mem hq_mem

end Lambda
