/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.LExprWFProps

import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
public import Strata.DL.Lambda.FactoryWF
import Strata.Util.PtrCacheProps

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

/-- Every `LExpr` has strictly positive `sizeOf`. -/
theorem LExpr.sizeOf_pos {T} (e : LExpr T) : 0 < sizeOf e := by
  cases e <;> simp <;> omega

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
/-- Rewriting annotations by `f` rewrites each binder annotation by `f`. -/
theorem binderAnnotations_replaceUserProvidedType (e : LExpr Tbase.mono)
    (f : LMonoTy → LMonoTy) :
    LExpr.binderAnnotations (LExpr.replaceUserProvidedType e f) =
      (LExpr.binderAnnotations e).map f := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs _ _ ty _ ih =>
    cases ty <;> simp [LExpr.replaceUserProvidedType, LExpr.binderAnnotations, ih]
  | quant _ _ _ ty _ _ iht ihb =>
    cases ty <;> simp [LExpr.replaceUserProvidedType, LExpr.binderAnnotations, iht, ihb]
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.binderAnnotations, ih1, ih2,
      List.map_append]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.binderAnnotations, ih1, ih2, ih3,
      List.map_append]
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.binderAnnotations, ih1, ih2,
      List.map_append]

omit [DecidableEq Tbase.IDMeta] in
/-- Rewriting annotations by `f` rewrites each free-variable annotation by `f`. -/
theorem fvarAnnotations_replaceUserProvidedType (e : LExpr Tbase.mono)
    (f : LMonoTy → LMonoTy) :
    LExpr.fvarAnnotations (LExpr.replaceUserProvidedType e f) =
      (LExpr.fvarAnnotations e).map f := by
  induction e with
  | const | op | bvar => rfl
  | fvar _ _ ty =>
    cases ty <;> simp [LExpr.replaceUserProvidedType, LExpr.fvarAnnotations]
  | abs _ _ _ _ ih =>
    simp only [LExpr.replaceUserProvidedType, LExpr.fvarAnnotations, ih]
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.replaceUserProvidedType, LExpr.fvarAnnotations, iht, ihb,
      List.map_append]
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.fvarAnnotations, ih1, ih2,
      List.map_append]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.fvarAnnotations, ih1, ih2, ih3,
      List.map_append]
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.fvarAnnotations, ih1, ih2,
      List.map_append]

omit [DecidableEq Tbase.IDMeta] in
/-- `applyTypeSubst` does not change the free variables (only type annotations). -/
theorem getVars_applyTypeSubst (e : LExpr Tbase.mono) (S : Subst) :
    LExpr.LExpr.getVars (e.applyTypeSubst S) = LExpr.LExpr.getVars e := by
  unfold LExpr.applyTypeSubst
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
  obtain ⟨q, hq_mem, hq_eq⟩ := List.mem_map.mp hname
  have hyq : y = q.fst := (hIdent q.1 y hq_eq).symm
  rw [hyq, ListMap.keys_eq_map_fst]
  exact List.mem_map_of_mem hq_mem

namespace LExpr
open Strata.PtrCache

/-- The pointer-address hash cache is a *transparent* optimization: it computes
    exactly the pure structural hash `hashExpr`, on the nose, for every
    expression. A one-line corollary of the generic `run'_output_eq` — the cache
    is functionally indistinguishable from `hashExpr`. -/
theorem hashExprCached_eq {T : LExprParamsT} [Hashable T.TypeType] (e : LExpr T) :
    hashExprCached e = hashExpr e :=
  run'_output_eq (hashExprPtrCache e) PtrCache.empty

/-- The pointer-address `hasBVar` cache is a *transparent* optimization: it
    computes exactly `hasBVar`, on the nose, for every expression. A one-line
    corollary of the generic `run'_output_eq`. -/
theorem hasBVarCached_eq {T : LExprParamsT} (e : LExpr T) :
    hasBVarCached e = hasBVar e :=
  run'_output_eq (hasBVarPtrCache e) PtrCache.empty

end LExpr

/-- Two lists are pointwise equal up to metadata iff their metadata erasures are equal. -/
theorem forall₂_iff_map_eraseMetadata_eq {T : LExprParams} (a₁ a₂ : List (LExpr T.mono)) :
    List.Rel₂ (fun x y => LExpr.eraseMetadata x = LExpr.eraseMetadata y) a₁ a₂ ↔
    a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata := by
  constructor
  · intro hfa
    induction hfa with
    | nil => rfl
    | cons hxy _ ih => rw [List.map_cons, List.map_cons, hxy, ih]
  · intro hmap
    induction a₁ generalizing a₂ with
    | nil =>
      cases a₂ with
      | nil => exact List.Rel₂.nil
      | cons y ys => exact absurd hmap (by simp)
    | cons x xs ih =>
      cases a₂ with
      | nil => exact absurd hmap (by simp)
      | cons y ys =>
        rw [List.map_cons, List.map_cons, List.cons.injEq] at hmap
        exact List.Rel₂.cons hmap.1 (ih ys hmap.2)

/-! ### Expressions that differ only in metadata -/

/-- Erasing metadata preserves whether an expression is an operator reference, and which
    operator at which type it names. -/
theorem eraseMetadata_op_cases {T : LExprParams} (a b : LExpr T.mono)
    (h : a.eraseMetadata = b.eraseMetadata) :
    (∃ (m₁ m₂ : T.Metadata) (o : T.Identifier) (ty : Option LMonoTy),
        a = .op m₁ o ty ∧ b = .op m₂ o ty)
    ∨ ((∀ m o ty, a ≠ .op m o ty) ∧ (∀ m o ty, b ≠ .op m o ty)) := by
  cases a
  case op m₁ o ty =>
    cases b
    case op m₂ o₂ ty₂ =>
      refine Or.inl ⟨m₁, m₂, o, ty, rfl, ?_⟩
      have hinj := h
      simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.op.injEq] at hinj
      grind
    all_goals exact absurd h (by simp [LExpr.eraseMetadata, LExpr.replaceMetadata])
  all_goals
    refine Or.inr ⟨by intro m o ty; simp, ?_⟩
    intro m o ty hb
    subst hb
    exact absurd h (by simp [LExpr.eraseMetadata, LExpr.replaceMetadata])

/-- Two lists that differ only in metadata have entries that differ only in metadata. -/
theorem getElem?_of_map_eraseMetadata_eq {T : LExprParams}
    (a₁ a₂ : List (LExpr T.mono))
    (h : a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata) (idx : Nat)
    (r₁ : LExpr T.mono) (h₁ : a₁[idx]? = some r₁) :
    ∃ r₂, a₂[idx]? = some r₂ ∧ r₁.eraseMetadata = r₂.eraseMetadata := by
  have hg : (a₁.map LExpr.eraseMetadata)[idx]? = (a₂.map LExpr.eraseMetadata)[idx]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map, h₁] at hg
  cases h₂ : a₂[idx]? with
  | none => rw [h₂] at hg; exact absurd hg (by simp)
  | some r₂ =>
    refine ⟨r₂, rfl, ?_⟩
    rw [h₂] at hg
    simpa only [Option.map_some, Option.some.injEq] using hg

/-! ### Free variables, metadata, and fresh annotations -/

/-- Applying a function to arguments introduces no variables beyond those of the function and
    of the arguments. -/
theorem getVars_mkApp {T : LExprParams} (m : T.Metadata) (f : LExpr T.mono)
    (args : List (LExpr T.mono)) :
    ∀ y ∈ LExpr.LExpr.getVars (LExpr.mkApp m f args),
      y ∈ LExpr.LExpr.getVars f ∨ ∃ a ∈ args, y ∈ LExpr.LExpr.getVars a := by
  induction args generalizing f with
  | nil => intro y hy; exact Or.inl (by simpa only [LExpr.mkApp] using hy)
  | cons a rest ih =>
    intro y hy
    simp only [LExpr.mkApp] at hy
    rcases ih (.app m f a) y hy with h1 | ⟨b, hb, hby⟩
    · simp only [LExpr.LExpr.getVars, List.mem_append] at h1
      rcases h1 with h2 | h3
      · exact Or.inl h2
      · exact Or.inr ⟨a, by simp, h3⟩
    · exact Or.inr ⟨b, by simp [hb], hby⟩

/-- An iterated lambda has exactly the free variables of its body. -/
theorem getVars_absMulti {T : LExprParams} (m : T.Metadata) (tys : List LMonoTy)
    (body : LExpr T.mono) :
    LExpr.LExpr.getVars (LExpr.absMulti m tys body) = LExpr.LExpr.getVars body := by
  induction tys with
  | nil => rfl
  | cons t rest ih =>
    show LExpr.LExpr.getVars
      (LExpr.abs m "" (some t) (LExpr.absMulti m rest body)) = LExpr.LExpr.getVars body
    simpa only [LExpr.LExpr.getVars] using ih

/-- Erasing metadata reaches under an iterated lambda. -/
theorem eraseMetadata_absMulti {T : LExprParams} (m : T.Metadata) (tys : List LMonoTy)
    (body : LExpr T.mono) :
    (LExpr.absMulti m tys body).eraseMetadata = LExpr.absMulti () tys body.eraseMetadata := by
  induction tys with
  | nil => rfl
  | cons t rest ih =>
    show (LExpr.abs m "" (some t) (LExpr.absMulti m rest body)).eraseMetadata
      = LExpr.abs () "" (some t) (LExpr.absMulti () rest body.eraseMetadata)
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.abs.injEq, true_and]
    simpa only [LExpr.eraseMetadata] using ih

/-- A type variable can be chosen fresh for an expression and outside a specified list of names. -/
theorem exists_fresh_ftvar_avoiding {T : LExprParams}
    (y : Identifier T.IDMeta) (e : LExpr T.mono) (vs : List TyIdentifier) :
    ∃ v : TyIdentifier,
      LExpr.fresh ((y, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) e ∧ v ∉ vs := by
  obtain ⟨v, hv⟩ := String.exists_notMem_strings
    ((LExpr.freeVars e).filterMap
        (fun p => match p.2 with | some (.ftvar w) => some w | _ => none) ++ vs)
  refine ⟨v, ?_, fun hmem => hv (List.mem_append_right _ hmem)⟩
  simp only [LExpr.fresh]
  intro hmem
  exact hv (List.mem_append_left _
    (List.mem_filterMap.mpr ⟨(y, some (LMonoTy.ftvar v)), hmem, rfl⟩))

/-- Some type-variable annotation of `y` is fresh for any expression. -/
theorem exists_fresh_ftvar {T : LExprParams}
    (y : Identifier T.IDMeta) (e : LExpr T.mono) :
    ∃ v : TyIdentifier, LExpr.fresh ((y, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) e :=
  let ⟨v, hv, _⟩ := exists_fresh_ftvar_avoiding y e []
  ⟨v, hv⟩

end Lambda
