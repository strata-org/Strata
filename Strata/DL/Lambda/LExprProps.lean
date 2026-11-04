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
