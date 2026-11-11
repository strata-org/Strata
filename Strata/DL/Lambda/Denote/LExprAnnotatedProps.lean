/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote

/-! # Annotated typing under rewriting of type annotations

Key theorems: `LExpr.HasTypeA_replaceUserProvidedType_map` (rewriting annotations by `φ` maps an
annotated typing by `φ`) and `OpsConsistentR.of_opAnnots` with its `_body` and `_resolveTy` forms
(operator annotations that instantiate their signatures give `OpsConsistentR`). -/

namespace Lambda

open LExpr
open Strata.Util (HMap HMaps)

public section

/-- Rewriting annotations by `φ` maps an annotated typing's context and type by `φ`, when `φ`
    preserves arrows, `bool`, and literal types. -/
theorem LExpr.HasTypeA_replaceUserProvidedType_map {T : LExprParams}
    (φ : LMonoTy → LMonoTy)
    (hφ_arrow : ∀ a b, φ (.arrow a b) = .arrow (φ a) (φ b))
    (hφ_bool : φ .bool = .bool)
    (hφ_const : ∀ c : LConst, φ c.ty = c.ty)
    (Δ : List LMonoTy) (e : LExpr T.mono) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ) :
    LExpr.HasTypeA (Δ.map φ) (LExpr.replaceUserProvidedType e φ) (φ τ) := by
  induction h with
  | const => rw [hφ_const]; exact .const
  | op => exact .op
  | fvar => exact .fvar
  | bvar hlk =>
    apply LExpr.HasTypeA.bvar
    rw [List.getElem?_map, hlk]; rfl
  | abs _ ih =>
    rw [hφ_arrow]
    exact .abs ih
  | quant _ _ ih_tr ih_b =>
    rw [hφ_bool] at ih_b ⊢
    exact .quant ih_tr ih_b
  | app _ _ ih_fn ih_arg =>
    rw [hφ_arrow] at ih_fn
    exact .app ih_fn ih_arg
  | ite _ _ _ ih_c ih_t ih_e =>
    rw [hφ_bool] at ih_c
    exact .ite ih_c ih_t ih_e
  | eq _ _ ih1 ih2 =>
    rw [hφ_bool]
    exact .eq ih1 ih2

/-! ## `OpsConsistentR` from operator annotations -/

/-- A fully annotated expression satisfies `OpsConsistentR F` when every operator annotation is
    an instance of the signature of the function that `F` stores under the operator's name. -/
theorem OpsConsistentR.of_opAnnots {T : LExprParams} {F : Factory T} {e : LExpr T.mono}
    (hann : LExpr.fullyAnnotated e = true)
    (h : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e → ∃ (fn : LFunc T) (τ : Subst),
      F[o.name]? = some fn ∧
        ty = LMonoTy.subst τ (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))) :
    OpsConsistentR F e := by
  induction e with
  | const => exact .const
  | bvar => exact .bvar
  | fvar => exact .fvar
  | op m o ty =>
    cases ty with
    | none => simp [LExpr.fullyAnnotated] at hann
    | some t =>
      have h_mem : (o, t) ∈ LExpr.opAnnots (LExpr.op m o (some t)) := by
        simp [LExpr.opAnnots]
      obtain ⟨fn, τ, hfn, hty⟩ := h o t h_mem
      exact .op_in hfn hty
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    exact .app (ih1 hann.1 (fun o ty ho => h o ty (List.subset_append_left _ _ ho)))
      (ih2 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))
  | abs m name ty body ih =>
    simp only [LExpr.fullyAnnotated] at hann
    exact .abs (ih hann h)
  | quant m k name ty tr body ih1 ih2 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    exact .quant (ih1 hann.1.2 (fun o ty ho => h o ty (List.subset_append_left _ _ ho)))
      (ih2 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))
  | ite m c t f ih1 ih2 ih3 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    have hc : LExpr.opAnnots c ⊆ LExpr.opAnnots (.ite m c t f) :=
      List.subset_append_of_subset_left _ (List.subset_append_left _ _)
    have ht : LExpr.opAnnots t ⊆ LExpr.opAnnots (.ite m c t f) :=
      List.subset_append_of_subset_left _ (List.subset_append_right _ _)
    exact .ite (ih1 hann.1.1 (fun o ty ho => h o ty (hc ho)))
      (ih2 hann.1.2 (fun o ty ho => h o ty (ht ho)))
      (ih3 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    exact .eq (ih1 hann.1 (fun o ty ho => h o ty (List.subset_append_left _ _ ho)))
      (ih2 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))

/-- A fully annotated expression satisfies `OpsConsistentR F` when every operator annotation is
    an instance of the body of its function's type scheme and every signature type is registered. -/
theorem OpsConsistentR.of_opAnnots_body {T : LExprParams} [DecidableEq T.IDMeta]
    {ks : KnownTypes} {F : Factory T} {e : LExpr T.mono} (hsig : FactorySigsKnown ks F)
    (hann : LExpr.fullyAnnotated e = true)
    (h : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e →
      ∃ f xs body, F[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ body) :
    OpsConsistentR F e := by
  refine OpsConsistentR.of_opAnnots hann fun o ty ho => ?_
  obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ := h o ty ho
  have hmem := Factory.getElem?_is_some_implies_mem hf
  have hbody := LFunc.type_eq_mkArrow' hsig.1 hty (hsig.2 f hmem f.output List.mem_cons_self)
  simp only [LTy.forAll.injEq] at hbody
  refine ⟨f, τ, hf, ?_⟩
  rw [hbody.2]

/-- A fully annotated expression satisfies `OpsConsistentR F` when every operator annotation is
    an instance of its function's type-scheme body with `Γ`'s aliases resolved, and no alias of
    `Γ` is named in `ks`. -/
theorem OpsConsistentR.of_opAnnots_resolveTy {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] {ks : KnownTypes} {F : Factory T}
    {Γ : TContext T.IDMeta} {e : LExpr T.mono} (hsig : FactorySigsKnown ks F)
    (hfresh : ∀ al ∈ Γ.aliases, ks.containsName al.name = false)
    (hann : LExpr.fullyAnnotated e = true)
    (h : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e →
      ∃ f xs body, F[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ (Γ.resolveTy body)) :
    OpsConsistentR F e := by
  refine OpsConsistentR.of_opAnnots_body hsig hann fun o ty ho => ?_
  obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ := h o ty ho
  have hkn := LFunc.body_knownInstance hsig.1
    (hsig.2 f (Factory.getElem?_is_some_implies_mem hf)) hty
  exact ⟨f, xs, body, hf, hty, τ,
    congrArg (LMonoTy.subst τ) (TContext.resolveTy_of_knownInstance hfresh hkn)⟩

end -- public section

end Lambda
