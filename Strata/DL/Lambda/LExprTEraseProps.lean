/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprTProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.Util.HMaps
import Strata.Util.Tactics

/-! # Type erasure under resolution

`LExpr.resolve` only adds type annotations: erasing the annotations of the
`unresolved` form of its output gives back the erased input. This needs the free
variables of the input to be bound in the context, because resolution opens a
binder with a generated variable and closes it again, which would also close an
input free variable that has the same name.

Key theorems: `resolve_unresolved_eraseTypes` (resolution keeps the erased
expression) and the erasure lemmas for the type-only maps
`eraseTypes_applyTypeSubst` and `eraseTypes_mapExprTys`.
-/

namespace Lambda

open Strata.Util (HMap HMaps)

public section

namespace LExpr

variable {T : LExprParams}

/-- Erasing types commutes with opening a bound variable: opening with an
    annotated free variable is opening with the unannotated one after
    erasure. -/
private theorem eraseTypes_varOpen (k : Nat) (x : T.Identifier) (t : LMonoTy)
    (e : LExpr T.mono) :
    (LExpr.varOpen k (x, some t) e).eraseTypes =
      LExpr.varOpen k (x, none) e.eraseTypes := by
  induction e generalizing k with
  | const m c => simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes]
  | op m o ty => simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes]
  | fvar m y ty => simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes]
  | bvar m i =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes]
    split <;> simp only [LExpr.eraseTypes]
  | abs m name ty b ih =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes] at ih ⊢
    rw [ih]
  | quant m qk name ty tr b ihtr ihb =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes] at ihtr ihb ⊢
    rw [ihtr, ihb]
  | app m f a ihf iha =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes] at ihf iha ⊢
    rw [ihf, iha]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes] at ihc iht ihf ⊢
    rw [ihc, iht, ihf]
  | eq m a b iha ihb =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.eraseTypes] at iha ihb ⊢
    rw [iha, ihb]

/-- Opening a bound variable adds no free variable other than the one it opens
    with. -/
private theorem getVars_varOpen_subset (k : Nat) (x : T.Identifier)
    (o : Option LMonoTy) (e : LExpr T.mono) (id : T.Identifier)
    (h : id ∈ LExpr.getVars (LExpr.varOpen k (x, o) e)) :
    id = x ∨ id ∈ LExpr.getVars e := by
  induction e generalizing k with
  | const m c =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars] at h
    exact absurd h List.not_mem_nil
  | op m o' ty =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars] at h
    exact absurd h List.not_mem_nil
  | fvar m y ty =>
    simp only [LExpr.varOpen, LExpr.substK] at h
    exact Or.inr h
  | bvar m i =>
    simp only [LExpr.varOpen, LExpr.substK] at h
    split at h
    · simp only [LExpr.getVars, List.mem_singleton] at h
      exact Or.inl h
    · simp only [LExpr.getVars] at h
      exact absurd h (List.not_mem_nil)
  | abs m name ty b ih =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars] at ih h ⊢
    exact ih (k + 1) h
  | quant m qk name ty tr b ihtr ihb =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars, List.mem_append]
      at ihtr ihb h ⊢
    rcases h with h | h
    · rcases ihtr (k + 1) h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases ihb (k + 1) h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | app m f a ihf iha =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars, List.mem_append]
      at ihf iha h ⊢
    rcases h with h | h
    · rcases ihf k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases iha k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars, List.mem_append]
      at ihc iht ihf h ⊢
    rcases h with (h | h) | h
    · rcases ihc k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
    · rcases iht k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inr h))
    · rcases ihf k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | eq m a b iha ihb =>
    simp only [LExpr.varOpen, LExpr.substK, LExpr.getVars, List.mem_append]
      at iha ihb h ⊢
    rcases h with h | h
    · rcases iha k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases ihb k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- Closing a variable of a resolved expression, then erasing, is erasing, then
    closing the unannotated variable. -/
private theorem eraseTypes_unresolved_varCloseT [DecidableEq T.IDMeta] (k : Nat)
    (x : T.Identifier) (et : LExprT T.mono) :
    (LExpr.unresolved (LExpr.varCloseT k x et)).eraseTypes =
      LExpr.varClose k (x, none) (LExpr.unresolved et).eraseTypes := by
  induction et generalizing k with
  | const m c =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose]
  | op m o ty =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose]
  | bvar m i =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose]
  | fvar m y ty =>
    simp only [LExpr.varCloseT]
    split
    · rename_i hxy
      simp only [LExpr.unresolved, LExpr.eraseTypes, LExpr.varClose, hxy,
        Bool.true_and, beq_self_eq_true, ↓reduceIte]
    · rename_i hxy
      simp only [LExpr.unresolved, LExpr.eraseTypes, LExpr.varClose]
      simp only [Bool.not_eq_true] at hxy
      simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | abs m name ty b ih =>
    simp only [LExpr.varCloseT, LExpr.unresolved]
    split <;>
      simp only [LExpr.eraseTypes, LExpr.varClose, ih (k + 1), *]
  | quant m qk name ty tr b ihtr ihb =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose, ihtr (k + 1), ihb (k + 1)]
  | app m f a ihf iha =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose, ihf k, iha k]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose, ihc k, iht k, ihf k]
  | eq m a b iha ihb =>
    simp only [LExpr.varCloseT, LExpr.unresolved, LExpr.eraseTypes,
      LExpr.varClose, iha k, ihb k]

/-- Applying a type substitution to the stored types of a resolved expression
    does not change its erased `unresolved` form. -/
theorem eraseTypes_unresolved_applySubstT (et : LExprT T.mono) (S : Subst) :
    (LExpr.unresolved (LExpr.applySubstT et S)).eraseTypes =
      (LExpr.unresolved et).eraseTypes := by
  induction et with
  | const m c =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
  | op m o ty =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.eraseTypes]
  | bvar m i =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
  | fvar m y ty =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.eraseTypes]
  | abs m name ty b ih =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
      at ih ⊢
    split <;> split <;> simp only [LExpr.eraseTypes, ih]
  | quant m qk name ty tr b ihtr ihb =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.eraseTypes] at ihtr ihb ⊢
    rw [ihtr, ihb]
  | app m f a ihf iha =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.eraseTypes] at ihf iha ⊢
    rw [ihf, iha]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.eraseTypes] at ihc iht ihf ⊢
    rw [ihc, iht, ihf]
  | eq m a b iha ihb =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.eraseTypes] at iha ihb ⊢
    rw [iha, ihb]

/-- The variables of an erased expression are those of the expression. -/
private theorem getVars_eraseTypes (e : LExpr T.mono) :
    LExpr.getVars e.eraseTypes = LExpr.getVars e := by
  induction e <;> simp only [LExpr.eraseTypes, LExpr.getVars, *]

/-- Closing the binder variable after opening the erased expression with it
    gives back the erased expression, when the variable is not free in the
    expression. -/
private theorem varClose_varOpen_eraseTypes [DecidableEq T.IDMeta] (k : Nat)
    (x : T.Identifier) (e : LExpr T.mono) (hx : x ∉ LExpr.getVars e) :
    LExpr.varClose k (x, none) (LExpr.varOpen k (x, none) e.eraseTypes) =
      e.eraseTypes := by
  have hfresh : LExpr.fresh (x, none) e.eraseTypes := by
    intro hmem
    have hvar : x ∈ LExpr.getVars e.eraseTypes := by
      rw [getVars_eq_freeVars_idents]
      exact List.mem_map.mpr ⟨(x, none), hmem, rfl⟩
    rw [getVars_eraseTypes] at hvar
    exact hx hvar
  exact LExpr.varClose_of_varOpen hfresh

/-- Rewriting the user-provided type annotations of an expression, with any
    choice of operator annotation, leaves its erasure unchanged. -/
theorem eraseTypes_replaceUserProvidedType {T : LExprParamsT}
    (f : T.TypeType → T.TypeType) (e : LExpr T)
    (opAnnot : Identifier T.base.IDMeta → Option T.TypeType →
      Option T.TypeType := fun _ => Option.map f) :
    (LExpr.replaceUserProvidedType e f opAnnot).eraseTypes = e.eraseTypes := by
  induction e with
  | const m c => simp only [LExpr.replaceUserProvidedType, LExpr.eraseTypes]
  | op m o ty => simp only [LExpr.replaceUserProvidedType, LExpr.eraseTypes]
  | bvar m i => simp only [LExpr.replaceUserProvidedType, LExpr.eraseTypes]
  | fvar m x ty => simp only [LExpr.replaceUserProvidedType, LExpr.eraseTypes]
  | abs m name ty b ih => simp only [LExpr.replaceUserProvidedType,
      LExpr.eraseTypes, ih]
  | quant m qk name ty tr b ihtr ihb =>
    simp only [LExpr.replaceUserProvidedType, LExpr.eraseTypes, ihtr, ihb]
  | app m g a ihg iha => simp only [LExpr.replaceUserProvidedType,
      LExpr.eraseTypes, ihg, iha]
  | ite m c t g ihc iht ihg =>
    simp only [LExpr.replaceUserProvidedType, LExpr.eraseTypes, ihc, iht, ihg]
  | eq m a b iha ihb => simp only [LExpr.replaceUserProvidedType,
      LExpr.eraseTypes, iha, ihb]

/-- Applying a type substitution to the annotations of an expression leaves its
    erasure unchanged. -/
theorem eraseTypes_applyTypeSubst (e : LExpr T.mono) (S : Subst) :
    (LExpr.applyTypeSubst e S).eraseTypes = e.eraseTypes := by
  simp only [LExpr.applyTypeSubst]
  split
  · rfl
  · exact eraseTypes_replaceUserProvidedType _ e

/-- Mapping the annotations of an expression leaves its erasure unchanged. -/
theorem eraseTypes_mapExprTys (f : LMonoTy → LMonoTy) (e : LExpr T.mono) :
    (mapExprTys f e).eraseTypes = e.eraseTypes := by
  simp only [mapExprTys]
  exact eraseTypes_replaceUserProvidedType f e

variable [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A successful `resolveAux` keeps the context nonempty and keeps every known
    variable known. -/
private theorem resolveAux_scoped_after (C : LContext T)
    (Env Env1 : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (L : List T.Identifier)
    (h : resolveAux C Env e = .ok (et, Env1)) (hne : Env.context.types ≠ [])
    (hL : ∀ id ∈ L, id ∈ TContext.knownVars Env.context) :
    Env1.context.types ≠ [] ∧
      ∀ id ∈ L, id ∈ TContext.knownVars Env1.context := by
  have hboth := resolveAux_context_types_ne_equiv C e Env Env1 et h hne
  refine ⟨hboth.1, ?_⟩
  intro id hid
  exact Proofs.mem_knownVars_of_Equiv hboth.2.symm (hL id hid)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- The variable `typeBoundVar` generates is not known in its input context. -/
private theorem typeBoundVar_xv_not_known (C : LContext T) (Env : TEnv T.IDMeta)
    (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    {avoid : List T.Identifier}
    (h : typeBoundVar C Env bty avoid = .ok (xv, xty, Env1)) :
    xv ∉ TContext.knownVars Env.context := by
  have hall := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h
  have hnone := HMaps.find?_of_all_none Env.context.types xv hall
  exact HMaps.find?_of_not_mem_values Env.context.types hnone

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `resolveAux` only adds type annotations: when the free variables of the
    input are bound in the context, erasing the annotations of the `unresolved`
    form of the output gives the erased input. Resolution opens a binder with a
    generated variable and closes it again, so the assumption is needed: an
    input free variable with the generated name would be closed too. -/
private theorem resolveAux_unresolved_eraseTypes (C : LContext T) :
    ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (Env Env' : TEnv T.IDMeta) (et : LExprT T.mono),
        resolveAux C Env e = .ok (et, Env') → Env.context.types ≠ [] →
        (∀ id ∈ LExpr.getVars e, id ∈ TContext.knownVars Env.context) →
        (LExpr.unresolved et).eraseTypes = e.eraseTypes := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e hn Env Env' et h hne hsc
  cases e with
  | const m c =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp only [reduceCtorEq] at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_et, _⟩ := h
      subst h_et
      simp only [LExpr.unresolved, LExpr.eraseTypes]
  | op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    revert h; repeat' split
    all_goals (
      intro h
      simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      try (obtain ⟨h_et, _⟩ := h; subst h_et; simp only [LExpr.unresolved,
          LExpr.eraseTypes]))
  | bvar m i =>
    simp only [resolveAux] at h
    simp only [reduceCtorEq] at h
  | fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp only [reduceCtorEq] at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_et, _⟩ := h
      subst h_et
      simp only [LExpr.unresolved, LExpr.eraseTypes]
  | app m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    rename_i x1 r1 h1 x2 r2 h2 x3 r3 h3 x4 r4 h4
    obtain ⟨e1t, Env1⟩ := r1
    obtain ⟨e2t, Env2⟩ := r2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, _⟩ := h
    subst h_et
    have hsz1 : e1.sizeOf < n := by subst hn; simp only [LExpr.sizeOf]; omega
    have hsz2 : e2.sizeOf < n := by
      subst hn; simp only [LExpr.sizeOf, Nat.lt_add_left_iff_pos]; omega
    have hsc1 : ∀ id ∈ LExpr.getVars e1, id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_left _ hid)
    have hsc2 : ∀ id ∈ LExpr.getVars e2, id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_right _ hid)
    have hstep := resolveAux_scoped_after C Env Env1 e1 e1t _ h1 hne hsc2
    have ih1 := ih e1.sizeOf hsz1 e1 rfl Env Env1 e1t h1 hne hsc1
    have ih2 := ih e2.sizeOf hsz2 e2 rfl Env1 Env2 e2t h2 hstep.1 hstep.2
    simp only [LExpr.unresolved, LExpr.eraseTypes, ih1, ih2]
  | eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    rename_i x1 r1 h1 x2 r2 h2 x3 r3 h3
    obtain ⟨e1t, Env1⟩ := r1
    obtain ⟨e2t, Env2⟩ := r2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, _⟩ := h
    subst h_et
    have hsz1 : e1.sizeOf < n := by subst hn; simp only [LExpr.sizeOf]; omega
    have hsz2 : e2.sizeOf < n := by
      subst hn; simp only [LExpr.sizeOf, Nat.lt_add_left_iff_pos]; omega
    have hsc1 : ∀ id ∈ LExpr.getVars e1, id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_left _ hid)
    have hsc2 : ∀ id ∈ LExpr.getVars e2, id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_right _ hid)
    have hstep := resolveAux_scoped_after C Env Env1 e1 e1t _ h1 hne hsc2
    have ih1 := ih e1.sizeOf hsz1 e1 rfl Env Env1 e1t h1 hne hsc1
    have ih2 := ih e2.sizeOf hsz2 e2 rfl Env1 Env2 e2t h2 hstep.1 hstep.2
    simp only [LExpr.unresolved, LExpr.eraseTypes, ih1, ih2]
  | ite m c th el =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    rename_i x1 r1 h1 x2 r2 h2 x3 r3 h3 x4 r4 h4
    obtain ⟨ct, Env1⟩ := r1
    obtain ⟨tt, Env2⟩ := r2
    obtain ⟨et', Env3⟩ := r3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, _⟩ := h
    subst h_et
    have hsz1 : c.sizeOf < n := by subst hn; simp only [LExpr.sizeOf]; omega
    have hsz2 : th.sizeOf < n := by subst hn; simp only [LExpr.sizeOf]; omega
    have hsz3 : el.sizeOf < n := by
      subst hn; simp only [LExpr.sizeOf, Nat.lt_add_left_iff_pos]; omega
    have hsc1 : ∀ id ∈ LExpr.getVars c, id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_left _ (List.mem_append_left _ hid))
    have hsc2 : ∀ id ∈ LExpr.getVars th, id ∈ TContext.knownVars Env.context :=
      fun id hid =>
        hsc id (List.mem_append_left _ (List.mem_append_right _ hid))
    have hsc3 : ∀ id ∈ LExpr.getVars el, id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_right _ hid)
    have hrest : ∀ id ∈ LExpr.getVars th ++ LExpr.getVars el,
        id ∈ TContext.knownVars Env.context := by
      intro id hid
      rcases List.mem_append.mp hid with hid | hid
      · exact hsc2 id hid
      · exact hsc3 id hid
    have hstep1 := resolveAux_scoped_after C Env Env1 c ct _ h1 hne hrest
    have hsc2' : ∀ id ∈ LExpr.getVars th,
        id ∈ TContext.knownVars Env1.context :=
      fun id hid => hstep1.2 id (List.mem_append_left _ hid)
    have hsc3' : ∀ id ∈ LExpr.getVars el,
        id ∈ TContext.knownVars Env1.context :=
      fun id hid => hstep1.2 id (List.mem_append_right _ hid)
    have hstep2 := resolveAux_scoped_after C Env1 Env2 th tt _ h2 hstep1.1 hsc3'
    have ih1 := ih c.sizeOf hsz1 c rfl Env Env1 ct h1 hne hsc1
    have ih2 := ih th.sizeOf hsz2 th rfl Env1 Env2 tt h2 hstep1.1 hsc2'
    have ih3 := ih el.sizeOf hsz3 el rfl Env2 Env3 et' h3 hstep2.1 hstep2.2
    simp only [LExpr.unresolved, LExpr.eraseTypes, ih1, ih2, ih3]
  | abs m name bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    rename_i x1 r1 h1 x2 r2 h2
    obtain ⟨xv, xty, Env1⟩ := r1
    obtain ⟨bt, Env2⟩ := r2
    dsimp only at h1 h2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, _⟩ := h
    subst h_et
    have hxv := typeBoundVar_xv_not_known C Env bty xv xty Env1 h1
    have hne1 := typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h1
    have hsc_body : ∀ id ∈ LExpr.getVars body,
        id ∈ TContext.knownVars Env.context :=
      hsc
    have hbody_not : xv ∉ LExpr.getVars body :=
      fun hmem => hxv (hsc_body xv hmem)
    have hsc' : ∀ id ∈ LExpr.getVars (LExpr.varOpen 0 (xv, some xty) body),
        id ∈ TContext.knownVars Env1.context := by
      intro id hid
      rcases getVars_varOpen_subset 0 xv (some xty) body id hid with hid | hid
      · subst hid
        exact typeBoundVar_xv_in_knownVars C Env bty id xty Env1 h1
      · exact typeBoundVar_knownVars_mono C Env bty xv xty Env1 h1 id
          (hsc_body id hid)
    have hsz : (LExpr.varOpen 0 (xv, some xty) body).sizeOf < n := by
      subst hn; rw [varOpen_sizeOf]
      simp only [LExpr.sizeOf, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
    have ih' := ih _ hsz _ rfl Env1 Env2 bt h2 hne1 hsc'
    have hclose := varClose_varOpen_eraseTypes 0 xv body hbody_not
    simp only [LExpr.unresolved]
    split <;>
      simp only [LExpr.eraseTypes, eraseTypes_unresolved_varCloseT, ih',
          eraseTypes_varOpen,
        hclose]
  | quant m qk name bty trig body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    rename_i x1 r1 h1 x2 r2 h2 x3 r3 h3 x4 r4 h4
    obtain ⟨xv, xty, Env1⟩ := r1
    obtain ⟨bt, Env2⟩ := r2
    obtain ⟨tt, Env3⟩ := r3
    dsimp only at h1 h2 h3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, _⟩ := h
    subst h_et
    have hxv := typeBoundVar_xv_not_known C Env bty xv xty Env1 h1
    have hne1 := typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h1
    have hsc_trig : ∀ id ∈ LExpr.getVars trig,
        id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_left _ hid)
    have hsc_body : ∀ id ∈ LExpr.getVars body,
        id ∈ TContext.knownVars Env.context :=
      fun id hid => hsc id (List.mem_append_right _ hid)
    have hbody_not : xv ∉ LExpr.getVars body :=
      fun hmem => hxv (hsc_body xv hmem)
    have htrig_not : xv ∉ LExpr.getVars trig :=
      fun hmem => hxv (hsc_trig xv hmem)
    have hopen : ∀ (g : LExpr T.mono),
        (∀ id ∈ LExpr.getVars g, id ∈ TContext.knownVars Env.context) →
        ∀ id ∈ LExpr.getVars (LExpr.varOpen 0 (xv, some xty) g),
          id ∈ TContext.knownVars Env1.context := by
      intro g hg id hid
      rcases getVars_varOpen_subset 0 xv (some xty) g id hid with hid | hid
      · subst hid
        exact typeBoundVar_xv_in_knownVars C Env bty id xty Env1 h1
      · exact typeBoundVar_knownVars_mono C Env bty xv xty Env1 h1 id
          (hg id hid)
    have hsz_body : (LExpr.varOpen 0 (xv, some xty) body).sizeOf < n := by
      subst hn; rw [varOpen_sizeOf]; simp only [LExpr.sizeOf]; omega
    have hsz_trig : (LExpr.varOpen 0 (xv, some xty) trig).sizeOf < n := by
      subst hn; rw [varOpen_sizeOf]; simp only [LExpr.sizeOf,
          Nat.lt_add_left_iff_pos]; omega
    have hstep := resolveAux_scoped_after C Env1 Env2 _ bt _ h2 hne1
      (hopen trig hsc_trig)
    have ihb := ih _ hsz_body _ rfl Env1 Env2 bt h2 hne1 (hopen body hsc_body)
    have iht := ih _ hsz_trig _ rfl Env2 Env3 tt h3 hstep.1 hstep.2
    have hclose_b := varClose_varOpen_eraseTypes 0 xv body hbody_not
    have hclose_t := varClose_varOpen_eraseTypes 0 xv trig htrig_not
    simp only [LExpr.unresolved, LExpr.eraseTypes,
        eraseTypes_unresolved_varCloseT, ihb, iht,
      eraseTypes_varOpen, hclose_b, hclose_t]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Resolving an expression whose free variables are bound in the context only
    adds type annotations: the output, with its annotations erased, is the
    erased input. Without the scoping assumption this fails: an input free
    variable named like the variable `resolve` generates for a binder is closed
    together with it. -/
theorem resolve_unresolved_eraseTypes (C : LContext T)
    (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (hsc : ∀ id ∈ LExpr.getVars e,
      id ∈ TContext.knownVars Env.context) :
    (LExpr.unresolved et).eraseTypes = e.eraseTypes := by
  obtain ⟨Env0, etAux, haux, hsub, _, hne0, _, h0⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have hsc0 : ∀ id ∈ LExpr.getVars e, id ∈ TContext.knownVars Env0.context :=
    fun id hid =>
      (Proofs.resolve_init_knownVars Env Env0 h0 id).mpr (hsc id hid)
  have hmain := resolveAux_unresolved_eraseTypes C e.sizeOf e rfl Env0 Env'
    etAux haux hne0 hsc0
  subst hsub
  rw [eraseTypes_unresolved_applySubstT]
  exact hmain

end LExpr

end

end Lambda
