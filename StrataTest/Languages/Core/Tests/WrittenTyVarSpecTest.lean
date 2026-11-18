/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Imperative.Cmd

/-! ## Written type variables in the typechecker spec

A type variable written in a declaration scopes over the rest of its block, and a type
annotation never binds one. `var x : a := *` followed by `assume l ((x : a) == (x : a))` is
accepted by the statement relation of the typechecker spec that threads written type variables;
the same assume after `var x : int := *`, with no declaration of `a`, is rejected.
-/

namespace Core.WrittenTyVarSpecTest

open Lambda Imperative Core.TypeSpec

/-- The empty program. -/
private def prog : Program := { decls := [] }

/-- The context with no known functions. -/
private def ctx : LContext CoreLParams := LContext.default

/-- The type scope with no variables or aliases. -/
private def emptyScope : TContext Unit := {}

/-- The variable `x`. -/
private def xId : Expression.Ident := ⟨"x", ()⟩

/-- The written type variable `a`. -/
private def aTy : LMonoTy := .ftvar "a"

/-- `(x : a) == (x : a)`. -/
private def eqXX : Expression.Expr :=
  .eq Core.valueLoc (.fvar Core.valueLoc xId (some aTy)) (.fvar Core.valueLoc xId (some aTy))

/-- `var x : ty := *`. -/
private def declX (ty : LMonoTy) : Statement :=
  .cmd (.cmd (.init xId (.forAll [] ty) .nondet .empty))

/-- `assume l ((x : a) == (x : a))`. -/
private def assumeXX : Statement :=
  .cmd (.cmd (.assume "l" eqXX .empty))

/-- The scope after declaring `x` at the monotype `ty`. -/
private def scopeX (ty : LMonoTy) : TContext Unit :=
  { emptyScope with types := emptyScope.types.insert xId (.forAll [] ty) }

/-- The written type variables after `var x : a := *`: `a` denotes itself. -/
private def envA : WrittenEnv :=
  WrittenEnv.bindFirst (fun _ => none) ctx.rigidTypeVars aTy Strata.Util.HMap.empty

/-- A type that applies no type constructor is well kinded. -/
private theorem wellKinded_ftvar (v : TyIdentifier) : ctx.WellKindedTy (.ftvar v) := by
  intro ref n hmem
  simp only [getTypeConsArities, List.not_mem_nil] at hmem

/-- `var x : a := *` declares `x` at `a` and binds `a` to itself. -/
private theorem declA_typed :
    StatementHasType prog ctx emptyScope (fun _ => none) [] (declX aTy)
      ctx (scopeX aTy) envA := by
  have hfind : emptyScope.types.find? xId = none := rfl
  have hfun : xId.name ∉ ctx.functions := Factory.default_empty _
  have hdecl : ScopedAnnotInst emptyScope.aliases ctx.rigidTypeVars (fun _ => none)
      Strata.Util.HMap.empty aTy aTy ∧ ValidDeclaredTy ctx emptyScope.aliases aTy := by
    refine ⟨⟨(fun v hv => nomatch hv), fun _ _ t hbound => ?_, ?_⟩, ?_⟩
    · have hcontra : (none : Option LMonoTy) = some t := hbound
      cases hcontra
    · rw [LMonoTy.subst_single_empty]
      exact AliasEquiv.refl
    · have hadm : TyVarAdmissibility.notGeneratedOrRigid "a" = true := by
        decide
      exact ⟨aTy, ⟨.ftvar, .ftvar hadm⟩⟩
  exact .cmd _ _ _ _ _ _ _ _
    (.cmd _ _ _ _ _
      (.init_nondet _ _ xId (.forAll [] aTy) aTy aTy Strata.Util.HMap.empty .empty (scopeX aTy)
        hfind hfun rfl hdecl (wellKinded_ftvar "a") (TContext.Equiv.refl _)))
    (TContext.Equiv.refl _)

/-- The type variable `a` occurs free in the type `a`. -/
private theorem a_mem_freeVars : "a" ∈ LMonoTy.freeVars aTy := by
  simp [aTy, LMonoTy.freeVars]

/-- Reading the annotations of `(x : a) == (x : a)` through `a := a` changes nothing. -/
private theorem instAnnots_eqXX : instAnnots envA eqXX = eqXX := by
  have hread : readTyVar envA "a" = aTy := by
    unfold readTyVar
    split <;> simp [envA, WrittenEnv.bindFirst, aTy, ctx, LContext.default, LMonoTy.freeVars,
      LMonoTy.subst_single_empty]
  have hfind : Strata.Util.HMaps.find? [restrictTo (readTyVar envA) aTy] "a" = some aTy := by
    rw [Strata.Util.HMaps.find?_single_scope, restrictTo,
      LExpr.find?_buildSubstFromFunction _ _ "a" a_mem_freeVars, hread]
  have hty : instAnnotTy envA aTy = aTy := by
    rw [instAnnotTy]
    exact LMonoTy.subst_ftvar_of_some hfind
  simp only [eqXX, instAnnots, Option.map_some, hty]

/-- `(x : a) == (x : a)` is a boolean once `x` is declared at `a`. -/
private theorem eqXX_typed : LExpr.HasType ctx (scopeX aTy) eqXX (.forAll [] .bool) := by
  have hx : LExpr.HasType ctx (scopeX aTy) (.fvar Core.valueLoc xId (some aTy))
      (.forAll [] aTy) := by
    refine .tvar_annotated _ _ _ (.forAll [] aTy) aTy [] aTy ?_ rfl ?_ LExpr.AnnotCompat.of_eq
    · show (emptyScope.types.insert xId (.forAll [] aTy)).find? xId = _
      exact Strata.Util.HMaps.find?_insert_self _ _ _
    · exact openFull_forAll_nil _ _
  exact .teq _ _ _ _ _ hx hx

/-- The written annotations of `(x : a) == (x : a)` are valid. -/
private theorem annotsOk_eqXX :
    WrittenAnnotsOk ctx (scopeX aTy) eqXX := by
  have hadm : TyVarAdmissibility.notGeneratedOrRigid "a" = true := by
    decide
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [eqXX, LExpr.fvarAnnotations, Option.toList_some, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at ht
    subst ht
    exact ⟨aTy, ⟨.ftvar, .ftvar hadm⟩⟩
  · simp only [eqXX, LExpr.binderAnnotations, List.append_nil, List.not_mem_nil] at ht

/-- The type variable `a` of `(x : a) == (x : a)` is bound by the declaration of `x`. -/
private theorem scoped_eqXX :
    AnnotsInScope ctx.rigidTypeVars envA eqXX := by
  intro t ht v hv
  simp only [eqXX, LExpr.fvarAnnotations, LExpr.binderAnnotations, Option.toList_some,
    List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false, or_self] at ht
  subst ht
  simp only [aTy, LMonoTy.freeVars, List.mem_singleton] at hv
  subst hv
  right
  simp [envA, WrittenEnv.bindFirst, aTy, ctx, LContext.default, LMonoTy.freeVars]

/-- The assumption after `var x : a := *` is typed and its type variable is in scope. -/
private theorem assumeXX_typed :
    StatementHasType prog ctx (scopeX aTy) envA [] assumeXX
      ctx (scopeX aTy) envA := by
  have htype : LExpr.HasType ctx (scopeX aTy) (instAnnots envA eqXX) (.forAll [] .bool) := by
    rw [instAnnots_eqXX]
    exact eqXX_typed
  exact .cmd _ _ _ _ _ _ _ _
    (.cmd _ _ _ _ _
      (.assume _ _ _ _ _ _ htype annotsOk_eqXX scoped_eqXX (TContext.Equiv.refl _)))
    (TContext.Equiv.refl _)

/-- The block `var x : a := *; assume l ((x : a) == (x : a))` is accepted. -/
example : ∃ C' Γ' Δ',
    StatementsHasType prog ctx emptyScope (fun _ => none) []
      [declX aTy, assumeXX] C' Γ' Δ' :=
  ⟨ctx, scopeX aTy, envA,
    .cons _ _ _ _ _ _ _ _ _ _ _ _ declA_typed
      (.cons _ _ _ _ _ _ _ _ _ _ _ _ assumeXX_typed (.nil _ _ _ _ _ (TContext.Equiv.refl _)))⟩

/-- After `var x : int := *`, the context is unchanged and no written type variable is
    bound. -/
private theorem declInt_binds_nothing {C1 : LContext CoreLParams} {Γ1 : TContext Unit}
    {Δ1 : WrittenEnv}
    (h : StatementHasType prog ctx emptyScope (fun _ => none) [] (declX .int) C1 Γ1 Δ1) :
    C1 = ctx ∧ ∀ v, (Δ1 v).isSome = false :=
  match h with
  | .cmd _ _ _ _ _ _ _ _
      (.cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ _ _ hxty _ _ _)) _ => by
    refine ⟨rfl, fun v => ?_⟩
    cases hxty
    simp [WrittenEnv.bindFirst, LMonoTy.freeVars, LMonoTys.freeVars]

/-- Typing `assume l ((x : a) == (x : a))` after a block that binds no written type variable
    is impossible. -/
private theorem assumeXX_unbound {C2 : LContext CoreLParams} {Γ1 Γ2 : TContext Unit}
    {Δ1 Δ2 : WrittenEnv} (hnone : ∀ v, (Δ1 v).isSome = false)
    (h : StatementHasType prog ctx Γ1 Δ1 [] assumeXX C2 Γ2 Δ2) : False :=
  match h with
  | .cmd _ _ _ _ _ _ _ _ (.cmd _ _ _ _ _ (.assume _ _ _ _ _ _ _ _ hscope _)) _ => by
    have hann : aTy ∈ LExpr.fvarAnnotations eqXX ++ LExpr.binderAnnotations eqXX := by
      simp [eqXX, LExpr.fvarAnnotations, aTy]
    have hbound := hscope aTy hann "a" a_mem_freeVars
    rcases hbound with hrigid | hbind
    · simp [ctx, LContext.default] at hrigid
    · simp [hnone] at hbind

/-- The block `var x : int := *; assume l ((x : a) == (x : a))` is rejected: the annotation `a`
    is bound by no declaration. -/
example : ¬ ∃ C' Γ' Δ',
    StatementsHasType prog ctx emptyScope (fun _ => none) []
      [declX .int, assumeXX] C' Γ' Δ' := by
  rintro ⟨C', Γ', Δ', h⟩
  match h with
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ hdecl (.cons _ _ _ _ _ _ _ _ _ _ _ _ hassume _) =>
    obtain ⟨hctx, hnone⟩ := declInt_binds_nothing hdecl
    subst hctx
    exact assumeXX_unbound hnone hassume

/-- The type variable `$__ty0`, which uses the checker's generated prefix. -/
private def genTy : LMonoTy := .ftvar "$__ty0"

/-- The type variable `$__rigid_a`, which uses the checker's rigid prefix. -/
private def rigidTy : LMonoTy := .ftvar "$__rigid_a"

/-- Typing `var x : v := *` is impossible when `v` is a reserved type-variable name. -/
private theorem declReserved_untypable {v : TyIdentifier}
    (hreserved : TyVarAdmissibility.notGeneratedOrRigid v = false)
    {C1 : LContext CoreLParams} {Γ1 : TContext Unit} {Δ1 : WrittenEnv}
    (h : StatementHasType prog ctx emptyScope (fun _ => none) [] (declX (.ftvar v))
      C1 Γ1 Δ1) :
    False :=
  match h with
  | .cmd _ _ _ _ _ _ _ _
      (.cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ _ _ hxty hdecl _ _)) _ => by
    cases hxty
    obtain ⟨-, r, hwf⟩ := hdecl
    obtain ⟨hresolve, htype⟩ := hwf
    cases hresolve
    cases htype with
    | ftvar hadm => exact Bool.false_ne_true (hreserved.symm.trans hadm)

/-- `var x : $__ty0 := *` is rejected: a declared type may not use a generated type
    variable. -/
example : ¬ ∃ C' Γ' Δ',
    StatementHasType prog ctx emptyScope (fun _ => none) [] (declX genTy) C' Γ' Δ' :=
  fun ⟨_, _, _, h⟩ => declReserved_untypable (v := "$__ty0") (by decide) h

/-- `var x : $__rigid_a := *` is rejected: a declared type may not use a rigid type
    variable. -/
example : ¬ ∃ C' Γ' Δ',
    StatementHasType prog ctx emptyScope (fun _ => none) [] (declX rigidTy) C' Γ' Δ' :=
  fun ⟨_, _, _, h⟩ => declReserved_untypable (v := "$__rigid_a") (by decide) h

end Core.WrittenTyVarSpecTest
