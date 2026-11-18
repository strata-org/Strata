/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.Cmd
public import Strata.Languages.Core.Typing.Spec.TypeSpecShared

/-! ## The Typechecker Spec for Imperative Commands

This file gives the typechecker spec for an `Imperative.Cmd Expression`. Expressions are typed
with `HasType` (polymorphic, Hindley-Milner), and their written annotations are constrained.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The type each written type variable bound in the current scope denotes. -/
abbrev WrittenEnv := TyIdentifier → Option LMonoTy

/-- Every free-variable annotation in `e` is a valid source type under `aliases` and `adm`. -/
def FVarAnnotsWF (C : LContext CoreLParams) (adm : TyVarAdmissibility)
    (aliases : List TypeAlias) (e : Expression.Expr) : Prop :=
  ∀ t ∈ LExpr.fvarAnnotations e, ∃ r, SourceTyWF C adm aliases t r

/-- Every type variable of a binder annotation in `e`, with aliases unresolved, satisfies `adm`. -/
def BinderAnnotTyVarsAdmissible (adm : TyVarAdmissibility)
    (e : Expression.Expr) : Prop :=
  ∀ t ∈ LExpr.binderAnnotations e, ∀ v ∈ LMonoTy.freeVars t, adm v = true

/-- The annotations written in a source expression are valid source types over user-writable
    type variables. -/
def WrittenAnnotsOk (C : LContext CoreLParams) (Γ : TContext Unit)
    (e : Expression.Expr) : Prop :=
  FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid Γ.aliases e ∧
    BinderAnnotTyVarsAdmissible TyVarAdmissibility.notGeneratedOrRigid e

/-- Every type variable of a free-variable or binder annotation in `e` is in `rigid` or bound
    in `Δ`. Operator annotations are not scoped: their type variables are the operator's own. -/
def AnnotsInScope (rigid : List TyIdentifier)
    (Δ : TyIdentifier → Option LMonoTy) (e : Expression.Expr) : Prop :=
  ∀ t ∈ LExpr.fvarAnnotations e ++ LExpr.binderAnnotations e,
    ∀ v ∈ LMonoTy.freeVars t, v ∈ rigid ∨ (Δ v).isSome

/-- `t` with each type variable `v` a user may write and `Δ` binds replaced by `Δ v`. -/
def instAnnotTy (Δ : TyIdentifier → Option LMonoTy) (t : LMonoTy) : LMonoTy :=
  LMonoTy.subst [restrictTo (readTyVar Δ) t] t

/-- `e` with every free-variable and binder annotation read through `Δ` (`instAnnotTy`). -/
def instAnnots (Δ : TyIdentifier → Option LMonoTy) :
    Expression.Expr → Expression.Expr
  | .fvar md x ty => .fvar md x (ty.map (instAnnotTy Δ))
  | .abs md n ty b => .abs md n (ty.map (instAnnotTy Δ)) (instAnnots Δ b)
  | .quant md k n ty tr b =>
    .quant md k n (ty.map (instAnnotTy Δ)) (instAnnots Δ tr) (instAnnots Δ b)
  | .app md f a => .app md (instAnnots Δ f) (instAnnots Δ a)
  | .ite md c t f => .ite md (instAnnots Δ c) (instAnnots Δ t) (instAnnots Δ f)
  | .eq md a b => .eq md (instAnnots Δ a) (instAnnots Δ b)
  | .const md c => .const md c
  | .op md o ty => .op md o ty
  | .bvar md i => .bvar md i

/-- `σ` sends each type variable of `ann` that `Δ` binds to its binding. -/
abbrev SubstAgreesWith (Δ : WrittenEnv) (σ : SubstOne) (ann : LMonoTy) : Prop :=
  ∀ v ∈ LMonoTy.freeVars ann, ∀ t, Δ v = some t → LMonoTy.subst [σ] (.ftvar v) = t

/-- `σ` instantiates `ann` to `mty` up to aliases, fixes every rigid type variable, and sends
    each type variable of `ann` that `Δ` binds to its binding. -/
def ScopedAnnotInst (aliases : List TypeAlias) (rigid : List TyIdentifier)
    (Δ : WrittenEnv) (σ : SubstOne) (ann mty : LMonoTy) : Prop :=
  SubstFixesRigid rigid σ ∧ SubstAgreesWith Δ σ ann ∧
  AliasEquiv aliases (LMonoTy.subst [σ] ann) mty

/-! ### Written type variables in scope

A written type variable denotes one type until its block, branch or loop body ends. -/

/-- `Δ` extended by binding each non-rigid type variable of `ann` it does not bind to its
    `σ`-instance. -/
def WrittenEnv.bindFirst (Δ : WrittenEnv) (rigid : List TyIdentifier)
    (ann : LMonoTy) (σ : SubstOne) : WrittenEnv := fun v =>
  match Δ v with
  | some t => some t
  | none =>
    if v ∈ LMonoTy.freeVars ann ∧ v ∉ rigid then some (LMonoTy.subst [σ] (.ftvar v)) else none

/-- The typechecker spec for commands, threading the environment `Δ` of written type variables.
    Expressions are typed as read through `Δ` (`instAnnots`), and the type variables of their
    annotations are rigid or bound in `Δ`. A declaration instantiates its type consistently with
    `Δ` and binds the variables it uses first, which its initializer sees; every other command
    leaves `Δ` unchanged. -/
inductive CmdHasType (C : LContext CoreLParams) :
    WrittenEnv → TContext Unit → Cmd Expression → TContext Unit → WrittenEnv → Prop where
  /-- `var x : T := e` — `x` must be fresh, not named like a function, `T` a valid declared
      monotype `T₀` (user-writable type variables only) admitting the stored monotype `mty`
      through an instantiation agreeing with `Δ`, and `mty` well-kinded.

      The output `Γ'` is required only up to `TContext.Equiv` with the canonical
      `insert`-form: the `HMap`-backed context ignores key/insertion order, so
      structural equality is too strong. This holds for every constructor below. -/
  | init_det : ∀ Δ Γ x (xty : LTy) e mty mty₀ σ md Γ',
      Γ.types.find? x = none →
      x.name ∉ C.functions →
      x ∉ HasFvars.getFvars (P := Expression) e →
      xty = .forAll [] mty₀ →
      ScopedAnnotInst Γ.aliases C.rigidTypeVars Δ σ mty₀ mty ∧
        ValidDeclaredTy C Γ.aliases mty₀ →
      C.WellKindedTy mty →
      HasType C Γ (instAnnots (Δ.bindFirst C.rigidTypeVars mty₀ σ) e) (.forAll [] mty) →
      WrittenAnnotsOk C Γ e →
      AnnotsInScope C.rigidTypeVars (Δ.bindFirst C.rigidTypeVars mty₀ σ) e →
      TContext.Equiv (T := CoreLParams) Γ' { Γ with types := Γ.types.insert x (.forAll [] mty) } →
      CmdHasType C Δ Γ (.init x xty (.det e) md) Γ' (Δ.bindFirst C.rigidTypeVars mty₀ σ)
  /-- `var x : T := *` — as `init_det`, with no initializer. -/
  | init_nondet : ∀ Δ Γ x (xty : LTy) mty mty₀ σ md Γ',
      Γ.types.find? x = none →
      x.name ∉ C.functions →
      xty = .forAll [] mty₀ →
      ScopedAnnotInst Γ.aliases C.rigidTypeVars Δ σ mty₀ mty ∧
        ValidDeclaredTy C Γ.aliases mty₀ →
      C.WellKindedTy mty →
      TContext.Equiv (T := CoreLParams) Γ' { Γ with types := Γ.types.insert x (.forAll [] mty) } →
      CmdHasType C Δ Γ (.init x xty .nondet md) Γ' (Δ.bindFirst C.rigidTypeVars mty₀ σ)
  /-- `x := e` — `x` must exist with mono type `mty`, and `e` must have that type.
      Output up to `Equiv` with the (unchanged) input context. -/
  | set_det : ∀ Δ Γ x mty e md Γ',
      Γ.types.find? x = some (.forAll [] mty) →
      HasType C Γ (instAnnots Δ e) (.forAll [] mty) →
      WrittenAnnotsOk C Γ e →
      AnnotsInScope C.rigidTypeVars Δ e →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      CmdHasType C Δ Γ (.set x (.det e) md) Γ' Δ
  /-- `x := *` — `x` must exist in context with a mono type. Output up to `Equiv`. -/
  | set_nondet : ∀ Δ Γ x mty md Γ',
      Γ.types.find? x = some (.forAll [] mty) →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      CmdHasType C Δ Γ (.set x .nondet md) Γ' Δ
  /-- `assert l e` — `e` must have type `bool`. Output up to `Equiv`. -/
  | assert : ∀ Δ Γ l e md Γ',
      HasType C Γ (instAnnots Δ e) (.forAll [] .bool) →
      WrittenAnnotsOk C Γ e →
      AnnotsInScope C.rigidTypeVars Δ e →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      CmdHasType C Δ Γ (.assert l e md) Γ' Δ
  /-- `assume l e` — `e` must have type `bool`. Output up to `Equiv`. -/
  | assume : ∀ Δ Γ l e md Γ',
      HasType C Γ (instAnnots Δ e) (.forAll [] .bool) →
      WrittenAnnotsOk C Γ e →
      AnnotsInScope C.rigidTypeVars Δ e →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      CmdHasType C Δ Γ (.assume l e md) Γ' Δ
  /-- `cover l e` — `e` must have type `bool`. Output up to `Equiv`. -/
  | cover : ∀ Δ Γ l e md Γ',
      HasType C Γ (instAnnots Δ e) (.forAll [] .bool) →
      WrittenAnnotsOk C Γ e →
      AnnotsInScope C.rigidTypeVars Δ e →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      CmdHasType C Δ Γ (.cover l e md) Γ' Δ

end -- public section

end TypeSpec
end Core
