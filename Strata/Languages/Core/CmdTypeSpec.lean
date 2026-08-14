/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.Cmd

/-! ## Declarative Typing Specification for Imperative Commands

This file specifies when an `Imperative.Cmd Expression` is well-typed.

The specifications are parameterized via the `ExprTypingSpec` typeclass, which
bundles a type universe and an expression typing predicate. Two instances are
provided:
- `instHasType` — uses `HasType` (polymorphic, Hindley-Milner), `τ = LTy`
- `instHasTypeA` — uses `HasTypeA` (annotated, monomorphic), `τ = LMonoTy`
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- Typeclass bundling the type universe and expression typing predicate.
    `τ` is the type universe (`LTy` for HasType, `LMonoTy` for HasTypeA`). -/
class ExprTypingSpec (τ : Type) where
  embed : LMonoTy → τ
  exprTyped : LContext CoreLParams → TContext Unit → Expression.Expr → τ → Prop
  /-- Matches a declared/annotation signature type against a resolved one. For
      `HasType` a signature may still contain aliases, so it is alias-equivalence;
      for `HasTypeA` types are already resolved, so it is equality. -/
  tyCompat : List TypeAlias → LMonoTy → LMonoTy → Prop

instance instHasType : ExprTypingSpec LTy where
  embed := fun mty => .forAll [] mty
  exprTyped := fun C => HasType C
  tyCompat := AliasEquiv

instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty
  tyCompat := fun _ ty ty' => ty = ty'

/--
Declarative typing for imperative commands, parameterized over `ExprTypingSpec`.
-/
inductive CmdHasType' (C : LContext CoreLParams) [S : ExprTypingSpec τ] :
    TContext Unit → Cmd Expression → TContext Unit → Prop where

  /-- `var x : T := e` — `x` must be fresh, and the stored monotype `mty` must be
      an instantiation of `T` up to `RigidAnnotCompat` and well-kinded.

      The output `Δ` is required only up to `TContext.Equiv` with the canonical
      `insert`-form: the `HMap`-backed context ignores key/insertion order, so
      structural equality is too strong. This holds for every constructor below. -/
  | init_det : ∀ Γ x (xty : LTy) e mty tys md Δ,
      Γ.types.find? x = none →
      x ∉ HasVarsPure.getVars (P := Expression) e →
      tys.length = xty.boundVars.length →
      RigidAnnotCompat Γ.aliases C.rigidTypeVars (LTy.openFull xty tys) mty →
      C.WellKindedTy mty →
      S.exprTyped C Γ e (S.embed mty) →
      TContext.Equiv (T := CoreLParams) Δ { Γ with types := Γ.types.insert x (.forAll [] mty) } →
      CmdHasType' C Γ (.init x xty (.det e) md) Δ

  /-- `var x : T := *` — `x` must be fresh, and `mty` must be an instantiation of
      `T` up to `RigidAnnotCompat` and well-kinded (as in `init_det`). Output up
      to `Equiv`. -/
  | init_nondet : ∀ Γ x (xty : LTy) mty tys md Δ,
      Γ.types.find? x = none →
      tys.length = xty.boundVars.length →
      RigidAnnotCompat Γ.aliases C.rigidTypeVars (LTy.openFull xty tys) mty →
      C.WellKindedTy mty →
      TContext.Equiv (T := CoreLParams) Δ { Γ with types := Γ.types.insert x (.forAll [] mty) } →
      CmdHasType' C Γ (.init x xty .nondet md) Δ

  /-- `x := e` — `x` must exist with mono type `mty`, and `e` must have that type.
      Output up to `Equiv` with the (unchanged) input context. -/
  | set_det : ∀ Γ x mty e md Δ,
      Γ.types.find? x = some (.forAll [] mty) →
      S.exprTyped C Γ e (S.embed mty) →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      CmdHasType' C Γ (.set x (.det e) md) Δ

  /-- `x := *` — `x` must exist in context with a mono type. Output up to `Equiv`. -/
  | set_nondet : ∀ Γ x mty md Δ,
      Γ.types.find? x = some (.forAll [] mty) →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      CmdHasType' C Γ (.set x .nondet md) Δ

  /-- `assert l e` — `e` must have type `bool`. Output up to `Equiv`. -/
  | assert : ∀ Γ l e md Δ,
      S.exprTyped C Γ e (S.embed .bool) →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      CmdHasType' C Γ (.assert l e md) Δ

  /-- `assume l e` — `e` must have type `bool`. Output up to `Equiv`. -/
  | assume : ∀ Γ l e md Δ,
      S.exprTyped C Γ e (S.embed .bool) →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      CmdHasType' C Γ (.assume l e md) Δ

  /-- `cover l e` — `e` must have type `bool`. Output up to `Equiv`. -/
  | cover : ∀ Γ l e md Δ,
      S.exprTyped C Γ e (S.embed .bool) →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      CmdHasType' C Γ (.cover l e md) Δ

/-- `CmdHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev CmdHasType (C : LContext CoreLParams) :=
  @CmdHasType' LTy C instHasType

/-- `CmdHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev CmdHasTypeA (C : LContext CoreLParams) :=
  @CmdHasType' LMonoTy C instHasTypeA

end -- public section

end TypeSpec
end Core
