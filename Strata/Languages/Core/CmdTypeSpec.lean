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

instance instHasType : ExprTypingSpec LTy where
  embed := fun mty => .forAll [] mty
  exprTyped := fun C => HasType C

instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty

/--
Declarative typing for imperative commands, parameterized over `ExprTypingSpec`.
-/
inductive CmdHasType' (C : LContext CoreLParams) [S : ExprTypingSpec τ] :
    TContext Unit → Cmd Expression → TContext Unit → Prop where

  /-- `var x : T := e` — `x` must be fresh, `e` must have a type unifiable with `T`. -/
  | init_det : ∀ Γ x (xty : LTy) e mty md,
      Γ.types.find? x = none →
      x ∉ HasVarsPure.getVars (P := Expression) e →
      S.exprTyped C Γ e (S.embed mty) →
      CmdHasType' C Γ (.init x xty (.det e) md)
        { Γ with types := Γ.types.insert x (.forAll [] mty) }

  /-- `var x : T := *` — `x` must be fresh. -/
  | init_nondet : ∀ Γ x (xty : LTy) mty md,
      Γ.types.find? x = none →
      CmdHasType' C Γ (.init x xty .nondet md)
        { Γ with types := Γ.types.insert x (.forAll [] mty) }

  /-- `x := e` — `x` must exist with mono type `mty`, and `e` must have that type. -/
  | set_det : ∀ Γ x mty e md,
      Γ.types.find? x = some (.forAll [] mty) →
      S.exprTyped C Γ e (S.embed mty) →
      CmdHasType' C Γ (.set x (.det e) md) Γ

  /-- `x := *` — `x` must exist in context with a mono type. -/
  | set_nondet : ∀ Γ x mty md,
      Γ.types.find? x = some (.forAll [] mty) →
      CmdHasType' C Γ (.set x .nondet md) Γ

  /-- `assert l e` — `e` must have type `bool`. -/
  | assert : ∀ Γ l e md,
      S.exprTyped C Γ e (S.embed .bool) →
      CmdHasType' C Γ (.assert l e md) Γ

  /-- `assume l e` — `e` must have type `bool`. -/
  | assume : ∀ Γ l e md,
      S.exprTyped C Γ e (S.embed .bool) →
      CmdHasType' C Γ (.assume l e md) Γ

  /-- `cover l e` — `e` must have type `bool`. -/
  | cover : ∀ Γ l e md,
      S.exprTyped C Γ e (S.embed .bool) →
      CmdHasType' C Γ (.cover l e md) Γ

/-- `CmdHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev CmdHasType (C : LContext CoreLParams) :=
  @CmdHasType' LTy C instHasType

/-- `CmdHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev CmdHasTypeA (C : LContext CoreLParams) :=
  @CmdHasType' LMonoTy C instHasTypeA

/-- All context types are monomorphic (have empty bound variables).
In Core this always holds: `preprocess` instantiates poly annotations, and
`update`/`postprocess` stores only `forAll [] _`. -/
@[expose] def ContextMono (Γ : TContext Unit) : Prop :=
  ∀ x ty, Γ.types.find? x = some ty → LTy.boundVars ty = []

end -- public section

end TypeSpec
end Core
