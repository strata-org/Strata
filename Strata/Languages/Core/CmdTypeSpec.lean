/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.Cmd

/-! ## Declarative Typing Specification for Imperative Commands

This file specifies when an `Imperative.Cmd Expression` is well-typed,
using `HasType` rather than `LExpr.resolve`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/--
Declarative typing for imperative commands.

`CmdHasType C Γ cmd Γ'` asserts that command `cmd` is well-typed in context
`C` with type environment `Γ`, and produces an updated type environment `Γ'`.
-/
inductive CmdHasType (C : LContext CoreLParams) :
    TContext Unit → Cmd Expression → TContext Unit → Prop where

  /-- `var x : T := e` — `x` must be fresh, `e` must have a type unifiable with `T`. -/
  | init_det : ∀ Γ x xty e mty md,
      Γ.types.find? x = none →
      x ∉ HasVarsPure.getVars (P := Expression) e →
      HasType C Γ e (.forAll [] mty) →
      AliasEquiv Γ.aliases xty mty →
      CmdHasType C Γ (.init x (.forAll [] xty) (.det e) md)
        { Γ with types := Γ.types.insert x (.forAll [] mty) }

  /-- `var x : T := *` — `x` must be fresh. -/
  | init_nondet : ∀ Γ x xty mty md,
      Γ.types.find? x = none →
      AliasEquiv Γ.aliases xty mty →
      CmdHasType C Γ (.init x (.forAll [] xty) .nondet md)
        { Γ with types := Γ.types.insert x (.forAll [] mty) }

  /-- `x := e` — `x` must exist with type `T`, and `e` must have type `T`. -/
  | set_det : ∀ Γ x xty e md,
      Γ.types.find? x = some xty →
      HasType C Γ e xty →
      CmdHasType C Γ (.set x (.det e) md) Γ

  /-- `x := *` — `x` must exist in context. -/
  | set_nondet : ∀ Γ x xty md,
      Γ.types.find? x = some xty →
      CmdHasType C Γ (.set x .nondet md) Γ

  /-- `assert l e` — `e` must have type `bool`. -/
  | assert : ∀ Γ l e md,
      HasType C Γ e (.forAll [] .bool) →
      CmdHasType C Γ (.assert l e md) Γ

  /-- `assume l e` — `e` must have type `bool`. -/
  | assume : ∀ Γ l e md,
      HasType C Γ e (.forAll [] .bool) →
      CmdHasType C Γ (.assume l e md) Γ

  /-- `cover l e` — `e` must have type `bool`. -/
  | cover : ∀ Γ l e md,
      HasType C Γ e (.forAll [] .bool) →
      CmdHasType C Γ (.cover l e md) Γ

end -- public section

end TypeSpec
end Core
