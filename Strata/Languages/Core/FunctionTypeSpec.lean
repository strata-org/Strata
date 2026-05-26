/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.Languages.Core.Function

/-! ## Declarative Typing Specification for Functions

Specifies when a `Function` (i.e., `LFunc CoreLParams`) is well-typed using
`HasType` rather than `LExpr.resolve`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/--
Declarative typing for functions.

A function is well-typed if its body (when present) has the declared return type
in a context extended with the formal parameters, and its measure (when present)
has type `int`.
-/
structure FuncHasType (C : LContext CoreLParams) (func : Function) : Prop where
  /-- If a body exists, it has the declared return type in the input context. -/
  bodyTyped : ∀ body, func.body = some body →
    ∃ (Γ : TContext Unit),
      (∀ x, ListMap.find? func.inputs x = some ty →
        Γ.types.find? x = some (.forAll [] ty)) ∧
      HasType C Γ body (.forAll [] func.output)
  /-- If a measure exists and is not a simple variable, it has type `int`. -/
  measureTyped : ∀ m, func.measure = some m →
    ∀ (Γ : TContext Unit),
      (∀ x ty, ListMap.find? func.inputs x = some ty →
        Γ.types.find? x = some (.forAll [] ty)) →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      HasType C Γ m (.forAll [] .int)

end -- public section

end TypeSpec
end Core
