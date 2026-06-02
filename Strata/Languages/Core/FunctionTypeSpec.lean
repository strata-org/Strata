/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CmdTypeSpec
public import Strata.Languages.Core.Function

/-! ## Declarative Typing Specification for Functions

Specifies when a `Function` (i.e., `LFunc CoreLParams`) is well-typed,
parameterized over the `ExprTypingSpec` typeclass.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/--
Declarative typing for functions, parameterized over `ExprTypingSpec`.

A function is well-typed if its body (when present) has the declared return type
in a context extended with the formal parameters, and its measure (when present)
has type `int`.
-/
structure FuncHasType' (τ : Type) [S : ExprTypingSpec τ]
    (C : LContext CoreLParams) (func : Function) : Prop where
  /-- If a body exists, it has the declared return type in the input context. -/
  bodyTyped : ∀ body, func.body = some body →
    ∃ (Γ : TContext Unit),
      (∀ x, ListMap.find? func.inputs x = some ty →
        Γ.types.find? x = some (.forAll [] ty)) ∧
      S.exprTyped C Γ body (S.embed func.output)
  /-- If a measure exists and is not a simple variable, it has type `int`. -/
  measureTyped : ∀ m, func.measure = some m →
    ∀ (Γ : TContext Unit),
      (∀ x ty, ListMap.find? func.inputs x = some ty →
        Γ.types.find? x = some (.forAll [] ty)) →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      S.exprTyped C Γ m (S.embed .int)

/-- `FuncHasType` instantiated with `HasType`. -/
abbrev FuncHasType (C : LContext CoreLParams) :=
  @FuncHasType' LTy instHasType C

/-- `FuncHasType` instantiated with `HasTypeA`. -/
abbrev FuncHasTypeA (C : LContext CoreLParams) :=
  @FuncHasType' LMonoTy instHasTypeA C

end -- public section

end TypeSpec
end Core
