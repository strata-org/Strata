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

A function is well-typed when:
1. Its signature is well-formed (no duplicate inputs, no duplicate typeArgs,
   no undeclared free type variables).
2. Its body (when present) has the declared return type in some context
   containing the formal parameters at their monomorphic types.
3. Its measure (when present and not a simple variable) has type `int` in some
   context containing the formals.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The typing context for a function body: the ambient context `Γ` (in which the
    function declaration was type-checked) with one additional newest scope binding
    each formal to its declared monomorphic type (wrapped in a trivial polytype).

    The ambient context matters: a statement-level `funcDecl` is checked with the
    enclosing procedure's locals/params in `Γ`, and its body may reference them.
    For top-level program functions `Γ.types = []`, so this reduces to the single
    formals scope `{ types := [formals] }`. -/
def funcContext (Γ : TContext Unit) (func : Function) : TContext Unit :=
  { Γ with types := Γ.types.push (func.inputs.map (fun (id, mty) => (id, .forAll [] mty))) }

/--
Declarative typing for functions, parameterized over `ExprTypingSpec`.
The `Γ` is the ambient context the function was type-checked in.
-/
structure FuncHasType' (τ : Type) [S : ExprTypingSpec τ]
    (C : LContext CoreLParams) (Γ : TContext Unit) (func : Function) : Prop where
  /-- The function's formal parameter names are distinct. -/
  inputsNodup : func.inputs.keys.Nodup
  /-- The function's type argument names are distinct. -/
  typeArgsNodup : func.typeArgs.Nodup
  /-- All free type variables in the signature are declared in `typeArgs`. -/
  noUndeclaredVars : ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) →
    v ∈ func.typeArgs
  /-- If a body exists, it has the declared return type in the ambient context
      extended with a scope binding each formal to its monomorphic type (up to
      consistent renaming of type variables). -/
  bodyTyped : ∀ body, func.body = some body →
    S.exprTyped C (funcContext Γ func) body (S.embed func.output)
  /-- If a measure exists and is not a simple variable, it has type `int`
      in the same context. -/
  measureTyped : ∀ m, func.measure = some m →
    (∀ mid x ann, m ≠ .fvar mid x ann) →
    S.exprTyped C (funcContext Γ func) m (S.embed .int)

/-- `FuncHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev FuncHasType (C : LContext CoreLParams) :=
  @FuncHasType' LTy instHasType C

/-- `FuncHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev FuncHasTypeA (C : LContext CoreLParams) :=
  @FuncHasType' LMonoTy instHasTypeA C

end -- public section

end TypeSpec
end Core
