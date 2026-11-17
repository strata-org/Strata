/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.Languages.Core.Function
public import Strata.Languages.Core.Typing.Spec.TypeSpecShared

/-! ## The Typechecker Spec for Functions

Specifies when a `Function` (i.e., `LFunc CoreLParams`) satisfies the
typechecker spec.

`FuncHasType'` holds when:
1. Its signature is well-formed (no duplicate inputs, no duplicate typeArgs,
   no undeclared or unused type parameters, no type parameter with a reserved
   prefix).
2. Its body (when present) has the declared return type in the function context
   `funcContext`.
   Its preconditions and axioms are `bool` expressions in that context.
3. Its measure (when present) belongs to a recursive function and has type `int`, or is a
   formal whose type is a registered datatype and has that type, in `funcContext`.
4. Its written annotations are valid in the function context, and their free-variable and
   binder type variables are type parameters.
5. It has no body if it is a constructor.

`FuncHasType` asks this of some renaming of the reserved type parameters
(`FuncAlphaVariant`).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The typing context for a function body: the ambient context `Γ` with one new
    scope binding each formal to its declared monotype.

    For top-level functions the ambient type scope `Γ.types` is empty, leaving
    just the formals scope. -/
def funcContext (Γ : TContext Unit) (func : Function) : TContext Unit :=
  { Γ with types := funcScopes Γ.types func }

/--
The typechecker spec for functions.
The `Γ` is the ambient context the function was type-checked in.
-/
structure FuncHasType' (C : LContext CoreLParams) (Γ : TContext Unit) (func : Function) :
    Prop where
  /-- The function's formal parameter names are distinct. -/
  inputsNodup : func.inputs.keys.Nodup
  /-- The function's type argument names are distinct. -/
  typeArgsNodup : func.typeArgs.Nodup
  /-- No type parameter starts with a reserved prefix. -/
  typeArgsNotReserved : ∀ ta ∈ func.typeArgs, isAllowedName ta = true
  /-- All free type variables in the signature are declared in `typeArgs`. -/
  noUndeclaredVars : ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) →
    v ∈ func.typeArgs
  /-- Every type parameter occurs in an input or output type. -/
  typeArgsInSignature : ∀ ta ∈ func.typeArgs,
    ta ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values)
  /-- Each input and output type is a valid written type. -/
  signatureWellKinded : ∀ ty ∈ func.output :: func.inputs.values,
    ValidWrittenTy C Γ.aliases ty
  /-- If a body exists, it has the declared return type in the ambient context
      extended with a scope binding each formal to its monomorphic type (up to
      consistent renaming of type variables). -/
  bodyTyped : ∀ body, func.body = some body →
    HasType C (funcContext Γ func) body (.forAll [] func.output)
  /-- Only a recursive function has a measure. -/
  measureOnlyRecursive : func.isRecursive = false → func.measure = none
  /-- A bare-variable measure is a formal and has type `int` or the registered datatype its
      declared type is compatible with. Every other measure has type `int`. -/
  measureTyped : ∀ m, func.measure = some m →
    match m with
    | .fvar _ x _ => ∃ ty, func.inputs.find? x = some ty ∧
        (HasType C (funcContext Γ func) m (.forAll [] .int) ∨
          ∃ n args, AliasEquiv Γ.aliases ty (.tcons n args) ∧ (C.datatypes.getType n).isSome ∧
            HasType C (funcContext Γ func) m (.forAll [] (.tcons n args)))
    | _ => HasType C (funcContext Γ func) m (.forAll [] .int)
  /-- Each precondition is a `bool` expression in the function context. -/
  preconditionsTyped : ∀ p ∈ func.preconditions,
    HasType C (funcContext Γ func) p.expr (.forAll [] .bool)
  /-- Each axiom is a `bool` expression in the function context. -/
  axiomsTyped : ∀ ax ∈ func.axioms,
    HasType C (funcContext Γ func) ax (.forAll [] .bool)
  /-- Every free-variable and binder annotation type variable of every expression is a type
      parameter. -/
  annotsScoped : ∀ e ∈ func.exprs, AnnotsInScope func.typeArgs (fun _ => none) e
  /-- Every expression's written annotations are valid in the function context. -/
  writtenAnnotsOk : ∀ e ∈ func.exprs, WrittenAnnotsOk C (funcContext Γ func) e
  /-- No formal parameter is named like an in-scope function. -/
  formalsNotFunctions : ∀ id ∈ func.inputs.keys, id.name ∉ C.functions
  /-- A constructor has no body. -/
  constrNoBody : func.isConstr = true → func.body = none

/-- `f'` is `func` with some of its reserved type parameters renamed throughout, injectively and
    to names that neither `func` nor the context `C`, `Γ` uses (`TyArgRenaming`). -/
def FuncAlphaVariant (C : LContext CoreLParams) (Γ : TContext Unit) (func f' : Function) :
    Prop :=
  ∃ ren : List (String × String),
    TyArgRenaming C Γ func.typeArgs func.mentionedTyVars ren ∧ f' = func.renameTypeArgs ren

/-- The typechecker spec for functions: some renaming of the type parameters of `func`
    (`FuncAlphaVariant`) satisfies `FuncHasType'`. -/
def FuncHasType (C : LContext CoreLParams) (Γ : TContext Unit) (func : Function) : Prop :=
  ∃ f', FuncAlphaVariant C Γ func f' ∧ FuncHasType' C Γ f'

end -- public section

end TypeSpec
end Core
