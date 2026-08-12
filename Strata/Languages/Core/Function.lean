/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import Strata.Languages.Core.Expressions

---------------------------------------------------------------------

namespace Core
public section

open Std (ToFormat Format format)
open Lambda

/-! # Strata Core Functions -/

@[expose]
abbrev Function := Lambda.LFuncDefined CoreLParams

instance : Inhabited Function where
  default := { name := default, inputs := [], output := default }

-- Type class instances to enable type class resolution for CoreLParams.Identifier
instance : DecidableEq CoreLParams.IDMeta :=
  show DecidableEq Unit from inferInstance

instance : ToFormat CoreLParams.IDMeta :=
  show ToFormat Unit from inferInstance

/--
Build a constant: a nullary function named `name` of type `ty`.

`value`, when given, is the constant's right-hand side. As for a function
definition, the value is substituted at each use only when `attr` contains
`.inline`; without it the value still reaches the solver through the encoded
body.

A constant is monomorphic. A polymorphic nullary value is a function: build it
as one, so the quantification is visible.
-/
@[expose]
def Function.const (name : CoreIdent) (ty : LMonoTy)
    (value : Option Expression.Expr := none)
    (attr : Array Strata.DL.Util.FuncAttr := #[]) : Function :=
  { name, inputs := [], output := ty, body := value, attr }

/-- Convert a `PureFunc Expression` (with polytypes) to a `Function` (with monotypes).
    Returns an error if any type is not a monotype. -/
@[expose]
def Function.ofPureFunc (decl : Imperative.PureFunc Expression) : Except Format Function := do
  let inputs ← decl.inputs.mapM fun (id, ty) =>
    match Lambda.LTy.toMonoType? ty with
    | some mty => .ok (id, mty)
    | none => .error f!"Function.ofPureFunc: non-monotype input '{id.name}': {repr ty}"
  let output ← match Lambda.LTy.toMonoType? decl.output with
    | some mty => .ok mty
    | none => .error f!"Function.ofPureFunc: non-monotype output: {repr decl.output}"
  .ok {
    name := decl.name
    typeArgs := decl.typeArgs
    isConstr := decl.isConstr
    inputs := inputs
    output := output
    body := decl.body
    attr := decl.attr
    axioms := decl.axioms
    preconditions := decl.preconditions
    measure := decl.measure
  }

---------------------------------------------------------------------

end
end Core
