/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Statement

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda

/-! # Strata Core Functions -/

abbrev Function := Lambda.LFunc CoreLParams

-- Type class instances to enable type class resolution for CoreLParams.Identifier
instance : DecidableEq CoreLParams.IDMeta :=
  show DecidableEq Visibility from inferInstance

instance : ToFormat CoreLParams.IDMeta :=
  show ToFormat Visibility from inferInstance

/-- Convert a `PureFunc Expression` (with polytypes) to a `Function` (with monotypes).
    Returns an error if any type is not a monotype. -/
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
    concreteEval := none
    axioms := decl.axioms
    preconditions := decl.preconditions
  }

---------------------------------------------------------------------

end Core
