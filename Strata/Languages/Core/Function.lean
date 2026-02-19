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

/-- Convert a `PureFunc Expression` (with polytypes) to a `Function` (with monotypes). -/
def Function.ofPureFunc (decl : Imperative.PureFunc Expression) : Function := {
  name := decl.name
  typeArgs := decl.typeArgs
  isConstr := decl.isConstr
  inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty))
  output := Lambda.LTy.toMonoTypeUnsafe decl.output
  body := decl.body
  attr := decl.attr
  concreteEval := none
  axioms := decl.axioms
  preconditions := decl.preconditions
}

---------------------------------------------------------------------

end Core
