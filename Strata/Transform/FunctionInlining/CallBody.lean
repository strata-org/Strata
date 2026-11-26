/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.Factory
import Strata.DL.Lambda.LExprType

/-! # The body of a function call

`inlineCallBody` gives the body of a called function with its parameters replaced by
the call's arguments. Function inlining and simplification both use it. The module
imports no pipeline phase.
-/

namespace Strata

public section

/-- The body of `lfunc`, called as `op_expr` applied to `args`, with its type
    parameters instantiated and `args` substituted for its parameters. `none`
    when `lfunc` has no body, or when the type substitution does not exist
    (which a well-typed call does not produce). -/
@[expose] def inlineCallBody
    (lfunc : Lambda.LFunc Core.CoreLParams)
    (op_expr : Lambda.LExpr Core.CoreLParams.mono)
    (args : List (Lambda.LExpr Core.CoreLParams.mono))
    : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  match lfunc.body with
  | none => none
  | some body => lfunc.instantiateBody? body op_expr args

end -- public section

end Strata
