/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Lambda.LExprEval

/-! # The fixpoint evaluator `evalFully`

`evalFully` runs the fuel-bounded evaluator `LExpr.eval` at fuel `0, 1, 2, …` and returns the
first fully reduced result (`.value true`); it is `none` when no fuel yields one. Its
properties, and the properties of `LExpr.eval` they rest on, are in `LExprEvalFuelProps`.
-/

namespace Lambda
open Std (ToFormat Format format)

public section

namespace LExpr

variable {TBase : LExprParams} [DecidableEq TBase.IDMeta] [Inhabited TBase.IDMeta]
  [Traceable EvalProvenance TBase.Metadata]

/-- Run `eval` at `fuel`, `fuel + 1`, … and return the first fully reduced result
    (`.value true`); `none` when no fuel from `fuel` on yields one (`partial_fixpoint`).

    `@[expose]` works around a panic of `partial_fixpoint` on non-exposed bodies in the
    current Lean release. -/
@[expose] def evalFullyAux (F : @Factory TBase) (env : Env TBase) (e : LExpr TBase.mono)
    (fuel : Nat) : Option (LExpr TBase.mono) :=
  let (e', res) := eval fuel F env e
  match res with
  | .value true => some e'
  | .value false => evalFullyAux F env e (fuel + 1)
  | .nonvalue => evalFullyAux F env e (fuel + 1)
  | .outOfFuel => evalFullyAux F env e (fuel + 1)
partial_fixpoint

/-- Fully evaluate an expression: `evalFullyAux` from fuel `0`. -/
def evalFully (F : @Factory TBase) (env : Env TBase) (e : LExpr TBase.mono)
    : Option (LExpr TBase.mono) :=
  evalFullyAux F env e 0

end LExpr
end -- public section
end Lambda
