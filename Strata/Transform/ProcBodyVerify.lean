/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Identifiers
import Strata.Transform.CoreTransform

/-! # Procedure Body Verification Transformation

This transformation converts a procedure into a statement that verifies the
procedure's body against its contract.

The transformation:
1. Initializes all input parameters and output parameters
2. Converts preconditions to `assume` statements
3. Wraps the body in a labeled block
4. Converts postconditions to `assert` statements

Modified globals are already converted to extra in/out parameters on the
procedure header before this transformation runs.

Example:
```
procedure P(x: int, g: int) returns (y: int, g: int)
spec {
  requires x > 0;
  ensures y > 0;
}
{ y := x; }
```

Transforms to:
```
block "verify_P" {
  init x; init g; init y; init g;
  assume "pre_0" (x > 0);
  block "body_P" { y := x; }
  assert "post_0" (y > 0);
}
```
-/

namespace Core.ProcBodyVerify

open Core Imperative Transform

/-- Convert preconditions to assume statements -/
def requiresToAssumes (preconditions : ListMap CoreLabel Procedure.Check) : List Statement :=
  preconditions.toList.map fun (label, check) =>
    Statement.assume label check.expr check.md

/-- Convert postconditions to assert statements -/
def ensuresToAsserts (postconditions : ListMap CoreLabel Procedure.Check) : List Statement :=
  postconditions.toList.filterMap fun (label, check) =>
    match check.attr with
    | .Free => none
    | .Default => some (Statement.assert label check.expr check.md)

/-- Main transformation: convert a procedure to a verification statement -/
def procToVerifyStmt (proc : Procedure) : CoreTransformM Statement := do
  let procName := proc.header.name.name
  let bodyLabel := s!"body_{procName}"
  let verifyLabel := s!"verify_{procName}"

  -- Initialize input parameters
  let inputInits := proc.header.inputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Initialize output parameters
  let outputInits := proc.header.outputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Convert preconditions to assumes
  let assumes := requiresToAssumes proc.spec.preconditions

  -- Wrap body in labeled block
  let bodyBlock := Stmt.block bodyLabel proc.body #[]

  -- Convert postconditions to asserts
  let asserts := ensuresToAsserts proc.spec.postconditions

  -- Combine all parts
  let allStmts := inputInits ++ outputInits ++ assumes ++ [bodyBlock] ++ asserts
  return Stmt.block verifyLabel allStmts #[]

end Core.ProcBodyVerify
