/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform

public section

/-! # Procedure Body Verification Transformation

This transformation converts a procedure into a statement that verifies the
procedure's body against its contract.

The transformation:
1. Initializes all input parameters and output parameters
2. For each in-out parameter `x` (appearing in both inputs and outputs),
   creates `old_x := x` to snapshot the pre-state
3. Converts preconditions to `assume` statements
4. Wraps the body in a labeled block
5. Converts postconditions to `assert` statements

Example:
```
procedure P(inout x: int, out y: int)
spec {
  requires x > 0;
  ensures y > 0;
  ensures x == old_x + 1;
}
{ y := x; x := x + 1; }
```

Transforms to:
```
block "verify_P" {
  init x; init y;
  init old_x := x;
  assume "pre_0" (x > 0);
  block "body_P" { y := x; x := x + 1; }
  assert "post_0" (y > 0);
  assert "post_1" (x == old_x + 1);
}
```
-/

namespace Core.ProcBodyVerify

open Core Imperative Transform

/-- Convert preconditions to assume statements -/
@[expose] def requiresToAssumes (preconditions : ListMap CoreLabel Procedure.Check) : List Statement :=
  preconditions.toList.map fun (label, check) =>
    Statement.assume label check.expr check.md

/-- Convert postconditions to assert statements -/
@[expose] def ensuresToAsserts (postconditions : ListMap CoreLabel Procedure.Check) : List Statement :=
  postconditions.toList.filterMap fun (label, check) =>
    match check.attr with
    | .Free => none
    | .Default => some (Statement.assert label check.expr check.md)

/-- Main transformation: convert a procedure to a verification statement -/
@[expose] def procToVerifyStmt (proc : Procedure) : CoreTransformM Statement := do
  let procName := proc.header.name.name
  let bodyLabel := s!"body_{procName}"
  let verifyLabel := s!"verify_{procName}"

  -- Initialize input parameters (includes in-out params)
  let inputInits := proc.header.inputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Initialize output-only parameters (outputs not in inputs)
  let outputOnlyInits := proc.header.getOutputOnlyParams.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Initialize old variables of in-out parameters (those in both inputs and outputs).
  let oldInoutInits ← proc.header.getInoutParams.mapM fun (id,ty) => do
    let oldG := CoreIdent.mkOld id.name
    let e : Core.Expression.Expr := .fvar () id none
    return (Statement.init oldG (Lambda.LTy.forAll [] ty) (.det e) #[])

  -- Convert preconditions to assumes
  let assumes := requiresToAssumes proc.spec.preconditions

  -- Wrap body in labeled block
  let bodyBlock := Stmt.block bodyLabel proc.body #[]

  -- Convert postconditions to asserts
  let asserts := ensuresToAsserts proc.spec.postconditions

  -- Combine all parts
  let allStmts := inputInits ++ outputOnlyInits ++ oldInoutInits ++
      assumes ++ [bodyBlock] ++ asserts
  return Stmt.block verifyLabel allStmts #[]

end Core.ProcBodyVerify
