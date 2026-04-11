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
1. Initializes old snapshots for modifies-converted variables
2. Initializes output parameters and non-modifies input parameters
3. Converts preconditions to `assume` statements
4. Prepends `g := old g` assignments for each modifies variable to the body
5. Wraps the body in a labeled block
6. Converts postconditions to `assert` statements

Modified globals are already converted to extra in/out parameters on the
procedure header before this transformation runs. A variable is recognized
as modifies-converted when it appears in both inputs and outputs.

Example:
```
procedure P(g: int, x: int) returns (g: int, y: int)
spec {
  requires x > 0;
  ensures y > 0;
  ensures g == old g + 1;
}
{ y := x; g := g + 1; }
```

Transforms to:
```
block "verify_P" {
  init old g; init g; init x; init y;
  assume "pre_0" (x > 0);
  block "body_P" { g := old g; y := x; g := g + 1; }
  assert "post_0" (y > 0);
  assert "post_1" (g == old g + 1);
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

/-- Compute the identifiers of modifies-converted variables (those in both inputs and outputs). -/
def modifiesKeys (proc : Procedure) : List Expression.Ident :=
  proc.header.inputs.keys.filter (· ∈ proc.header.outputs.keys)

/-- Compute the full body including modifies assignments prepended. -/
def fullBody (proc : Procedure) : List Statement :=
  let assigns := (modifiesKeys proc).reverse.map fun id =>
    Statement.set id (Lambda.LExpr.fvar () (CoreIdent.mkOld id.name) none) #[]
  assigns.reverse ++ proc.body

/-- Main transformation: convert a procedure to a verification statement -/
def procToVerifyStmt (proc : Procedure) : CoreTransformM Statement := do
  let procName := proc.header.name.name
  let bodyLabel := s!"body_{procName}"
  let verifyLabel := s!"verify_{procName}"

  let mKeys := modifiesKeys proc

  -- Initialize old snapshots for modifies variables
  let oldInits := proc.header.inputs.toList.reverse.filterMap fun (id, ty) =>
    if id ∈ mKeys then
      some (Statement.init (CoreIdent.mkOld id.name) (Lambda.LTy.forAll [] ty) .nondet #[])
    else none
  let oldInits := oldInits.reverse

  -- Initialize non-modifies input parameters
  let inputInits := proc.header.inputs.toList.filterMap fun (id, ty) =>
    if id ∈ mKeys then none
    else some (Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[])

  -- Initialize output parameters (includes modifies variables)
  let outputInits := proc.header.outputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Convert preconditions to assumes
  let assumes := requiresToAssumes proc.spec.preconditions

  -- Wrap body with modifies assignments prepended, in labeled block
  let bodyBlock := Stmt.block bodyLabel (fullBody proc) #[]

  -- Convert postconditions to asserts
  let asserts := ensuresToAsserts proc.spec.postconditions

  -- Combine all parts
  let allStmts := oldInits ++ outputInits ++ inputInits ++ assumes ++ [bodyBlock] ++ asserts
  return Stmt.block verifyLabel allStmts #[]

end Core.ProcBodyVerify
