/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Identifiers
public import Strata.Transform.CoreTransform

public section

/-! # Procedure Body Verification Transformation

This transformation converts a procedure into a statement that verifies the
procedure's body against its contract.

The transformation:
1. Initializes all input parameters, output parameters, and modified globals
2. For each modified global `g`, creates `old_g` (pre-state) and `g` (post-state)
3. Converts preconditions to `assume` statements
4. Wraps the body in a labeled block
5. Converts postconditions to `assert` statements

Example:
```
procedure P(x: int) returns (y: int)
spec {
  modifies g;
  requires x > 0;
  ensures y > 0;
  ensures g == old_g + 1;
}
{ y := x; g := g + 1; }
```

Transforms to:
```
block "verify_P" {
  init x; init y;
  init old_g; init g := old_g;
  assume "pre_0" (x > 0);
  block "body_P" { y := x; g := g + 1; }
  assert "post_0" (y > 0);
  assert "post_1" (g == old_g + 1);
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
@[expose] def procToVerifyStmt (proc : Procedure) (p : Program) : CoreTransformM Statement := do
  let procName := proc.header.name.name
  let bodyLabel := s!"body_{procName}"
  let verifyLabel := s!"verify_{procName}"

  -- Initialize input parameters
  let inputInits := proc.header.inputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Initialize output parameters
  let outputInits := proc.header.outputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

  -- Initialize modified globals: old_g (no RHS), then g := old_g
  let modifiesInits ← proc.spec.modifies.mapM fun g => do
    let oldG := CoreIdent.mkOld g.name
    let gTy ← getIdentTy! p g
    return [ Statement.init oldG gTy .nondet #[],
             Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[] ]
  let modifiesInits := modifiesInits.flatten

  -- Convert preconditions to assumes
  let assumes := requiresToAssumes proc.spec.preconditions

  -- Wrap body in labeled block
  let bodyBlock := Stmt.block bodyLabel proc.body #[]

  -- Convert postconditions to asserts
  let asserts := ensuresToAsserts proc.spec.postconditions

  -- Combine all parts
  let allStmts := inputInits ++ outputInits ++ modifiesInits ++ assumes ++ [bodyBlock] ++ asserts
  return Stmt.block verifyLabel allStmts #[]

end Core.ProcBodyVerify
