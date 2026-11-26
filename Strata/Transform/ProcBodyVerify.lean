/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Transform.CoreTransform

public section

/-! # Procedure Body Verification Transformation

This transformation converts a procedure into a statement that verifies the
procedure's body against its contract.

The transformation:
1. Initializes all input parameters and output parameters
2. For each in-out parameter `x` (appearing in both inputs and outputs),
   creates `old x := x` to snapshot the pre-state (`CoreIdent.mkOld`; the
   translator turns `old(x)` into the variable `old x`)
3. Converts preconditions to `assume` statements
4. Wraps the body in a labeled block
5. Converts postconditions to `assert` statements; a free postcondition becomes
   `assume true` (`Imperative.Check.asserts`)

Example:
```
procedure P(inout x: int, out y: int)
spec {
  requires x > 0;
  ensures y > 0;
  ensures x == old(x) + 1;
}
{ y := x; x := x + 1; }
```

Transforms to:
```
block "verify_P" {
  init x; init y;
  init (old x) := x;
  assume "pre_0" (x > 0);
  block "body_P" { y := x; x := x + 1; }
  assert "post_0" (y > 0);
  assert "post_1" (x == old x + 1);
}
```
-/

namespace Core.ProcBodyVerify

open Core Imperative Transform

/-- An unconstrained declaration of each input parameter (in-out ones included)
    and each output-only parameter. -/
@[expose] def paramInits (header : Procedure.Header) : List Statement :=
  (header.inputs.toList ++ header.getOutputOnlyParams.toList).map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]

/-- `init (old x) := x` for each in-out parameter `x`: the snapshot of its
    value on entry. -/
@[expose] def oldInits (header : Procedure.Header) : List Statement :=
  header.getInoutParams.toList.map fun (id, ty) =>
    Statement.init (CoreIdent.mkOld id.name) (Lambda.LTy.forAll [] ty)
      (.det (Lambda.LExpr.fvar (ExprSourceLoc.synthesized "transform") id none)) #[]

/-- Main transformation: convert a procedure to a verification statement -/
@[expose] def procToVerifyStmt (proc : Procedure) : CoreTransformM Statement := do
  let procName := proc.header.name.name
  let bodyLabel := s!"body_{procName}"
  let verifyLabel := s!"verify_{procName}"

  -- Convert preconditions to assumes
  let assumes := (Check.assumes proc.spec.preconditions).map (Stmt.cmd (P := Expression))

  -- ProcBodyVerify expects a structured body: the prefix (inits + assumes) and
  -- suffix (postcondition asserts) are statement-level constructs that embed
  -- around the body. Unstructured CFG bodies are not supported here.
  let bodyStmts ← proc.body.getStructured.mapError Strata.Message.fromString
  -- Wrap body in labeled block
  let bodyBlock := Stmt.block bodyLabel bodyStmts #[]

  -- Convert postconditions to asserts
  let asserts := (Check.asserts proc.spec.postconditions).map (Stmt.cmd (P := Expression))

  -- Combine all parts
  let allStmts := paramInits proc.header ++ oldInits proc.header ++
      assumes ++ [bodyBlock] ++ asserts
  return Stmt.block verifyLabel allStmts #[]

end Core.ProcBodyVerify
