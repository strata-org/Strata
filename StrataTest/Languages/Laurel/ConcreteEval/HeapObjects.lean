/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Heap Object Semantics Tests

Tests for object allocation, field read/write, multiple fields, multiple
objects, instance method calls, static fields, and field access on
unallocated addresses.
-/

namespace Strata.Laurel.ConcreteEval.HeapObjectsTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: New object allocation -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int }
procedure main() { var p: Point := new Point; return 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 2: Field write and read -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int }
procedure main() { var p: Point := new Point; p#x := 42; return p#x };
"
  IO.println (toString (runProgram prog))

/-! ## Test 3: Multiple fields -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int  var y: int }
procedure main() {
  var p: Point := new Point; p#x := 1; p#y := 2;
  return p#x + p#y
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Multiple objects on heap — no cross-contamination -/

/--
info: returned: 30
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Box { var v: int }
procedure main() {
  var a: Box := new Box; a#v := 10;
  var b: Box := new Box; b#v := 20;
  return a#v + b#v
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 5: Instance method call — programmatic AST

Parser does not support instance call syntax, so we build the AST directly.
Composite `Counter` with field `n` and method `get(this: Counter) { return this#n }`.
-/

#guard
  let getBody := StmtExpr.Return (some (mk (.FieldSelect (mk (.This)) "n")))
  let getProc : Procedure := {
    name := "get"
    inputs := [⟨"this", ⟨.UserDefined "Counter", emd⟩⟩]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk getBody)
    md := emd
  }
  let counterType : TypeDefinition := .Composite {
    name := "Counter"
    extending := []
    fields := [{ name := "n", isMutable := true, type := ⟨.TInt, emd⟩ }]
    instanceProcedures := [getProc]
  }
  let body := StmtExpr.Block [
    mk (.LocalVariable "c" ⟨.UserDefined "Counter", emd⟩ (some (mk (.New "Counter")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "c")) "n", emd⟩] (mk (.LiteralInt 7))),
    mk (.Return (some (mk (.InstanceCall (mk (.Identifier "c")) "get" []))))
  ] none
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := []
    types := [counterType]
    constants := []
  }
  getOutcome (evalProgram prog) = some (.ret (some (.vInt 7)))

/-! ## Test 6: Instance method modifying fields — programmatic AST

`Counter` with method `inc(this: Counter) { this#n := this#n + 1 }`.
Call `inc` twice, expect `n` = 2.
-/

#guard
  let incBody := StmtExpr.Block [
    mk (.Assign [⟨.FieldSelect (mk (.This)) "n", emd⟩]
      (mk (.PrimitiveOp .Add [⟨.FieldSelect (mk (.This)) "n", emd⟩, ⟨.LiteralInt 1, emd⟩])))
  ] none
  let incProc : Procedure := {
    name := "inc"
    inputs := [⟨"this", ⟨.UserDefined "Counter", emd⟩⟩]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk incBody)
    md := emd
  }
  let counterType : TypeDefinition := .Composite {
    name := "Counter"
    extending := []
    fields := [{ name := "n", isMutable := true, type := ⟨.TInt, emd⟩ }]
    instanceProcedures := [incProc]
  }
  let body := StmtExpr.Block [
    mk (.LocalVariable "c" ⟨.UserDefined "Counter", emd⟩ (some (mk (.New "Counter")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "c")) "n", emd⟩] (mk (.LiteralInt 0))),
    mk (.InstanceCall (mk (.Identifier "c")) "inc" []),
    mk (.InstanceCall (mk (.Identifier "c")) "inc" []),
    mk (.Return (some (mk (.FieldSelect (mk (.Identifier "c")) "n"))))
  ] none
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := []
    types := [counterType]
    constants := []
  }
  getOutcome (evalProgram prog) = some (.ret (some (.vInt 2)))

/-! ## Test 7: Static fields (global variables) — programmatic AST -/

#guard
  let body := StmtExpr.Block [
    mk (.Assign [⟨.Identifier "counter", emd⟩] (mk (.LiteralInt 10))),
    mk (.Return (some (mk (.Identifier "counter"))))
  ] none
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := [{ name := "counter", isMutable := true, type := ⟨.TInt, emd⟩ }]
    types := []
    constants := []
  }
  getOutcome (evalProgram prog) = some (.ret (some (.vInt 10)))

/-! ## Test 8: Field access on unallocated address → stuck — programmatic AST

Use `interpStmt` directly with a store where `"x"` maps to `.vRef 999` and an
empty heap.  `FieldSelect (Identifier "x") "f"` evaluates the target to
`.vRef 999`, then `heapFieldRead` returns `none` because address 999 was never
allocated.
-/

#guard
  let σ : LaurelStore := fun x => if x == "x" then some (.vRef 999) else none
  let h : LaurelHeap := fun _ => none
  let expr := StmtExpr.FieldSelect (mk (.Identifier "x")) "f"
  (interpStmt defaultEval (fun _ => none) 100 h σ expr).isNone

end Strata.Laurel.ConcreteEval.HeapObjectsTest
