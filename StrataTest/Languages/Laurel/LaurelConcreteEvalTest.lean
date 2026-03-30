/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Tests for Laurel Concrete Program Evaluator

Tests that `evalProgram` and `interpProgram` correctly wire up `interpStmt`
for whole `Laurel.Program` values.

Tests 1–8 use the Laurel parser to build programs from source strings.
Tests 9–13 use programmatic AST construction for internal API features
that cannot be expressed in Laurel concrete syntax.
-/

namespace Strata.Laurel.ConcreteEvalTest

open Strata
open Strata.Laurel
open Strata.Laurel.ConcreteEval.TestHelper

/-! ## Test 1: Minimal program — main returns literal int -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 42 };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 2: Local variables and arithmetic -/

/--
info: returned: 7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 3;
  var y: int := 4;
  return x + y
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 3: Static procedure call -/

/--
info: returned: 30
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure add(a: int, b: int) { return a + b };
procedure main() { return add(10, 20) };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 4: While loop — sum 1..10 -/

/--
info: returned: 55
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var sum: int := 0;
  var i: int := 1;
  while (i <= 10) {
    sum := sum + i;
    i := i + 1
  };
  return sum
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5: If-then-else (abs function) -/

/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure abs(x: int) {
  if (x < 0) { return 0 - x } else { return x }
};
procedure main() { return abs(-5) };
"
  IO.println (toString (interpProgram prog))


/-! ## Test 5b: Lazy And -/

/--
info: returned: -1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure lazyAnd(x: int) {
  var sum : int := 0;
  if (x < 0 && {sum := 1; sum == 1}) { sum := 42} else { sum := sum - 1};
  return sum
};
procedure main() { return lazyAnd(5) };
"
  IO.println (toString (interpProgram prog))


/--
info: returned: -1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure lazyAnd(x: int) {
  var sum : int := 0;
  if (x < 0 && {sum := 1; sum == 1}) { sum := 42} else { sum := sum - 1};
  return sum
};
procedure main() { return lazyAnd(5) };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5c: Lazy Or -/

/--
info: returned: -1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure lazyOr(x: int) {
  var sum : int := 0;
  if (x > 0 || {sum := 1; sum == 1}) { sum := sum - 1} else { sum := 42};
  return sum
};
procedure main() { return lazyOr(5) };
"
  IO.println (toString (interpProgram prog))


/-! ## Test 6: Recursive procedure (factorial) -/

/--
info: returned: 120
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure fact(n: int) {
  if (n <= 1) { return 1 } else { return n * fact(n - 1) }
};
procedure main() { return fact(5) };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 7: No main procedure -/

/--
info: error: no 'main' procedure found
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure notMain() { return 1 };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 8: OO features — composite type with field access -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point {
  var x: int
  var y: int
}
procedure main() {
  var p: Point := new Point;
  p#x := 1;
  p#y := 2;
  return p#x + p#y
};
"
  IO.println (toString (interpProgram prog))

/-! ## Programmatic AST Tests

The following tests exercise internal API features (outcome classification,
opaque procedures, instance methods, static fields) that cannot be expressed
in Laurel concrete syntax. They use programmatic AST construction.
-/

/-! ## Test 9: interpProgram success classification -/

#guard
  let prog := mkProgram [mkProc "main" [] (.LiteralInt 42)]
  match interpProgram prog with
  | .success (.vInt 42) _ _ => true
  | _ => false

/-! ## Test 10: interpProgram returned classification -/

#guard
  let prog := mkProgram [mkProc "main" [] (.Return (some (mk (.LiteralInt 99))))]
  match interpProgram prog with
  | .returned (some (.vInt 99)) _ _ => true
  | _ => false

/-! ## Test 11: No body (opaque procedure) -/

#guard
  let mainProc : Procedure := {
    name := "main"
    inputs := []
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Opaque [] none []
    md := emd
  }
  let prog := mkProgram [mainProc]
  match interpProgram prog with
  | .noBody => true
  | _ => false

/-! ## Test 12: Instance method call via buildProcEnv -/

#guard
  let getXBody := StmtExpr.Return (some (mk (.FieldSelect (mk (.This)) "x")))
  let getXProc : Procedure := {
    name := "getX"
    inputs := [⟨"this", ⟨.UserDefined "Point", emd⟩⟩]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk getXBody)
    md := emd
  }
  let pointType : TypeDefinition := .Composite {
    name := "Point"
    extending := []
    fields := [{ name := "x", isMutable := true, type := ⟨.TInt, emd⟩ }]
    instanceProcedures := [getXProc]
  }
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "p")) "x", emd⟩] (mk (.LiteralInt 7))),
    mk (.Return (some (mk (.InstanceCall (mk (.Identifier "p")) "getX" []))))
  ] none
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := []
    types := [pointType]
    constants := []
  }
  getOutcome (interpProgram prog) = some (.vInt 7)

/-! ## Test 13: Static fields initialized to vVoid -/

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
  getOutcome (interpProgram prog) = some (.vInt 10)

end Strata.Laurel.ConcreteEvalTest
