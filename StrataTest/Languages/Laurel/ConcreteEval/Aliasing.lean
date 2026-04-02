/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Aliasing Semantics Tests

Tests for reference aliasing: shared mutation, distinct objects,
aliasing through procedure calls, and programmatic ReferenceEquals.
-/

namespace Strata.Laurel.ConcreteEval.AliasingTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Simple aliasing — two vars, same object -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int }
procedure main() {
  var p: Point := new Point; p#x := 1;
  var q: Point := p;
  q#x := 42;
  return p#x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 2: Aliasing through procedure call — pass same object twice -/

/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Box { var v: int }
procedure swap(a: Box, b: Box) {
  var tmp: int := a#v; a#v := b#v; b#v := tmp
};
procedure main() {
  var b: Box := new Box; b#v := 5;
  swap(b, b);
  return b#v
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 3: Distinct objects are independent -/

/--
info: returned: 2
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int }
procedure main() {
  var p: Point := new Point; p#x := 1;
  var q: Point := new Point; q#x := 2;
  p#x := 99;
  return q#x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 4: Alias survives procedure call -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Box { var v: int }
procedure setV(b: Box, x: int) { b#v := x };
procedure main() {
  var a: Box := new Box; a#v := 0;
  var b: Box := a;
  setV(a, 42);
  return b#v
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5: ReferenceEquals — programmatic AST test -/

-- 5a: Same ref → true
#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.LocalVariable "q" ⟨.UserDefined "Point", emd⟩ (some (mk (.Identifier "p")))),
    mk (.Return (some (mk (.ReferenceEquals (mk (.Identifier "p")) (mk (.Identifier "q"))))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point"
    extending := []
    fields := [{ name := "x", isMutable := true, type := ⟨.TInt, emd⟩ }]
    instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := []
    types := [pointType]
    constants := []
  }
  getOutcome (interpProgram prog) = some (.vBool true)

-- 5b: Different refs → false
#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.LocalVariable "r" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Return (some (mk (.ReferenceEquals (mk (.Identifier "p")) (mk (.Identifier "r"))))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point"
    extending := []
    fields := [{ name := "x", isMutable := true, type := ⟨.TInt, emd⟩ }]
    instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := []
    types := [pointType]
    constants := []
  }
  getOutcome (interpProgram prog) = some (.vBool false)

end Strata.Laurel.ConcreteEval.AliasingTest
