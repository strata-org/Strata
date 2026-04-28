/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Languages.Core.Program
import Strata.DDM.Integration.Lean
import Strata.Languages.Core.DDMTransform.Translate

/-! # Procedure Body Verification Tests

Unit tests for the ProcBodyVerify transformation.
Tests verify the transformation produces correct output structure.
-/

namespace ProcBodyVerifyTest

open Core Core.ProcBodyVerify Lambda Transform Imperative
open Strata

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- Helper to show transformed output for a procedure -/
def showTransformed (prog : Strata.Program) (procName : String) : Except String Std.Format := do
  let p := translate prog
  let some proc := Program.Procedure.find? p procName
    | throw s!"Procedure {procName} not found"
  let state := { CoreTransformState.emp with currentProgram := .some p }
  let (.ok stmt, _) := (procToVerifyStmt proc).run state
    | throw "Transformation failed"
  return Core.formatStatement stmt

/-! ## Test 1: Procedure with modifies clause -/

-- Show the transformed output
/--
info: ok: verify_Test: {
  var g : int;
  var x : int;
  var y : int;
  var |old g| : int := g;
  assume [Test_requires_0]: x > 0;
  body_Test: {
    y := x;
    g := g + 1;
  }
  assert [Test_ensures_1]: y > 0;
  assert [Test_ensures_2]: g == old g + 1;
}
-/
#guard_msgs in
#eval! showTransformed
  (#strata
  program Core;
  procedure Test(inout g : int, x : int, out y : int)
  spec {
    requires (x > 0);
    ensures (y > 0);
    ensures (g == old g + 1);
  }
  {
    y := x;
    g := g + 1;
  };
  #end)
  "Test"

/-! ## Test 2: Simple procedure without modifies -/

-- Show the transformed output
/--
info: ok: verify_Simple: {
  var x : bool;
  var y : bool;
  assume [Simple_requires_0]: x;
  body_Simple: {
    y := x;
  }
  assert [Simple_ensures_1]: y;
}
-/
#guard_msgs in
#eval! showTransformed
  (#strata
  program Core;
  procedure Simple(x : bool, out y : bool)
  spec {
    requires x;
    ensures y;
  }
  {
    y := x;
  };
  #end)
  "Simple"

/-! ## Test 3: Free specifications (should be filtered out) -/

-- Show the transformed output
/--
info: ok: verify_WithFree: {
  var x : int;
  var y : int;
  assume [WithFree_requires_0]: x >= 0;
  assume [WithFree_requires_1]: x > 0;
  body_WithFree: {
    y := x;
  }
  assert [WithFree_ensures_3]: y == x;
}
-/
#guard_msgs in
#eval! showTransformed
  (#strata
  program Core;
  procedure WithFree(x : int, out y : int)
  spec {
    free requires (x >= 0);
    requires (x > 0);
    free ensures (y >= 0);
    ensures (y == x);
  }
  {
    y := x;
  };
  #end)
  "WithFree"

/-! ## Test 4: Multiple modified globals -/

-- Show the transformed output
/--
info: ok: verify_MultipleModifies: {
  var g1 : int;
  var g2 : bool;
  var x : int;
  var y : int;
  var |old g1| : int := g1;
  var |old g2| : bool := g2;
  assume [MultipleModifies_requires_0]: x > 0;
  body_MultipleModifies: {
    y := x;
    g1 := g1 + 1;
    g2 := true;
  }
  assert [MultipleModifies_ensures_1]: y == x;
  assert [MultipleModifies_ensures_2]: g1 == old g1 + 1;
  assert [MultipleModifies_ensures_3]: g2;
}
-/
#guard_msgs in
#eval! showTransformed
  (#strata
  program Core;
  procedure MultipleModifies(inout g1 : int, inout g2 : bool, x : int, out y : int)
  spec {
    requires (x > 0);
    ensures (y == x);
    ensures (g1 == old g1 + 1);
    ensures g2;
  }
  {
    y := x;
    g1 := g1 + 1;
    g2 := true;
  };
  #end)
  "MultipleModifies"

end ProcBodyVerifyTest
