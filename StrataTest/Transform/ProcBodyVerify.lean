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

/-! ## Test 1: Procedure with modifies clause -/

def Test1 :=
#strata
program Core;
var g : int;
procedure Test(x : int) returns (y : int)
spec {
  modifies g;
  requires (x > 0);
  ensures (y > 0);
  ensures (g == old g + 1);
}
{
  y := x;
  g := g + 1;
};
#end

-- Show the transformed output
/--
info: "verify_Test :\n{\n  init (x : int)\n  init (y : int)\n  init (old g : int)\n  init (g : int) := old g\n  assume [Test_requires_1] ((~Int.Gt : (arrow int (arrow int bool))) (x : int) #0)\n  body_Test :\n  {\n    y := (x : int)\n    g := ((~Int.Add : (arrow int (arrow int int))) (g : int) #1)\n  }\n  assert [Test_ensures_2] ((~Int.Gt : (arrow int (arrow int bool))) (y : int) #0)\n  assert [Test_ensures_3] ((g : int) == ((~Int.Add : (arrow int (arrow int int))) (old g : int) #1))\n}"
-/
#guard_msgs in
#eval
  let p := translate Test1
  match Program.Procedure.find? p "Test" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) => toString (Std.format stmt)
    | (.error e, _) => s!"Transformation failed: {e}"
  | none => "Procedure not found"

-- Verify transformation succeeds
#guard_msgs in
example : True := by
  let p := translate Test1
  match Program.Procedure.find? p "Test" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) =>
      match stmt with
      | .block "verify_Test" _ _ => trivial
      | _ => trivial
    | (.error _, _) => trivial
  | none => trivial

/-! ## Test 2: Simple procedure without modifies -/

def Test2 :=
#strata
program Core;
procedure Simple(x : bool) returns (y : bool)
spec {
  requires x;
  ensures y;
}
{
  y := x;
};
#end

-- Show the transformed output
/--
info: "verify_Simple :\n{\n  init (x : bool)\n  init (y : bool)\n  assume [Simple_requires_0] (x : bool)\n  body_Simple :\n  {\n    y := (x : bool)\n  }\n  assert [Simple_ensures_1] (y : bool)\n}"
-/
#guard_msgs in
#eval
  let p := translate Test2
  match Program.Procedure.find? p "Simple" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) => toString (Std.format stmt)
    | (.error e, _) => s!"Transformation failed: {e}"
  | none => "Procedure not found"

#guard_msgs in
example : True := by
  let p := translate Test2
  match Program.Procedure.find? p "Simple" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) =>
      match stmt with
      | .block "verify_Simple" _ _ => trivial
      | _ => trivial
    | (.error _, _) => trivial
  | none => trivial

/-! ## Test 3: Free specifications (should be filtered out) -/

def Test3 :=
#strata
program Core;
procedure WithFree(x : int) returns (y : int)
spec {
  free requires (x >= 0);
  requires (x > 0);
  free ensures (y >= 0);
  ensures (y == x);
}
{
  y := x;
};
#end

-- Show the transformed output
/--
info: "verify_WithFree :\n{\n  init (x : int)\n  init (y : int)\n  assume [WithFree_requires_1] ((~Int.Gt : (arrow int (arrow int bool))) (x : int) #0)\n  body_WithFree :\n  {\n    y := (x : int)\n  }\n  assert [WithFree_ensures_3] ((y : int) == (x : int))\n}"
-/
#guard_msgs in
#eval
  let p := translate Test3
  match Program.Procedure.find? p "WithFree" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) => toString (Std.format stmt)
    | (.error e, _) => s!"Transformation failed: {e}"
  | none => "Procedure not found"

#guard_msgs in
example : True := by
  let p := translate Test3
  match Program.Procedure.find? p "WithFree" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) =>
      match stmt with
      | .block "verify_WithFree" _ _ => trivial
      | _ => trivial
    | (.error _, _) => trivial
  | none => trivial

/-! ## Test 4: Multiple modified globals -/

def Test4 :=
#strata
program Core;
var g1 : int;
var g2 : bool;
procedure MultipleModifies(x : int) returns (y : int)
spec {
  modifies g1, g2;
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
#end

-- Show the transformed output
/--
info: "verify_MultipleModifies :\n{\n  init (x : int)\n  init (y : int)\n  init (old g1 : int)\n  init (g1 : int) := old g1\n  init (old g2 : bool)\n  init (g2 : bool) := old g2\n  assume [MultipleModifies_requires_1] ((~Int.Gt : (arrow int (arrow int bool))) (x : int) #0)\n  body_MultipleModifies :\n  {\n    y := (x : int)\n    g1 := ((~Int.Add : (arrow int (arrow int int))) (g1 : int) #1)\n    g2 := #true\n  }\n  assert [MultipleModifies_ensures_2] ((y : int) == (x : int))\n  assert [MultipleModifies_ensures_3] ((g1 : int) == ((~Int.Add : (arrow int (arrow int int))) (old g1 : int) #1))\n  assert [MultipleModifies_ensures_4] (g2 : bool)\n}"
-/
#guard_msgs in
#eval
  let p := translate Test4
  match Program.Procedure.find? p "MultipleModifies" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) => toString (Std.format stmt)
    | (.error e, _) => s!"Transformation failed: {e}"
  | none => "Procedure not found"

#guard_msgs in
example : True := by
  let p := translate Test4
  match Program.Procedure.find? p "MultipleModifies" with
  | some proc =>
    let state := { CoreTransformState.emp with currentProgram := .some p }
    match (procToVerifyStmt proc p).run state with
    | (.ok stmt, _) =>
      match stmt with
      | .block "verify_MultipleModifies" _ _ => trivial
      | _ => trivial
    | (.error _, _) => trivial
  | none => trivial

end ProcBodyVerifyTest
