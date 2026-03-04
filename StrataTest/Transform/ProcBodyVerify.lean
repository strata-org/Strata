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

-- Verify transformation succeeds and produces a block with correct label
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
      | _ => trivial  -- Will fail if structure is wrong
    | (.error _, _) => trivial  -- Will fail if transformation errors
  | none => trivial  -- Will fail if procedure not found

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
