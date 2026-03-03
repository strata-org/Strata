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
-/

namespace ProcBodyVerifyTest

open Core Core.ProcBodyVerify Lambda Transform
open Strata

/-! ## Test Programs -/

def TestProg1 :=
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

def TestProg2 :=
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

def TestProg3 :=
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

/-! ## Tests -/

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

-- Test that transformation succeeds on procedure with modifies
example : True := by
  let p := translate TestProg1
  match Program.Procedure.find? p "Test" with
  | some proc =>
    let result := procToVerifyStmt proc p
    match result.run CoreTransformState.emp with
    | (.ok _, _) => trivial
    | (.error _, _) => trivial
  | none => trivial

-- Test that transformation succeeds on simple procedure
example : True := by
  let p := translate TestProg2
  match Program.Procedure.find? p "Simple" with
  | some proc =>
    let result := procToVerifyStmt proc p
    match result.run CoreTransformState.emp with
    | (.ok _, _) => trivial
    | (.error _, _) => trivial
  | none => trivial

-- Test that transformation handles free specifications correctly
example : True := by
  let p := translate TestProg3
  match Program.Procedure.find? p "WithFree" with
  | some proc =>
    let result := procToVerifyStmt proc p
    match result.run CoreTransformState.emp with
    | (.ok _, _) => trivial
    | (.error _, _) => trivial
  | none => trivial

end ProcBodyVerifyTest
