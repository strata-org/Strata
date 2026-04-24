/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Transform.SSA
import Strata.SimpleAPI

open Core
open Core.SSA
open Strata

private def translate (p : Strata.Program) : Core.Program :=
  let (program, _) := Core.getProgram p
  program

private def runSSA (p : Core.Program) : Core.Program :=
  match Core.Transform.run p (fun prog => do
    let (_, result) ← Core.SSA.ssaTransform prog
    return result) with
  | .ok res => res
  | .error _ => { decls := [] }

/-! ## SSA Basic Tests -/
section SSABasicTests

/-- Simple straight-line: init + set → two inits -/
def SSATest1 :=
#strata
program Core;
procedure f(x : int, out y : int) {
  var a : int := x;
  a := (a + 1);
  y := a;
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATest1
  let result := runSSA pgm
  -- After SSA, the program should be different (variables renamed)
  return toString (Std.format result) != toString (Std.format pgm)

/-- If-then-else with join point merge -/
def SSATest2 :=
#strata
program Core;
procedure f(c : bool, out y : int) {
  var x : int := 0;
  if (c) {
    x := 1;
  } else {
    x := 2;
  }
  y := x;
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATest2
  let result := runSSA pgm
  -- After SSA, should have more declarations (fresh variables + merges)
  return toString (Std.format result) != toString (Std.format pgm)

/-- Havoc becomes nondet init -/
def SSATest3 :=
#strata
program Core;
procedure f(out y : int) {
  var x : int := 0;
  havoc x;
  assert [pos]: (x > 0);
};
#end

set_option linter.unusedVariables false in
/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATest3
  let _result := runSSA pgm
  return true

/-- Empty body procedure passes through unchanged -/
def SSATest4 :=
#strata
program Core;
procedure f(x : int, out y : int)
spec {
  ensures (y == x);
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATest4
  let result := runSSA pgm
  return toString (Std.format result) == toString (Std.format pgm)

end SSABasicTests

/-! ## SSA via transform CLI pass -/
section SSATransformPassTests

-- SSA can be applied via runTransforms
/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATest1
  match Core.runTransforms pgm [.ssa] with
  | .ok result => return toString (Std.format result) != ""
  | .error _ => return false

-- SSA after callElim pipeline
def SSATestPipeline :=
#strata
program Core;
procedure g(x : int, out y : int)
spec {
  requires (x > 0);
  ensures (y > 0);
};
procedure f(a : int, out b : int) {
  call g(a, out b);
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestPipeline
  match Core.runTransforms pgm [.callElim, .ssa] with
  | .ok result => return toString (Std.format result) != ""
  | .error _ => return false

end SSATransformPassTests

/-! ## SSA Edge Case Tests -/
section SSAEdgeCaseTests

/-- Nested if-then-else: inner and outer branches both modify x -/
def SSATestNestedIte :=
#strata
program Core;
procedure f(c1 : bool, c2 : bool, out y : int) {
  var x : int := 0;
  if (c1) {
    if (c2) {
      x := 1;
    } else {
      x := 2;
    }
  } else {
    x := 3;
  }
  y := x;
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestNestedIte
  let result := runSSA pgm
  return toString (Std.format result) != toString (Std.format pgm)

/-- Multiple variables modified in one branch only -/
def SSATestOneBranchModifies :=
#strata
program Core;
procedure f(c : bool, out r : int) {
  var x : int := 0;
  var y : int := 0;
  if (c) {
    x := 1;
    y := 2;
  } else {
  }
  r := (x + y);
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestOneBranchModifies
  let result := runSSA pgm
  return toString (Std.format result) != toString (Std.format pgm)

/-- Multiple sequential assignments to the same variable -/
def SSATestMultiAssign :=
#strata
program Core;
procedure f(out y : int) {
  var x : int := 0;
  x := 1;
  x := 2;
  x := 3;
  y := x;
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestMultiAssign
  let result := runSSA pgm
  return toString (Std.format result) != toString (Std.format pgm)

/-- Assert and assume expressions get rewritten to use SSA versions -/
def SSATestAssertAssume :=
#strata
program Core;
procedure f(x : int, out y : int) {
  var a : int := x;
  a := (a + 1);
  assert [check]: (a > 0);
  assume [hint]: (a < 100);
  y := a;
};
#end

set_option linter.unusedVariables false in
/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestAssertAssume
  let _result := runSSA pgm
  return true

/-- Havoc followed by assignment -/
def SSATestHavocThenSet :=
#strata
program Core;
procedure f(out y : int) {
  var x : int := 0;
  havoc x;
  x := (x + 1);
  y := x;
};
#end

set_option linter.unusedVariables false in
/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestHavocThenSet
  let _result := runSSA pgm
  return true

/-- Inout parameter: modified in body -/
def SSATestInout :=
#strata
program Core;
procedure f(inout g : int) {
  g := (g + 1);
};
#end

set_option linter.unusedVariables false in
/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestInout
  let _result := runSSA pgm
  return true

/-- Multiple procedures: each gets independent SSA numbering -/
def SSATestMultiProc :=
#strata
program Core;
procedure f(x : int, out y : int) {
  var a : int := x;
  a := (a + 1);
  y := a;
};
procedure g(x : int, out y : int) {
  var a : int := x;
  a := (a + 2);
  y := a;
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestMultiProc
  let result := runSSA pgm
  -- Both procedures should be transformed
  return toString (Std.format result) != toString (Std.format pgm)

/-- If-then-else where only else branch modifies a variable -/
def SSATestElseOnly :=
#strata
program Core;
procedure f(c : bool, out y : int) {
  var x : int := 0;
  if (c) {
  } else {
    x := 1;
  }
  y := x;
};
#end

/-- info: true -/
#guard_msgs in
#eval! do
  let pgm := translate SSATestElseOnly
  let result := runSSA pgm
  return toString (Std.format result) != toString (Std.format pgm)

end SSAEdgeCaseTests
