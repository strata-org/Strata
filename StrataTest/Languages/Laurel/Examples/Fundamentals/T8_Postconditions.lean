/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"
procedure opaqueBody(x: int) returns (r: int)
// the presence of the ensures make the body opaque. we can consider more explicit syntax.
  ensures r > 0
{
  if x > 0 then { r := x }
  else { r := 1 }
};

procedure callerOfOpaqueProcedure() {
  var x: int := opaqueBody(3);
  assert x > 0;
  assert x == 3
//^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure invalidPostcondition(x: int)
    ensures false
//          ^^^^^ error: assertion does not hold
{
};

// Function with explicit ensures — body checked, caller gets assume
function absFunc(x: int): int
  ensures result >= 0
{
  if x >= 0 then x else -x
};

procedure callerOfAbsFunc() {
  var a: int := absFunc(-5);
  assert a >= 0
};

// Function with ensures — body is transparent, caller can reason about return value
function funcWithEnsures(x: int) returns (r: int)
  requires x > 0
  ensures r > 0
{
  x
};

procedure callerOfFuncWithEnsures() {
  var x: int := funcWithEnsures(3);
  assert x > 0;
  assert x == 3
};

// Function with invalid ensures — check procedure catches violation
function badEnsures(x: int): int
//       ^^^^^^^^^^ error: assertion does not hold
  ensures result > 0
{
  x
};

// Opaque function with ensures — caller relies solely on postcondition
function opaqueWithEnsures(x: int) returns (r: int)
  requires x > 0
  ensures r >= 0;
procedure callerOfOpaqueWithEnsures() {
  var y: int := opaqueWithEnsures(5);
  assert y >= 0
};

// Opaque function with body — caller cannot see the body
opaque function opaqueAbs(x: int): int
  ensures result >= 0
{
  if x >= 0 then x else -x
};
procedure callerOfOpaqueAbs() {
  var a: int := opaqueAbs(-5);
  assert a >= 0;
  assert a == 5
//^^^^^^^^^^^^^ error: assertion could not be proved
};

// Function calling opaque function — postcondition available via axiom
opaque function opaquePositive(x: int): int
  requires x >= 0
  ensures result >= 0
{ x };
function callsOpaque(x: int): int
  requires x >= 0
  ensures result >= 0
{ opaquePositive(x) };
procedure verifyCallsOpaque() {
  var y: int := callsOpaque(5);
  assert y >= 0
};

// Postconditioned function call inside quantifier with bound variable
opaque function opaqueInc(x: int): int
  ensures result > x
{ x + 1 };
procedure quantifierPostcond() {
  var b: bool := forall(n: int) { opaqueInc(n) } => opaqueInc(n) > n;
  assert b
};

// Postcondition with quantifier that shadows 'result'
opaque function shadowTest(x: int): int
//              ^^^^^^^^^^ error: assertion does not hold
  ensures result > 0 && forall(result: int) => result >= 0 ==> result + x >= 0
{ x + 1 };
procedure verifyShadowTest() {
  var y: int := shadowTest(5);
  assert y > 0
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" program 14 processLaurelFile
