/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
constrained nat = x: int where x >= 0 witness 0
constrained posnat = x: nat where x > 0 witness 1

// Input constraint becomes requires — body can rely on it
procedure inputAssumed(n: nat) {
  assert n >= 0;
}

// Output constraint — valid return passes
procedure outputValid(): nat {
  return 3;
}

// Output constraint — invalid return fails
procedure outputInvalid(): nat {
//                         ^^^ error: assertion does not hold
  return -1;
}

// Return value of constrained type — caller gets ensures via call elimination
procedure opaqueNat(): nat
procedure callerAssumes() returns (r: int) {
  var x: int := opaqueNat();
  assert x >= 0;
  return x;
}

// Assignment to constrained-typed variable — valid
procedure assignValid() {
  var y: nat := 5;
}

// Assignment to constrained-typed variable — invalid
procedure assignInvalid() {
  var y: nat := -1;
//              ^^ error: assertion does not hold
}

// Reassignment to constrained-typed variable — invalid
procedure reassignInvalid() {
  var y: nat := 5;
  y := -1;
//^^^^^^^^ error: assertion does not hold
}

// Argument to constrained-typed parameter — valid
procedure takesNat(n: nat) returns (r: int) { return n; }
//                    ^^^ error: assertion does not hold
procedure argValid() returns (r: int) {
  var x: int := takesNat(3);
  return x;
}

// Argument to constrained-typed parameter — invalid (requires violation)
procedure argInvalid() returns (r: int) {
  var x: int := takesNat(-1);
  return x;
}

// Nested constrained type — posnat is nat with x > 0, nat is int with x >= 0
procedure nestedInput(x: posnat) {
  assert x > 0;
  assert x >= 0;
}

// Multiple constrained-typed parameters
procedure multiParam(a: nat, b: nat) {
  assert a >= 0;
  assert b >= 0;
}

// Two calls to same procedure — no temp var collision
procedure twoCalls() returns (r: int) {
  var a: int := takesNat(1);
  var b: int := takesNat(2);
  return a + b;
}

// Constrained type in expression position must be resolved
procedure constrainedInExpr() {
  var b: bool := forall(n: nat) => n + 1 > n;
  assert b;
}

// Invalid witness — witness -1 does not satisfy x > 0
constrained bad = x: int where x > 0 witness -1
//                             ^^^^^ error: assertion does not hold

// Uninitialized constrained variable — witness used as default
procedure uninitNat() {
  var y: nat;
  assert y >= 0;
}

// Uninitialized nested constrained variable — outermost witness used
procedure uninitPosnat() {
  var y: posnat;
  assert y > 0;
  assert y >= 0;
}

// Function with valid constrained return — cleared isFunctional, ensures passes
// TODO: restore isFunctional once function postconditions are supported
function goodFunc(): nat { 3 }

// Function with invalid constrained return — ensures catches it
function badFunc(): nat { -1 }
//                  ^^^ error: assertion does not hold

// Caller of constrained function — ensures assumed via call elimination
procedure callerGood() {
  var x: int := goodFunc();
  assert x >= 0;
}

// Quantifier constraint injection — forall
procedure forallNat() {
  var b: bool := forall(n: nat) => n >= 0;
  assert b;
}

// Quantifier constraint injection — exists
procedure existsNat() {
  var b: bool := exists(n: nat) => n == 42;
  assert b;
}

// Quantifier constraint injection — nested constrained type
procedure forallPosnat() {
  var b: bool := forall(n: posnat) => n > 0 && n >= 0;
  assert b;
}

// Capture avoidance — bound var y in constraint must not collide with parameter y
// Without capture avoidance, requires becomes exists(y) => y > y (false), making body vacuously true
constrained haslarger = x: int where (exists(y: int) => y > x) witness 0
procedure captureTest(y: haslarger) {
  assert false;
//^^^^^^^^^^^^^ error: assertion does not hold
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ConstrainedTypes" program 14 processLaurelFile

end Laurel
end Strata
