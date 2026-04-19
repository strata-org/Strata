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
constrained posnat = x: nat where x != 0 witness 1

// Input constraint becomes requires — body can rely on it
procedure inputAssumed(n: nat)
  opaque
{
  assert n >= 0
};

// Output constraint — valid return passes
procedure outputValid(): nat
  opaque
{
  return 3
};

// Output constraint — invalid return fails
procedure outputInvalid(): nat
//                         ^^^ error: assertion does not hold
  opaque
{
  return -1
};

// Return value of constrained type — caller gets ensures via call elimination
procedure opaqueNat(): nat;
procedure callerAssumes() returns (r: int)
  opaque
{
  var x: int := opaqueNat();
  assert x >= 0;
  return x
};

// Assignment to constrained-typed variable — valid
procedure assignValid()
  opaque
{
  var y: nat := 5
};

// Assignment to constrained-typed variable — invalid
procedure assignInvalid()
  opaque
{
  var y: nat := -1
//^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Reassignment to constrained-typed variable — invalid
procedure reassignInvalid()
  opaque
{
  var y: nat := 5;
  y := -1
//^^^^^^^ error: assertion does not hold
};

// Argument to constrained-typed parameter — valid
procedure takesNat(n: nat) returns (r: int)
  opaque
{ return n };
procedure argValid() returns (r: int)
  opaque
{
  var x: int := takesNat(3);
  return x
};

// Argument to constrained-typed parameter — invalid (requires violation)
procedure argInvalid() returns (r: int)
  opaque
{
  var x: int := takesNat(-1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  return x
};

// Nested constrained type — independent constraints require transitive collection
constrained even = x: int where x % 2 == 0 witness 0
constrained evenpos = x: even where x > 0 witness 2
procedure nestedInput(x: evenpos)
  opaque
{
  assert x > 0;
  assert x % 2 == 0
};

// Multiple constrained-typed parameters
procedure multiParam(a: nat, b: nat)
  opaque
{
  assert a >= 0;
  assert b >= 0
};

// Two calls to same procedure — no temp var collision
procedure twoCalls() returns (r: int)
  opaque
{
  var a: int := takesNat(1);
  var b: int := takesNat(2);
  return a + b
};

// Constrained type in expression position must be resolved
procedure constrainedInExpr()
  opaque
{
  var b: bool := forall(n: nat) => n + 1 > n;
  assert b
};

// Invalid witness — witness -1 does not satisfy x > 0
constrained bad = x: int where x > 0 witness -1
//                                           ^^ error: assertion does not hold

// Uninitialized constrained variable — havoc + assume constraint
procedure uninitNat()
  opaque
{
  var y: nat;
  assert y >= 0
};

// Uninitialized nested constrained variable — havoc + assume constraint
procedure uninitPosnat()
  opaque
{
  var y: posnat;
  assert y != 0;
  assert y >= 0
};

// Uninitialized constrained variable — witness value is not provable
procedure uninitNotWitness()
  opaque
{
  var y: posnat;
  assert y == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};

// Function with valid constrained return — constraint not checked (not yet supported)
function goodFunc(): nat { 3 };
//       ^^^^^^^^ error: constrained return types on functions are not yet supported

// Function with invalid constrained return — constraint not checked (not yet supported)
function badFunc(): nat { -1 };
//       ^^^^^^^ error: constrained return types on functions are not yet supported

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood()
  opaque
{
  var x: int := goodFunc();
  assert x >= 0
};

// Quantifier constraint injection — forall
// n + 1 > 0 is only provable with n >= 0 injected; false for all int
procedure forallNat()
  opaque
{
  var b: bool := forall(n: nat) => n + 1 > 0;
  assert b
};

// Quantifier constraint injection — exists
// n == -1 is satisfiable for int, but not when n >= 0 is required
// n == 42 works because 42 >= 0
procedure existsNat()
  opaque
{
  var b: bool := exists(n: nat) => n == 42;
  assert b
};

// Quantifier constraint injection — nested constrained type
// n - 1 >= 0 is only provable with n > 0 injected
procedure forallPosnat()
  opaque
{
  var b: bool := forall(n: posnat) => n - 1 >= 0;
  assert b
};

// Capture avoidance — bound var y in constraint must not collide with parameter y
// Without capture avoidance, requires becomes exists(y) => y > y (false), making body vacuously true
constrained haslarger = x: int where (exists(y: int) => y > x) witness 0
procedure captureTest(y: haslarger)
  opaque
{
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ConstrainedTypes" program 14 processLaurelFile

end Laurel
end Strata
