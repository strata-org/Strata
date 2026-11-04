/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests that the constrained type elimination pass correctly transforms
Laurel programs by comparing the output against expected results.

Uses `runPassAfterForIdiomaticity`, the shared idiomaticity driver run with
`EliminateValueInReturns` as the predecessor: parse, resolve, eliminate values in
returns, run `constrainedTypeElimPass`, print the result for the `#guard_msgs`
golden. The predecessor is what makes the input the pass expects — it rewrites
`return e` into an assignment to the output followed by a bare `return`, and an
assignment to the output is exactly what the pass checks a constrained output's
constraint on. Without it a `return e` would carry the value past the pass
unchecked (`StmtExpr.Return.value.some` is in the pass's `unsupported` list).
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.ConstrainedTypeElim
import StrataLaurel.Implementation.EliminateValueInReturns

open Strata
open StrataTest.Util

namespace Strata.Laurel

/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure test(n: int)
  returns (r: int)
  requires nat$constraint(n)
  opaque
  ensures nat$constraint(r)
{
  assert r >= 0;
  var y: int := n;
  assert nat$constraint(y);
  r := y;
  assert nat$constraint(r);
  return
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure test(n: nat) returns (r: nat) opaque {
  assert r >= 0;
  var y: nat := n;
  return y
};
#end

-- Scope management: constrained variable in if-branch must not leak into sibling block
/--
info: procedure pos$constraint(v: int): bool
{
  $result := v > 0;
  return
};
procedure test(b: bool)
  opaque
{
  if b
    then {
      var x: int := 1;
      assert pos$constraint(x)
    };
  {
    var x: int := -5;
    x := -10
  }
};
procedure $witness_pos()
  opaque
{
  var $witness: int := 1;
  assert pos$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained pos = v: int where v > 0 witness 1
procedure test(b: bool) opaque {
  if b then {
    var x: pos := 1
  };
  {
    var x: int := -5;
    x := -10
  }
};
#end

-- Uninitialized constrained variable: havoc + assume constraint.
-- The variable has no known value, only the type constraint is assumed.
/--
info: procedure posint$constraint(x: int): bool
{
  $result := x > 0;
  return
};
procedure f()
  opaque
{
  var x: int;
  assume posint$constraint(x);
  assert x == 1
};
procedure $witness_posint()
  opaque
{
  var $witness: int := 1;
  assert posint$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained posint = x: int where x > 0 witness 1
procedure f() opaque {
  var x: posint;
  assert x == 1
};
#end

-- Hole of a constrained type: bound to a fresh local whose constraint is assumed, so the
-- declaration's check holds.
/--
info: procedure posint$constraint(x: int): bool
{
  $result := x > 0;
  return
};
procedure f()
  opaque
{
  var x: int := {
    var $constrainedHole0: int := <?>;
    assume posint$constraint($constrainedHole0);
    $constrainedHole0
  };
  assert posint$constraint(x);
  assert x == 1
};
procedure $witness_posint()
  opaque
{
  var $witness: int := 1;
  assert posint$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained posint = x: int where x > 0 witness 1
procedure f() opaque {
  var x: posint := <?>;
  assert x == 1
};
#end

-- Composite field of constrained type: a field constraint axiom procedure, the
-- field read assumed in range, and the output checked where the body assigns it.
/--
info: composite Ctr { var n: int }
procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure getN(c: Ctr): int
{
  $result := {
    assume nat$constraint(c#n);
    c#n
  };
  assert nat$constraint($result);
  return
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
procedure $fieldConstraint_Ctr$n($o: Ctr)
  invokeOn $o#n
  opaque
  ensures nat$constraint($o#n);
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Ctr { var n: nat }
procedure getN(c: Ctr) : nat { return c#n };
#end

-- Generic procedure: the output check sits in the polymorphic body, where the
-- procedure's type arguments are already in scope, so it carries none itself.
/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure countOf<T>(x: T): int
{
  $result := 0;
  assert nat$constraint($result);
  return
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure countOf<T>(x: T) : nat { return 0 };
#end

-- Transparent body whose value is a trailing expression rather than a `return`:
-- the value becomes an assignment to the output, so it gets checked. The
-- fall-off-the-end exit check then restates it.
/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure tail(): int
{
  $result := 3;
  assert nat$constraint($result);
  assert nat$constraint($result)
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure tail() : nat { 3 };
#end

-- Transparent body that leaves its constrained output unassigned on a path:
-- the check lands after the body, on the path that falls off its end.
/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure partial(b: bool)
  returns (r: int)
{
  if b
    then {
      r := 1;
      assert nat$constraint(r)
    };
  assert nat$constraint(r)
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure partial(b: bool) returns (r: nat) { if b then { r := 1 } };
#end

end Laurel
