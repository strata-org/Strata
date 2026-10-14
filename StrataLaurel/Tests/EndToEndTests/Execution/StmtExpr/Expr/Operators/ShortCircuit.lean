/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure mustNotCallFunc(x: int): int
  requires false
{ return x };

procedure mustNotCallProc(): int
  requires false
  opaque
{
  return 0
};

// Pure path: function with requires false
procedure testAndThenFunc()
  entry
  opaque
{
  var b: bool := false && mustNotCallFunc(0) > 0;
  assert !b
};

procedure testOrElseFunc()
  entry
  opaque
{
  var b: bool := true || mustNotCallFunc(0) > 0;
  assert b
};

procedure testImpliesFunc()
  entry
  opaque
{
  var b: bool := false ==> mustNotCallFunc(0) > 0;
  assert b
};

// Pure path: division by zero

procedure testAndThenDivByZero()
  entry
  opaque
{
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero()
  entry
  opaque
{
  assert true || 1 / 0 > 0
};

procedure testImpliesDivByZero()
  entry
  opaque
{
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc()
  entry
  opaque
{
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc()
  entry
  opaque
{
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc()
  entry
  opaque
{
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
#end

/-! ## A doubly booby-trapped callee

The right operand's callee is trapped two ways, so every path observes a
short-circuit miss:

- `requires false` — at a guarded call site the precondition is never checked
  because `&&`/`||` short-circuit. If a short-circuit misfired, the verifier and
  both interpreters would report it.
- body `assert false` — if either interpreter actually entered the callee it
  would record an assertion failure. Short-circuited, the callee is never
  entered, so no failure fires. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure boom() returns (r: bool)
  requires false
  opaque
{
  assert false;
  return true
};

procedure shortCircuitAndThen()
  entry
  opaque
{
  var b: bool := false && boom();
  assert !b
};

procedure shortCircuitOrElse()
  entry
  opaque
{
  var b: bool := true || boom();
  assert b
};
#end
