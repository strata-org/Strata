/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Tests.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util
open StrataTest.Util.Concurrency
open Strata

/-!
## Assigning to an input parameter

A procedure body may assign to an input parameter. The write is local to the
body: body code — including loop guards and invariants — reads the current
value, while specifications (`requires`, `ensures`, `decreases`) and `old(...)`
always denote the parameter's ENTRY value.
-/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure plainReassign(x: int)
  opaque
{
  x := 1;
  assert x == 1
};

// The loop guard and the invariant read the current value of the input.
procedure loopCountdown(n: int)
  requires 0 <= n
  opaque
{
  while (n > 0)
    invariant 0 <= n
  {
    n := n - 1
  };
  assert n == 0
};

// A specification reference to a mutated input means its ENTRY value: the body
// doubles `x` in place, and the postcondition's `x + x` still refers to the
// argument the caller passed.
procedure postconditionSeesEntryValue(x: int) returns (r: int)
  requires 0 <= x
  opaque
  ensures r == x + x
{
  x := x + x;
  r := x
};

// In the body, `old(x)` denotes the entry value while `x` reads the live
// value — and is therefore not flagged as a no-op `old`.
procedure bodyOldSeesEntryValue(x: int)
  opaque
{
  x := x + 1;
  assert old(x) + 1 == x
};

// The same holds when the write is an increment or a compound assignment.
procedure bodyOldAfterIncrement(x: int)
  opaque
{
  x++;
  assert old(x) + 1 == x
};

procedure bodyOldAfterCompoundAssign(x: int)
  opaque
{
  x += 2;
  assert old(x) + 2 == x
};

// In a specification a bare `x` already denotes the entry value, so `old(x)`
// there is a no-op even when the body assigns `x`.
procedure specOldIsNoOp(x: int) returns (r: int)
  opaque
  ensures r == old(x) + 1
//             ^^^^^^ warning: `old(...)` has no effect
{
  x := x + 1;
  r := x
};

// A body `old(x)` over an input the body never assigns is a no-op.
procedure bodyOldOverUnassignedInputIsNoOp(x: int)
  opaque
{
  assert old(x) == x
//       ^^^^^^ warning: `old(...)` has no effect
};

// A binder that shadows the reassigned input is a different variable: the
// quantified `x` ranges over all integers, whatever the body assigned to the
// input.
procedure shadowingBinderIsUntouched(x: int)
  opaque
{
  x := 5;
  assert exists(x: int) => x == 6
};
#end

-- The Core and Laurel interpreters agree with the verifier on a reassigned
-- input, in a transparent body, an opaque body and a loop.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure bump(x: int): int { x := x + 1; return x };

procedure clamp(x: int) returns (r: int)
  opaque
  ensures r >= 0
{
  if (x < 0) then { x := 0 };
  r := x
};

procedure countdown(n: int) returns (r: int)
  requires 0 <= n
  opaque
  ensures r == 0
{
  while (n > 0)
    invariant 0 <= n
  {
    n := n - 1
  };
  r := n
};

procedure main()
  entry
  opaque
{
  assert bump(1) == 2;
  var c: int := clamp(-3);
  assert c >= 0;
  var z: int := countdown(3);
  assert z == 0
};
#end

-- A reassignment inside a block value is visible after the block: `f(1)` is 2
-- on the JVM (`int u = (x = x + 1); return x;`).
#eval testLaurelVerification <|
#strata
program Laurel;
procedure blockValueReassign(x: int): int
{
  var u: int := { x := x + 1; x };
  return x
};

procedure callerSeesUpdate()
  opaque
{
  assert blockValueReassign(1) == 2
};
#end

-- An assignment to an input of a constrained type is checked against the
-- constraint, as an assignment to a local of that type is.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0

procedure dec(n: nat)
  opaque
{
  n := n - 1
//^^^^^^^^^^ error: assertion does not hold
};
#end

-- The same holds in a transparent body, whose caller sees the new value.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0

procedure inc(n: nat): int { n := n + 1; return n };

procedure callerSeesIncrement()
  opaque
{
  assert inc(1) == 2
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0

procedure decTransparent(n: nat): int { n := n - 1; return n };
//                                      ^^^^^^^^^^ error: assertion does not hold
#end

-- A coroutine may reassign an input: the body reads the current value across
-- a yield, and the entry value is not what it reads.
#eval testLaurelVerification (options := coroutineOptions) <|
#strata
program Laurel;

coroutine reassignAcrossYield(n: int)
  requires n == 0
  modifies *
{
  n := 5;
  yield;
  assert n == 5
};

coroutine entryValueNotReadAfterYield(n: int)
  requires n == 0
  modifies *
{
  n := 5;
  yield;
  assert n == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A coroutine's `relies` or `guarantees` may not mention a reassigned input.
#eval testLaurelVerification (options := coroutineOptions) <|
#strata
program Laurel;

coroutine guaranteesOverReassignedInput(n: int)
  requires n == 0
  guarantees n == 0
//           ^ error: a coroutine's relies/guarantees cannot YET refer to input parameter 'n', which the body reassigns; copy the input into a local and reassign that instead
  modifies *
{
  n := 5;
  yield
};

coroutine reliesOverReassignedInput(n: int)
  requires n == 0
  relies n == 0
//       ^ error: a coroutine's relies/guarantees cannot YET refer to input parameter 'n', which the body reassigns; copy the input into a local and reassign that instead
  modifies *
{
  n := 5;
  yield
};
#end

-- Nor may a body `oldGuarantee(...)` or `oldRelies(...)`.
#eval testLaurelVerification (options := coroutineOptions) <|
#strata
program Laurel;

coroutine oldGuaranteeOverReassignedInput(n: int)
  requires n == 0
  modifies *
{
  n := 5;
  yield;
  assert oldGuarantee(n) == 0
//                    ^ error: `oldGuarantee(...)`/`oldRelies(...)` cannot YET refer to input parameter 'n', which the body reassigns; copy the input into a local and reassign that instead
};

coroutine oldReliesOverReassignedInput(n: int)
  requires n == 0
  modifies *
{
  n := 5;
  yield;
  assert oldRelies(n) == 0
//                 ^ error: `oldGuarantee(...)`/`oldRelies(...)` cannot YET refer to input parameter 'n', which the body reassigns; copy the input into a local and reassign that instead
};
#end
