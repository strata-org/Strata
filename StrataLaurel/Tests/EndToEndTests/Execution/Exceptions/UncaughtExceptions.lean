/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Uncaught exceptions in a procedure that declares no `throws`.

Such an exception is not a static error. `EliminateExceptions` asserts, where the
exception would leave the procedure, that it does not:
  * an uncaught `throw` outside every `try` becomes `assert false`, so it is an error
    only if the `throw` is reachable;
  * an uncaught call to a throwing procedure asserts that the call did not throw,
    which the callee's `throwsOn` contract proves or refutes for these arguments;
  * an exception that reaches the end of an outermost `try` (a `catch` that did not
    match, or no `catch` at all) is asserted not to be pending there. The assertion
    is on that edge rather than at the `throw` because the `try` may still intercept
    it, e.g. with a `finally` that completes abruptly.

A procedure that declares `throws T` is unaffected: its escapes propagate, and an
escape outside `T` is still rejected statically (`ThrowsEscape.lean`).
-/

/-! ## Literal `throw` -/

-- Unreachable under the precondition: verifies.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Boom {}
procedure unreachableThrow(x: int) returns (r: int)
  requires x >= 0
  opaque
{
  if x < 0 then {
    var b: Boom := new Boom;
    throw b
  };
  r := x
};
#end

-- Reachable: the `throw` itself is reported, and only once (the `if` branch that
-- throws does not fall through into a second failure).
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Boom {}
procedure reachableThrow(x: int) returns (r: int)
  opaque
  ensures r == x
{
  if x < 0 then {
    var b: Boom := new Boom;
    throw b
//  ^^^^^^^ error: uncaught exception 'Boom' is not thrown does not hold
  };
  r := x
};
#end

/-! ## Calls to throwing procedures -/

-- The callee's `throwsOn` guard is false for these arguments: verifies.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure thrower(x: int) returns (r: int)
  throws (e: int)
  opaque
  ensures r == x
  throwsOn x < 0 {
    ensures e == 42
  }
{
  if x < 0 then {
    throw 42
  };
  r := x
};
procedure callsSafely() returns (r: int)
  opaque
  ensures r == 1
{
  r := thrower(1)
};
#end

-- The guard holds for these arguments: the call is reported.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure thrower(x: int) returns (r: int)
  throws (e: int)
  opaque
  throwsOn x < 0 {
    ensures e == 42
  }
{
  if x < 0 then {
    throw 42
  };
  r := x
};
procedure callsUnsafely() returns (r: int)
  opaque
{
  r := thrower(-1)
//     ^^^^^^^^^^^ error: call does not throw an uncaught 'int' does not hold
};
#end

-- A callee that states no `throwsOn` cases says nothing about when it throws, so a
-- call to it cannot be proved not to throw.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exception {}
procedure mayThrow() returns (r: int)
  throws (e: Exception)
  opaque;
procedure callsUnknown() returns (r: int)
  opaque
{
  r := mayThrow()
//     ^^^^^^^^^^ error: call does not throw an uncaught 'Exception' could not be proved
};
#end

-- A void call statement is checked the same way.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure check(x: int)
  throws (e: int)
  opaque
  throwsOn x < 0 { }
{
  if x < 0 then {
    throw 1
  }
};
procedure callsVoid(y: int)
  requires y >= 0
  opaque
{
  check(y)
};
#end

/-! ## Inside a `try` -/

-- Caught: no obligation at all, even though the `throw` always runs.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Boom {}
procedure caught() returns (r: int)
  opaque
  ensures r == -1
{
  var b: Boom := new Boom;
  try {
    throw b
  } catch c when c is Boom {
    r := -1
  }
};
#end

-- Not matched by the `catch`: the exception escapes the `try`, reported there.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exception {}
composite Boom extends Exception {}
composite Other extends Exception {}
procedure notMatched(x: int) returns (r: int)
  opaque
{
  r := 0;
  try {
//^ error: no exception escapes this `try` uncaught could not be proved
    if x < 0 then {
      var b: Exception := new Boom;
      throw b
    }
  } catch c when c is Other {
    r := -1
  }
};
#end

-- The same shape is fine when the escaping path is unreachable.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exception {}
composite Boom extends Exception {}
composite Other extends Exception {}
procedure notMatchedUnreachable(x: int) returns (r: int)
  requires x >= 0
  opaque
{
  r := 0;
  try {
    if x < 0 then {
      var b: Exception := new Boom;
      throw b
    }
  } catch c when c is Other {
    r := -1
  }
};
#end

-- A re-throw from a handler escapes the outermost `try` and is reported there.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Boom {}
procedure rethrows() returns (r: int)
  opaque
{
  r := 0;
  var b: Boom := new Boom;
  try {
//^ error: no exception escapes this `try` uncaught could not be proved
    throw b
  } catch c when c is Boom {
    throw c
  }
};
#end

-- A `finally` that always returns discards the pending exception: verifies (an
-- `assert false` at the `throw` would have been a false alarm here).
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Boom {}
procedure swallowedByFinally() returns (r: int)
  opaque
  ensures r == 7
{
  var b: Boom := new Boom;
  try {
    throw b
  } finally {
    r := 7;
    return
  }
};
#end

-- A throwing call inside a `try` whose `catch` handles it: no obligation.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exception {}
procedure mayThrow() returns (r: int)
  throws (e: Exception)
  opaque;
procedure callsInTry() returns (r: int)
  opaque
{
  r := 0;
  try {
    r := mayThrow()
  } catch c {
    r := -1
  }
};
#end

/-! ## Concrete execution

The Core interpreter treats `assume` as a no-op, so each escape assertion is followed
by an exit from the procedure: the `entry` procedure stops where the exception would
have left it. These run the verifier and the Core interpreter against the same
annotations. The standalone Laurel interpreter runs before `EliminateExceptions` and
aborts on an escaping exception ("uncaught throw"), so it runs only the caught case.
-/

-- Nothing after an uncaught `throw` runs: the division by zero is not reached.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure stopsAtThrow() entry opaque {
  var z: int := 0;
  if z == 0 then { throw 7 };
//                 ^^^^^^^ error: uncaught exception 'int' is not thrown does not hold
  var q: int := 10 / z
};
#end

-- Nothing after an uncaught throwing call runs: its result is not unwrapped.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure thrower(x: int) returns (r: int)
  throws (e: int)
  opaque
  throwsOn x < 0 { ensures e == 42 }
{ if x < 0 then { throw 42 }; r := x };
procedure stopsAtCall() entry opaque {
  var y: int := thrower(-1);
//              ^^^^^^^^^^^ error: call does not throw an uncaught 'int' does not hold
  assert y == -1
};
#end

-- Nothing after a `try` that an exception escapes runs.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure stopsAfterTry() entry opaque {
  var z: int := 0;
  try {
//^ error: no exception escapes this `try` uncaught does not hold
    throw 7
  } catch c when c == 8 {
    z := 1
  };
  var q: int := 10 / z
};
#end

-- A caught exception runs the handler and continues normally.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure thrower(x: int) returns (r: int)
  throws (e: int)
  opaque
  throwsOn x < 0 { ensures e == 42 }
{ if x < 0 then { throw 42 }; r := x };
procedure handles() entry opaque {
  var y: int := 0;
  try {
    y := thrower(-1)
  } catch c {
    y := c
  };
  assert y == 42
};
#end
