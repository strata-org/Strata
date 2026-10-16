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

-- Not matched by the `catch`: the exception escapes the `try`. It is reported at
-- the `throw` it came from, although the check is on the `try`'s exit edge.
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
    if x < 0 then {
      var b: Exception := new Boom;
      throw b
//    ^^^^^^^ error: uncaught exception 'Exception' is not thrown could not be proved
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

-- A re-throw from a handler escapes the outermost `try`; the re-throw is reported.
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
    throw b
  } catch c when c is Boom {
    throw c
//  ^^^^^^^ error: uncaught exception 'Boom' is not thrown could not be proved
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

-- Several throw sites in one `try` with a `finally`: each reachable one is reported
-- at its own `throw`.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite A {}
procedure twoSites(x: int) returns (r: int)
  requires x != 2
  opaque
{
  r := 0;
  try {
    if x == 0 then { var a: A := new A; throw a };
//                                      ^^^^^^^ error: uncaught exception 'A' is not thrown does not hold
    if x == 1 then { var a2: A := new A; throw a2 };
//                                       ^^^^^^^^ error: uncaught exception 'A' is not thrown does not hold
    if x == 2 then { var a3: A := new A; throw a3 };
    r := 1
  } finally { r := 2 }
};
#end

-- An inner `try` that does not match passes the exception on unchanged: the
-- original `throw` is reported, not the inner `try`.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exception {}
composite A extends Exception {}
composite B extends Exception {}
procedure throughInner() returns (r: int)
  opaque
{
  r := 0;
  try {
    try {
      var a: Exception := new A;
      throw a
//    ^^^^^^^ error: uncaught exception 'Exception' is not thrown could not be proved
    } catch c when c is B {
      r := 1
    }
  } finally { r := 2 }
};
#end

-- An outermost `try` in another one's `finally`, with a throw site of its own: the
-- outer `throw` is still reported.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite A {}
composite B {}
procedure innerTryInFinally() returns (r: int)
  opaque
{
  r := 0;
  try {
    var a: A := new A;
    throw a
//  ^^^^^^^ error: uncaught exception 'A' is not thrown does not hold
  } finally {
    try { var b: B := new B; throw b } catch c { r := 3 }
  }
};
#end

/-! ## `catch` guards naming an unrelated type

A guard may test the caught exception against a type unrelated to its binding type
(the join of what the `try` body throws), e.g. the arms of a Java multi-catch. Such a
test can never be true: it is accepted without a diagnostic and lowered to `false`,
and the other arms still catch.
-/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite StateEx {}
composite ArithEx {}
procedure multiCatch(x: int) returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0;
  try {
    if x == 0 then { var e: ArithEx := new ArithEx; throw e };
    r := 1
  } catch c when c is StateEx || c is ArithEx {
    r := 0
  }
};
#end

-- Only an unrelated arm: the exception is not caught.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite StateEx {}
composite ArithEx {}
procedure onlyUnrelated(x: int) returns (r: int)
  opaque
{
  r := 0;
  try {
    if x == 0 then { var e: ArithEx := new ArithEx; throw e };
//                                                  ^^^^^^^ error: uncaught exception 'ArithEx' is not thrown does not hold
    r := 1
  } catch c when c is StateEx {
    r := 0
  }
};
#end

-- A type sharing a descendant with the binding type is not unrelated: under
-- multiple inheritance an `A` may be a `D`, which is a `B`, so the test may be true.
-- It is rejected rather than lowered to `false`.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite A {}
composite B {}
composite D extends A, B {}
procedure commonDescendant() returns (r: int)
  opaque
  ensures r == 0
{
  r := 0;
  { try {
      var a: A := new D;
      throw a
    } catch c when c is B {
//                 ^ error: cannot test unrelated type 'A' against 'B'
      r := 1
    } finally { exit L }
  } L
};
#end

-- A guard that can never hold makes its clause dead, and its body is discarded
-- unresolved, so a front end's read of the binding at the arm type
-- (`c as StateEx`, an unrelated cast here) is not rejected.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite StateEx { var code: int }
composite ArithEx {}
procedure deadArmRebind(x: int) returns (r: int)
  requires x != 0
  opaque
{
  r := 0;
  try {
    if x == 0 then { var e: ArithEx := new ArithEx; throw e };
    r := 1
  } catch c when c is StateEx {
    r := (c as StateEx)#code
  }
};
#end

-- Only a test of the binding against an unrelated type, or a disjunction of such
-- tests, makes a clause dead. A `false` guard, or a conjunction with such a test, is
-- not recognized: its clause's body is still resolved, and its errors reported.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite StateEx {}
composite ArithEx {}
procedure falseGuard(x: int) returns (r: int)
  requires x != 0
  opaque
{
  r := 0;
  try {
    if x == 0 then { var e: ArithEx := new ArithEx; throw e };
    r := 1
  } catch c when false {
    r := undefinedName
//       ^^^^^^^^^^^^^ error: 'undefinedName' is not defined
  }
};
procedure conjunctionGuard(x: int) returns (r: int)
  requires x != 0
  opaque
{
  r := 0;
  try {
    if x == 0 then { var e: ArithEx := new ArithEx; throw e };
    r := 1
  } catch c when c is StateEx && x > 0 {
    r := undefinedName
//       ^^^^^^^^^^^^^ error: 'undefinedName' is not defined
  }
};
#end

-- Outside a guard, testing the binding against an unrelated type is still an error.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite StateEx {}
composite ArithEx {}
procedure unrelatedTestInBody(x: int) returns (r: int)
  opaque
{
  r := 0;
  try {
    var e: ArithEx := new ArithEx;
    throw e
  } catch c when x > 0 {
    if c is StateEx then { r := 1 }
//     ^ error: cannot test unrelated type 'ArithEx' against 'StateEx'
  } catch c {
    r := 1
  }
};
#end

-- A binding typed at a wider join than its arm (`RtEx`, because the body also
-- throws an `ArEx`) read at the arm type reads the arm's fields.
#eval testLaurelExecution { skipCoreInterpreter := true, skipVerification := true } <|
#strata
program Laurel;
composite RtEx {}
composite MyEx extends RtEx { var code: int }
composite ArEx extends RtEx {}
procedure readAtArmType() entry opaque modifies * {
  var r: int := 0;
  var b: int := 1;
  try {
    if b == 0 then { var a: ArEx := new ArEx; throw a };
    var m: MyEx := new MyEx;
    m#code := 5;
    throw m
  } catch c when c is MyEx {
    r := (c as MyEx)#code
  };
  assert r == 5
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
    throw 7
//  ^^^^^^^ error: uncaught exception 'int' is not thrown does not hold
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
