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
//     ^^^^^^^^^^ error: call does not throw an uncaught 'Exception' does not hold
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
//    ^^^^^^^ error: uncaught exception 'Exception' is not thrown does not hold
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
//  ^^^^^^^ error: uncaught exception 'Boom' is not thrown does not hold
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
//    ^^^^^^^ error: uncaught exception 'Exception' is not thrown does not hold
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
-- multiple inheritance an `A` may be a `D`, which is a `B`, so the test is kept and
-- catches the `D`.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite A {}
composite B {}
composite D extends A, B {}
procedure commonDescendant() returns (r: int)
  opaque
  ensures r == 1
{
  r := 0;
  try {
    var a: A := new D;
    throw a
  } catch c when c is B {
    r := 1
  }
};
#end

-- A `C` escapes a `try` whose exception type is `B` into a `throws A` procedure: the
-- two exception variables are copied through a cast, so the escaping `C` arrives.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite A {}
composite B {}
composite B2 extends B {}
composite C extends A, B {}
procedure escapesThroughSharedDescendant(pick: bool)
  throws (e: A)
  opaque
  throwsOn pick {
    ensures e is C
  }
{
  var c: C := new C;
  var b2: B2 := new B2;
  try {
    if pick then { throw c } else { throw b2 }
  } catch e when e is B2 {
    assert true
  }
};

procedure escapesThroughSharedDescendantFalse(pick: bool)
  throws (e: A)
  opaque
  throwsOn pick {
    ensures !(e is C)
//          ^^^^^^^^^ error: postcondition does not hold
  }
{
  var c: C := new C;
  var b2: B2 := new B2;
  try {
    if pick then { throw c } else { throw b2 }
  } catch e when e is B2 {
    assert true
  }
};
#end

-- The cast is asserted where the exception crosses into an `A`-typed `try`. In
-- `untypedEscape`, `collectThrownTypes` cannot type the handler's `throw h#b`, so the
-- outer `try` is typed `A` (its `C` and `A2`). In `nestedInHandler`, the inner `try`
-- propagates into its handler's `try`, typed `A` by that `try`'s body alone.
-- `parameterEscape` verifies: its `h#b` is a `B4` and is caught, the parameter `c`,
-- thrown in a nested `try` and rethrown by the handler, is an `A`, and the `int` raised
-- inside, which `is` cannot test, is caught.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite A {}
composite A2 extends A {}
composite B {}
composite B3 extends B {}
composite B4 extends B {}
composite C extends A, B {}
composite H { var b: B }
procedure untypedEscape(h: H, k: int)
  opaque
{
  var c: C := new C;
  var b4: B4 := new B4;
  var a2: A2 := new A2;
  try {
    try {
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: the exception escaping this try fits the 'A' it propagates into does not hold
      if k == 0 then { throw c } else { throw b4 }
    } catch e when e is B4 { throw h#b };
    if k == 5 then { throw a2 }
  } catch e { assert e is A }
};

procedure nestedInHandler(k: int)
  opaque
{
  var c: C := new C;
  var a2: A2 := new A2;
  var b3: B3 := new B3;
  var b4: B4 := new B4;
  try {
    if k == 0 then { throw a2 } else { throw c }
  } catch x {
    try {
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: the exception escaping this try fits the 'A' it propagates into does not hold
      if k == 1 then { throw b4 } else { throw b3 }
    } catch e when e is B4 { }
  }
};

procedure parameterEscape(h: H, c: C, b4: B4, k: int)
  requires h#b is B4
  opaque
{
  var a2: A2 := new A2;
  try {
    try {
      try { throw 42 } catch n { };
      if k == 0 then { try { throw c } finally { } }
      else { if k == 1 then { throw b4 } else { throw h#b } }
    } catch e when e is B4 { throw c };
    if k == 5 then { throw a2 }
  } catch e { assert e is A }
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

-- A read at the arm type (`c as MyEx`), as a front end emits it, reads the arm's fields.
#eval testLaurelExecution {} <|
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

-- So does the binding without the cast: the clause sees it at what its guard admits, the
-- arm type, or for a multi-catch its alternatives' join (`Mid`).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite RtEx {}
composite Mid extends RtEx { var code: int }
composite MyEx extends Mid {}
composite OtEx extends Mid {}
composite ArEx extends RtEx {}
procedure readUncast() entry opaque modifies * {
  var r: int := 0;
  var b: int := 1;
  try {
    if b == 0 then { var a: ArEx := new ArEx; throw a };
    var m: MyEx := new MyEx;
    m#code := 5;
    throw m
  } catch c when c is MyEx {
    var n: MyEx := c;
    r := n#code
  };
  assert r == 5
};
procedure readMultiCatch() entry opaque modifies * {
  var r: int := 0;
  var b: int := 1;
  try {
    if b == 0 then { var a: ArEx := new ArEx; throw a };
    var m: MyEx := new MyEx;
    m#code := 5;
    throw m
  } catch c when c is MyEx || c is OtEx {
    r := c#code
  };
  assert r == 5
};
procedure rethrowMultiCatchRun() entry opaque modifies * {
  var r: int := 0;
  var b: int := 1;
  try {
    try {
      if b == 0 then { var a: ArEx := new ArEx; throw a };
      var m: MyEx := new MyEx;
      m#code := 1;
      throw m
    } catch c when c is MyEx || c is OtEx { throw c } catch c2 { r := 2 }
  } catch d { r := d#code };
  assert r == 1
};
#end

-- A multi-catch arm rethrows its binding at the alternatives' join (`Mid`), which the
-- enclosing handler reads uncast.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top {}
composite Mid extends Top { var code: int }
composite A extends Mid {}
composite B extends Mid {}
composite C extends Top {}
procedure rethrowMultiCatch(k: int) returns (r: int)
  opaque
  ensures k > 0 ==> r == 1
{
  r := 0;
  try {
    try { if k > 0 then { var a: A := new A; a#code := 1; throw a } else { throw new C } }
    catch c when c is A || c is B { throw c } catch c2 { r := 2 }
  } catch d { r := d#code }
};
procedure rethrowMultiCatchWrong(k: int) returns (r: int)
  opaque
  ensures k > 0 ==> r == 2
//        ^^^^^^^^^^^^^^^^ error: postcondition does not hold
{
  r := 0;
  try {
    try { if k > 0 then { var a: A := new A; a#code := 1; throw a } else { throw new C } }
    catch c when c is A || c is B { throw c } catch c2 { r := 2 }
  } catch d { r := d#code }
};
#end

-- A guard that names an alternative through an alias narrows the binding as one naming the
-- target does, to `Mid`: reading `code` would fail at the `try`'s join `Top`, testing for `B`
-- at `A`, and testing for `AE` at `B`.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top {}
composite Mid extends Top { var code: int }
composite A extends Mid {}
composite B extends Mid {}
composite C extends Top {}
type AE = A
procedure aliasMultiCatch(k: int) returns (r: int)
  opaque
  ensures k > 0 ==> r == 4
  ensures k < 0 ==> r == 1
{
  r := 0;
  try {
    if k > 0 then { var a: A := new A; a#code := 4; throw a }
    else { if k < 0 then { throw new B } else { throw new C } }
  } catch c when c is AE || c is B {
    if c is AE then { r := c#code } else { if c is B then { r := 1 } }
  } catch c2 { r := 3 }
};
#end

-- Narrowing to `A` keeps a cast to `B` that a `D extends A, B` makes possible.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Base {}
composite A extends Base {}
composite B extends Base { var code: int }
composite D extends A, B {}
composite C extends Base {}
procedure castToCommonDescendantParent(k: int) returns (r: int)
  opaque
  ensures k > 0 ==> r == 3
{
  r := 0;
  try {
    if k > 0 then { var d: D := new D; d#code := 3; throw d } else { throw new C }
  } catch c when c is A {
    if c is D then { var b: B := c as B; r := b#code }
  } catch c2 { r := 2 }
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
