/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exercises the E4 procedure exceptional contract: an optional `throws` type and
`onThrow` exceptional postconditions (see `docs/design/laurel_extensions.md`,
extension E4). The `throws` type must be a subtype of the channel root
`BaseException`, and each `onThrow` predicate is checked at `bool` with its
binding typed `BaseException`.

E4 enforcement (the "check, don't trust" analysis): a procedure may only let an
exception escape whose type is a subtype of its declared `throws` type, and a
procedure that declares no `throws` may not let any exception escape (whether
thrown directly or propagated from a callee). Java-style declare-or-catch at
call sites remains front-end policy.
-/

-- Valid: `throws` a BaseException subtype. Recorded and ignored at translation,
-- so the procedure verifies with no diagnostics.
#eval testLaurel <|
#strata
program Laurel;

composite ArithError extends BaseException {}

procedure mightThrow()
  throws ArithError
  opaque
{
  assert true
};
#end

-- Valid: an `onThrow` exceptional postcondition with a boolean predicate.
#eval testLaurel <|
#strata
program Laurel;

composite ArithError extends BaseException {}

procedure mightThrow2()
  throws ArithError
  onThrow (e) true
  opaque
{
  assert true
};
#end

-- Ill-typed: the `throws` type is not a subtype of BaseException.
#eval testLaurel <|
#strata
program Laurel;

procedure badThrows()
  throws int
//       ^^^ error: throws type must be a subtype of 'BaseException'
  opaque
{
  assert true
};
#end

-- Ill-typed: the `onThrow` predicate is an int, not a bool.
#eval testLaurel <|
#strata
program Laurel;

procedure badOnThrow()
  onThrow (e) 5
//            ^ error: expected 'bool', got 'int'
  opaque
{
  assert true
};
#end

/-! ## E4 enforcement: no-escape and the throws upper-bound -/

-- Upper-bound violation: declares `throws ArithError` but throws a sibling
-- `ParseError`, which is not a subtype of the declared type.
#eval testLaurel <|
#strata
program Laurel;
composite ArithError extends BaseException {}
composite ParseError extends BaseException {}
procedure wrongThrows()
  throws ArithError
  opaque
{
  var e: ParseError := new ParseError;
  throw e
//^^^^^^^ error: procedure 'wrongThrows' may throw 'ParseError', which is not a subtype of its declared `throws` type 'ArithError'
};
#end

-- No-escape via a propagated call: `callsThrower` invokes a throwing procedure
-- without catching it and without declaring `throws` itself.
#eval testLaurel <|
#strata
program Laurel;
procedure thrower()
  returns (r: int)
  throws BaseException
  opaque
{
  var e: BaseException := new BaseException;
  throw e
};
procedure callsThrower()
  returns (r: int)
  opaque
{
  r := thrower()
//     ^^^^^^^^^ error: procedure 'callsThrower' may let an exception of type 'BaseException' escape; catch it with a `try`/`catch` or declare a `throws` clause
};
#end

-- Allowed: the declared `throws` type is a supertype of what is thrown, so the
-- coarsened contract holds (this is how a Java `throws Exception` covering a
-- more specific throw is represented).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
procedure coarsenedThrows()
  throws BaseException
  opaque
{
  var e: ParseError := new ParseError;
  throw e
};
#end

-- Allowed (no-escape via catch): `handled` throws inside a `try` whose `catch`
-- handles the thrown type, so nothing escapes and no `throws` declaration is
-- required. Must produce no diagnostics.
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
procedure handled()
  returns (r: int)
  opaque
{
  var e: ParseError := new ParseError;
  try {
    throw e
  } catch c when c is ParseError {
    r := -1
  };
  r := 0
};
#end

-- A throwing procedure lowers to a single `Result<Val, Composite>` output, so it
-- can carry at most one value output. A `throws` procedure with two value
-- outputs is rejected loudly (rather than silently degrading the `Result`
-- payload to a placeholder).
#eval testLaurel <|
#strata
program Laurel;
composite E extends BaseException {}
procedure twoOut()
//        ^^^^^^ not-yet-implemented: at most one value output
  returns (a: int, b: int)
  throws E
  opaque
{
  a := 1;
  b := 2
};
#end
