/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
A `catch` binding that resolution cannot type is typed `Unknown`, and
`EliminateExceptions.lowerTry` reads an `Unknown` binding as "this handler can
never fire" and DISCARDS the clause, with only a `.warning`. So each shape of
thrown value has to type the binding: the failing `assert` inside each handler is
the evidence that the clause was kept.

A `try` whose body throws nothing keeps the plain `.warning`. Pinned by the
`badGuard` block in `CatchGuardTyping.lean`, whose body is just `assert true`.
-/

-- (1a) `throw f()` is typed from `f`'s single output, so the handler survives and the
-- caught value is the thrown one. The failing `assert` is what shows the clause is
-- still in the program: a discarded one takes its obligations with it.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure f() returns (q: int) opaque { return 7 };
procedure throwsCallResult() returns (r: int) opaque
{
  try {
    throw f()
  } catch c {
    assert c == 8
//  ^^^^^^^^^^^^^ error: assertion does not hold
  };
  r := 0
};
#end

-- (1b) An unannotated local is typed from its initializer, so `var e := 7; throw e`
-- reaches the binding too. No warning: the body's thrown type is determined.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure throwsInferredLocal() returns (r: int) opaque
{
  try {
    var e := 7;
    throw e
  } catch c {
    assert c == 8
//  ^^^^^^^^^^^^^ error: assertion does not hold
  };
  r := 0
};
#end

-- (2) A `throw` of a field read is typed from the field.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Box { var v: int }
procedure throwsFieldRead(b: Box) returns (r: int) opaque
{
  try {
    throw b#v
  } catch c {
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
  };
  r := 0
};
#end

-- (3) A body that throws only a value of unknown type does throw, so discarding its handler
-- is an error: verified without it, `ensures out == 1` would hold, as the declared `throws`
-- lets the exception escape.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Err {}
procedure throwsHole(k: bool) returns (out: int) throws (e: Err) opaque ensures out == 1 {
  out := 1;
  try {
//^ error: the `catch` binding of this `try` cannot be typed: the body throws a value of unknown type
    if k then { throw <?> }
  } catch c {
    out := 2
  }
};
#end
