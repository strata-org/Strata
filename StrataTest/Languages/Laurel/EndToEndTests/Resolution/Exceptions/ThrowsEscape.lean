/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Catch-or-declare enforcement — the "check, don't trust" half of the exceptional
contract. Clause typing is `ThrowsContractTyping.lean`; the same analysis applied to
instance methods is `ThrowsEscapeMethods.lean`.

The rule has two directions, and both are checked on the program as authored, during
resolution:
  * a procedure that declares no `throws` may not let any exception escape, whether
    thrown directly or propagated from a callee;
  * a procedure that declares `throws T` may only let subtypes of `T` escape, so `T`
    is an upper bound rather than an exact type — which is how a Java
    `throws Exception` covering a more specific throw is represented.

Catching discharges the obligation: a `throw` inside a `try` whose `catch` handles
the type needs no declaration. Java-style declare-or-catch *at call sites* remains
front-end policy.
-/

/-! ## Enforcement: no-escape and the throws upper-bound -/

-- Upper-bound violation: declares `throws ArithError` but throws a sibling
-- `ParseError`, which is not a subtype of the declared type.
#eval testLaurel <|
#strata
program Laurel;
composite ArithError {}
composite ParseError {}
procedure wrongThrows()
  throws (e: ArithError)
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
composite Exception {}
procedure thrower()
  returns (r: int)
  throws (e: Exception)
  opaque
{
  var e: Exception := new Exception;
  throw e
};
procedure callsThrower()
  returns (r: int)
  opaque
{
  r := thrower()
//     ^^^^^^^^^ error: procedure 'callsThrower' may let an exception of type 'Exception' escape; catch it with a `try`/`catch` or declare a `throws` clause
};
#end

-- Allowed: the declared `throws` type is a supertype of what is thrown, so the
-- coarsened contract holds (this is how a Java `throws Exception` covering a
-- more specific throw is represented).
#eval testLaurel <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
procedure coarsenedThrows()
  throws (e: Exception)
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
composite ParseError {}
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
