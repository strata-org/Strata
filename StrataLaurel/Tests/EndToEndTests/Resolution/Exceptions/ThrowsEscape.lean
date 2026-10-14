/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Declared-`throws` enforcement — the "check, don't trust" half of the exceptional
contract. Clause typing is `ThrowsContractTyping.lean`; the same analysis applied to
instance methods is `ThrowsEscapeMethods.lean`.

A procedure that declares `throws T` may only let subtypes of `T` escape, so `T` is
an upper bound rather than an exact type — which is how a Java `throws Exception`
covering a more specific throw is represented. This is checked on the program as
authored, during resolution. Catching discharges it: a `throw` inside a `try` whose
`catch` handles the type does not count as an escape.

A procedure that declares no `throws` is not checked here: an exception escaping it
is a verification obligation, asserted where it would escape (see
`Execution/Exceptions/UncaughtExceptions.lean`). Java-style declare-or-catch *at call
sites* remains front-end policy.
-/

/-! ## Enforcement: the throws upper-bound -/

-- Upper-bound violation: declares `throws ArithError` but throws a sibling
-- `ParseError`, which is not a subtype of the declared type.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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

-- No static error for a propagated call: `callsThrower` invokes a throwing
-- procedure without catching it and without declaring `throws` itself. The escape
-- is a verification obligation at the call instead, which fails here because the
-- callee always throws.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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
//     ^^^^^^^^^ error: call does not throw an uncaught 'Exception' could not be proved
};
#end

-- Allowed: the declared `throws` type is a supertype of what is thrown, so the
-- coarsened contract holds (this is how a Java `throws Exception` covering a
-- more specific throw is represented).
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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

-- Allowed (caught): `handled` throws a `ParseError`, outside its declared `throws`
-- type, inside a `try` whose `catch` handles it, so nothing outside `Other` escapes.
-- Must produce no diagnostics.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite ParseError {}
composite Other {}
procedure handled()
  returns (r: int)
  throws (e: Other)
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
