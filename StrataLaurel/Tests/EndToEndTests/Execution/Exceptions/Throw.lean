/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exercises the `throw` statement (see the Exceptions section of the Laurel User
Guide).
`throw`'s operand is not constrained to a built-in root: the thrown value is
reconciled at each enclosing `catch` binding or a `throwsOn` case, whose binding is typed at the
least common ancestor of the types that can reach it.

Lowering: a `throw` in a procedure that declares `throws` lowers to a
`Result<Val, Composite>`-returning Core procedure — an in-flight exception sets
the synthesized `$thrown`/`$exc` locals and exits, and the procedure's result is
constructed as `Bad(exc)`. A `throw` whose exception would escape a procedure
that does *not* declare `throws` is the no-escape case, rejected during the
resolution-time exception checks (see `validateExceptionEscapes` in `Resolution.lean`).

What may be thrown is also covered here, because it is a property of `throw`'s
operand rather than of any combination: a composite, and — since there is no built-in
root — a bare primitive. Each case pairs its throwing procedure with a caller
that catches, marked `entry`, so it runs under the verifier and both interpreters;
the no-escape rejection is a resolution error and stays verification-only.

Front-end *boxing* — wrapping an arbitrary value in a carrier composite so a single
`catch` can see values of unrelated kinds — is an idiom rather than a rule about
`throw`, so it lives in `UseCases/ThrowAnyValue.lean`.
-/

-- Well-typed and declared `throws`: lowers to a `Result`-returning procedure
-- and verifies — there are no proof obligations to discharge.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite Exception {}
procedure throwsException()
  throws (e: Exception)
  opaque
{
  var e: Exception := new Exception;
  throw e
};

procedure runAll() entry
  opaque
  modifies *
{
  try {
    throwsException()
  } catch e {
    assert true
  }
};
#end

-- No-escape enforcement: a `throw` whose exception would escape a procedure
-- that does not declare `throws` is rejected during resolution.
-- No interpreters: the annotated error is a resolution rejection, so there is no program to run.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;

composite Exception {}
procedure throwsWithoutDeclaring()
  opaque
{
  var e: Exception := new Exception;
  throw e
//^^^^^^^ error: procedure 'throwsWithoutDeclaring' may let an exception of type 'Exception' escape; catch it with a `try`/`catch` or declare a `throws` clause
};
#end

-- Throw a value of a declared subtype of the `throws` type. The procedure
-- declares `throws`, so this lowers to a `Result`-returning Core procedure
-- and verifies (no proof obligations).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
procedure throwsSubtype() throws (e: Exception) opaque {
  var e: ParseError := new ParseError;
  throw e
};

procedure runAll() entry
  opaque
  modifies *
{
  try {
    throwsSubtype()
  } catch e {
    assert true
  }
};
#end

/-! ### Unboxed primitives

Laurel imposes no root exception type, so a primitive is a legal `throws` type and a
legal `throw` operand. Both guides say so; these two cases are the evidence. Each pairs
its throwing procedure with a caller that catches, so it has a parameterless `entry` and
runs under the verifier and both interpreters. -/

-- `throws int` with a bare `throw 3`, caught by the caller.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure parsePositive(x: int) returns (r: int)
  throws (e: int)
  opaque
{
  if x < 0 then {
    throw 3
  };
  r := x
};
procedure catchesInt()
  returns (out: int) entry
  opaque
{
  out := 0;
  try {
    out := parsePositive(-1)
  } catch e {
    out := -1
  }
};
#end

-- The thrown primitive is observable in the handler, and a case's `ensures` can
-- constrain it by value rather than by type — there is no type test to make here,
-- which is the point: the binding is an `int`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure throwsCode(x: int) returns (r: int)
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
procedure readsCode()
  returns (out: int) entry
  opaque
{
  out := 0;
  try {
    out := throwsCode(-1)
  } catch e {
    assert e == 42;
    out := e
  }
};
#end

-- REGRESSION (dropped handler over a primitive `throws`). The two cases above are
-- not by themselves evidence that the handler RUNS: both observe the caught value
-- only from *inside* the handler, so if the handler is ever discarded their
-- observations go with it and they pass vacuously. That failure mode is live, not
-- hypothetical: `EliminateExceptions` deletes a `catch` clause whose binding is typed
-- `Unknown`, so any slip in the binding inference turns both of them green.
--
-- The claim is therefore moved OUT of the handler: the handler is the only code that
-- assigns `out`, so `ensures out == -7` holds only if the handler actually ran. Drop
-- the clause and `out` is never assigned, leaving the postcondition unprovable — a
-- diagnostic no annotation here expects, so this test fails rather than quietly
-- weakening. Note an `assert` placed *after* the `try` would NOT do: a discarded
-- handler leaves the exception in flight, which exits the procedure body and skips
-- every statement that follows it.
--
-- The contract sits on `catchesSeven` rather than on the `entry` procedure because an
-- `entry` procedure may not carry an `ensures` (it initializes its globals as locals
-- inside its body, which a contract cannot see). The `entry` caller re-states the
-- claim as an `assert` so the interpreter checks it too: verification pins that the
-- handler is *provably* reached, concrete execution pins that it actually is.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure throwsSeven(x: int) returns (r: int)
  throws (e: int)
  opaque
  throwsOn x < 0 {
    ensures e == 7
  }
{
  if x < 0 then {
    throw 7
  };
  r := x
};
procedure catchesSeven()
  returns (out: int)
  opaque
  ensures out == -7
{
  var n: int := 0;
  try {
    n := throwsSeven(-1)
  } catch c {
    n := 0 - c
  };
  out := n
};
procedure handlerRunsForPrimitiveThrows()
  returns (out: int) entry
  opaque
{
  out := catchesSeven();
  assert out == -7
};
#end
