/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

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
root — a bare primitive. The primitive section at the end allocates nothing, so it
runs under `testLaurelExecution { skipCoreInterpreter := false }`, i.e. verifier *and*
interpreter. The composite cases above it put their exception value on the heap, which
the interpret path does not support yet, so those stay verification-only
(`testLaurelExecution` with the default paths). The other file that runs both ways is
`TryCatchThrow.lean`, whose smoke cases throw nothing at all.

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
#end

-- No-escape enforcement: a `throw` whose exception would escape a procedure
-- that does not declare `throws` is rejected during resolution.
#eval testLaurelExecution {} <|
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
#end

/-! ### Unboxed primitives

Laurel imposes no root exception type, so a primitive is a legal `throws` type and a
legal `throw` operand. Both guides say so; these two cases are the evidence. Nothing is
allocated here, so unlike the rest of the file these two run under `testLaurelExecution`
— verifier *and* interpreter. That is also why the callers take no arguments and pass a
literal: `testLaurelExecution` needs an `entry` procedure for the interpreter to invoke,
and an entry point is called with none. -/

-- `throws int` with a bare `throw 3`, caught by the caller.
#eval testLaurelExecution { skipCoreInterpreter := false } <|
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
#eval testLaurelExecution { skipCoreInterpreter := false } <|
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
