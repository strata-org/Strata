/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exercises the E2 `throw` statement (see `docs/design/laurel_extensions.md`,
extension E2). `throw`'s operand is typed at the prelude root `BaseException`
(E1); any declared subtype is accepted.

E7 lowering: a `throw` in a procedure that declares `throws` lowers to a
`Result<Val, Composite>`-returning Core procedure — an in-flight exception sets
the synthesized `$thrown`/`$exc` locals and exits, and the procedure's result is
constructed as `Bad(exc)`. A `throw` whose exception would escape a procedure
that does *not* declare `throws` is the E4 no-escape case, now rejected during
resolution (E4 enforcement).
-/

-- Ill-typed: the operand is an `int`, not a `BaseException`. The type error is
-- reported during resolution, so the pipeline never reaches translation.
#eval testLaurel <|
#strata
program Laurel;

procedure throwsNonException()
  opaque
{
  throw 5
//      ^ error: expected 'BaseException', got 'int'
};
#end

-- Well-typed and declared `throws`: lowers to a `Result`-returning procedure
-- (E7) and verifies — there are no proof obligations to discharge.
#eval testLaurel <|
#strata
program Laurel;

procedure throwsException()
  throws BaseException
  opaque
{
  var e: BaseException := new BaseException;
  throw e
};
#end

-- E4 no-escape enforcement: a `throw` whose exception would escape a procedure
-- that does not declare `throws` is rejected during resolution.
#eval testLaurel <|
#strata
program Laurel;

procedure throwsWithoutDeclaring()
  opaque
{
  var e: BaseException := new BaseException;
  throw e
//^^^^^^^ error: procedure 'throwsWithoutDeclaring' may let an exception of type 'BaseException' escape; catch it with a `try`/`catch` or declare a `throws` clause
};
#end
