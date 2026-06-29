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

Full lowering to Core targets a generic `Result<Val, Err>` (E7), which Laurel
cannot express until it gains generic datatypes, so a well-typed `throw`
currently reaches translation and reports `not-yet-implemented` there. These
tests pin down the front half of the pipeline: parsing, resolution, and the
`BaseException` type rule.
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

-- Well-typed: the operand is a `BaseException`. Parsing, resolution, and the
-- `BaseException` type rule all succeed; only the Core lowering is missing (E7).
#eval testLaurel <|
#strata
program Laurel;

procedure throwsException()
  opaque
{
  var e: BaseException := new BaseException;
  throw e
//^^^^^^^ not-yet-implemented: throw is not yet supported (requires generic Result lowering, E7)
};
#end
