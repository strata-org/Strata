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
extension E4). Laurel *records* these and resolves/type-checks them — the
`throws` type must be a subtype of the channel root `BaseException`, and each
`onThrow` predicate is checked at `bool` with its binding typed `BaseException`.
Laurel performs no declare-or-catch enforcement (that is front-end policy), and
the contract is not yet consumed by lowering (E7), so a well-formed contract
verifies cleanly (it is ignored during translation).
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
