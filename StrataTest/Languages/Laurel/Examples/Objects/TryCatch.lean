/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exercises the E3/E5 structured handler: `try` / predicate-based `catch` /
`finally` (see `docs/design/laurel_extensions.md`, extensions E3 and E5). A
`catch` binds the caught value (typed at the channel root `BaseException`, E1)
and may carry a `when` guard (checked at `bool`).

Like `throw` (E2), full lowering to Core targets a generic `Result<Val, Err>`
(E7), which Laurel cannot express until it gains generic datatypes. So a
well-typed `try` reaches translation and reports `not-yet-implemented` there.
These tests pin down the front half: parsing, resolution, catch-binding
scoping, and guard type-checking.
-/

-- Well-typed try / catch / finally: parses, resolves, type-checks; only the
-- Core lowering is missing (E7).
#eval testLaurel <|
#strata
program Laurel;

procedure tryCatchFinally()
  opaque
{
  try {
//^ not-yet-implemented: try/catch is not yet supported (requires generic Result lowering, E7)
    assert true
  } catch e {
    assert true
  } finally {
    assert true
  }
};
#end

-- Well-typed catch with a boolean `when` guard.
#eval testLaurel <|
#strata
program Laurel;

procedure tryWithGuard()
  opaque
{
  try {
//^ not-yet-implemented: try/catch is not yet supported (requires generic Result lowering, E7)
    assert true
  } catch e when true {
    assert true
  }
};
#end

-- Ill-typed: the `when` guard is an int, not a bool. Reported during
-- resolution, so the pipeline never reaches translation.
#eval testLaurel <|
#strata
program Laurel;

procedure badGuard()
  opaque
{
  try {
    assert true
  } catch e when 5 {
//               ^ error: expected 'bool', got 'int'
    assert true
  }
};
#end
