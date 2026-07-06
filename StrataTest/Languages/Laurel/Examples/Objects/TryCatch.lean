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

`try`/`catch`/`finally` now lowers to Core (E7): the body runs in a labeled
block, a `throw` exits to it, a first-match-wins chain of guarded handlers runs
after it, and `finally` runs on the fall-through edge. These well-typed cases
lower and verify; the negative case is rejected during resolution.
-/

-- Well-typed try / catch / finally: parses, resolves, type-checks, lowers, and
-- verifies (the bodies have no proof obligations that fail).
#eval testLaurel <|
#strata
program Laurel;

procedure tryCatchFinally()
  opaque
{
  try {
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
