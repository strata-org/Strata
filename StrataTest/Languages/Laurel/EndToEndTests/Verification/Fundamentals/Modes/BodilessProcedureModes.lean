/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Condition modes on a *bodiless* procedure (an `opaque` declaration with no
implementation).

A bodiless procedure has no body in which to check anything, so its
postconditions are trusted: callers assume them. Two consequences the tests
below pin:

  - a plain or `free` `ensures` is *assumed* at call sites (the declaration is
    trusted), so a caller can rely on it;

  - a `checked ensures` is NOT assumed at call sites. `checked` means "assert,
    never assume", but there is no body to assert it against, so the contract
    pass drops it entirely. Previously it was silently downgraded to a free
    (assumed) postcondition, inverting its meaning: `checked ensures false` on a
    bodiless procedure would then let any caller assume `false` — a soundness
    hole. Now a caller cannot rely on it.

Preconditions are unaffected by bodilessness: a precondition is asserted at the
call site (which always exists) and only *assumed* in the body, so a missing
body never turns an assert into an unchecked assume.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `checked ensures` on a bodiless procedure is not assumed at callers

This is the regression test for the soundness hole. A bodiless `opaque`
procedure has no body against which to check a `checked` (assert-only)
postcondition, so the contract pass drops it: it is neither checked (no body)
nor assumed at call sites (assert-only postconditions are never assumed). The
key soundness property is that a caller does NOT get to assume it. -/

/-! `checked ensures false` on a bodiless procedure must NOT be assumed by
    callers. Previously it was silently downgraded to a free (assumed)
    postcondition, so the caller's `assert false` verified — any caller could
    prove anything. Now the clause is dropped, so `assert false` at the call
    site is (correctly) unprovable. -/
#eval testLaurel <|
#strata
program Laurel;
procedure bad() returns (r: int)
  opaque
  checked ensures false
;
procedure callerOfBad() returns (r: int)
  opaque
{
  r := bad();
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Bodiless postconditions that ARE trusted still work

A bodiless procedure's plain and `free` postconditions are assumed at call
sites, so callers can rely on them. -/

/-! A plain `ensures` on a bodiless procedure is assumed at the call site. -/
#eval testLaurel <|
#strata
program Laurel;
procedure bodilessPlain(x: int) returns (r: int)
  opaque
  ensures r > x
;
procedure usesBodilessPlain()
  opaque
{
  var v: int := bodilessPlain(3);
  assert v > 3
};
#end

/-! A `free ensures` on a bodiless procedure is likewise assumed at the call
    site (this is the `free := true` behavior the mode replaced). -/
#eval testLaurel <|
#strata
program Laurel;
procedure bodilessFree(x: int) returns (r: int)
  opaque
  free ensures r > x
;
procedure usesBodilessFree()
  opaque
{
  var v: int := bodilessFree(3);
  assert v > 3
};
#end

/-! ## Preconditions on a bodiless procedure are unaffected

A precondition is asserted at the (always-present) call site, so bodilessness
does not weaken it: a violated `checked requires` still fails at the caller. -/

/-! A `checked requires` on a bodiless procedure is still asserted at callers. -/
#eval testLaurel <|
#strata
program Laurel;
procedure bodilessNeedsPositive(x: int) returns (r: int)
  checked requires x > 0
  opaque
;
procedure callsBodilessNeg()
  opaque
{
  var y: int := bodilessNeedsPositive(-1)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end
