/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
End-to-end verification tests for the three condition modes selected by the
`free` and `checked` clause keywords, run through the *full* pipeline (translate
+ resolve + verify) rather than only inspecting the lowered text (that is
`Idiomaticity/ContractPassConditionModeTest.lean`).

Each mode has a distinct assert/assume behavior at each of a condition's two
natural sites:

  - plain `requires`/`ensures` (mode `Both`)     — asserted AND assumed;
  - `free    requires`/`ensures` (mode `Assume`)  — assumed only, never checked;
  - `checked requires`/`ensures` (mode `Assert`)  — checked only, never assumed.

For a precondition the natural assertion site is the call site and the natural
assumption site is the implementation body. For a postcondition the natural
assertion site is the end of the body and the natural assumption site is the
call site. The tests below pin, per mode, that a violated `checked`/plain clause
FAILS at its assertion site and that the same clause written `free` VERIFIES
(because it is never asserted), and that a `checked` clause is not silently
assumed at its assumption site.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Preconditions

A precondition is asserted at the call site and assumed in the body. -/

/-! A violated plain `requires` FAILS at the call site; the same clause written
    `free` VERIFIES because a free precondition is never asserted at callers. -/
#eval testLaurel <|
#strata
program Laurel;
procedure needsPositive(x: int) returns (r: int)
  requires x > 0
  opaque
{
  r := x
};
procedure freeNeedsPositive(x: int) returns (r: int)
  free requires x > 0
  opaque
{
  r := x
};
procedure callsRequires()
  opaque
{
  var bad: int := needsPositive(-1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  var good: int := needsPositive(1);
  // A `free requires` is assumed by the implementation but never checked at
  // the call site, so passing -1 verifies.
  var free: int := freeNeedsPositive(-1)
};
#end

/-! A `checked requires` is asserted at the call site but NOT assumed in the
    body (assert-only): the body cannot rely on it, so an in-body `assert` of the
    same fact fails. A plain `requires` IS assumed, so the same assert verifies. -/
#eval testLaurel <|
#strata
program Laurel;
procedure checkedReqNotAssumed(x: int) returns (r: int)
  checked requires x > 0
  opaque
{
  assert x > 0;
//^^^^^^^^^^^^ error: assertion does not hold
  r := x
};
procedure plainReqAssumed(x: int) returns (r: int)
  requires x > 0
  opaque
{
  assert x > 0;
  r := x
};
#end

/-! ## Postconditions (procedure with a body)

A postcondition is asserted at the end of the body and assumed at the call
site. -/

/-! A violated plain `ensures` FAILS at the end of the body; the same clause
    written `free` VERIFIES because a free postcondition is never checked. -/
#eval testLaurel <|
#strata
program Laurel;
procedure plainEnsuresViolated(x: int) returns (r: int)
  opaque
  ensures r > x
//        ^^^^^ error: postcondition does not hold
{
  r := x
};
procedure freeEnsuresViolated(x: int) returns (r: int)
  opaque
  free ensures r > x
{
  r := x
};
#end

/-! A `checked ensures` that holds VERIFIES; and it is asserted at the body but
    NOT assumed at the call site (assert-only), so a caller may not rely on it —
    an `assert` of the same fact after the call fails. -/
#eval testLaurel <|
#strata
program Laurel;
procedure checkedEnsuresCallee(x: int) returns (r: int)
  opaque
  checked ensures r > x
{
  r := x + 1
};
procedure usesCheckedEnsures()
  opaque
{
  var v: int := checkedEnsuresCallee(3);
  assert v > 3
//^^^^^^^^^^^^ error: assertion could not be proved
};
#end
