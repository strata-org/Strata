/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # An UNCALLED polymorphic procedure over a generic composite

A procedure whose `T` appears in a generic composite is checked by cloning it per call-site
instantiation. With ZERO call sites there is nothing to clone, so the procedure would be
dropped at emission and its contract would go unchecked — and silently, since a dropped
procedure produces no diagnostic.

So an uncalled one is cloned at a synthetic WITNESS: a fresh opaque zero-field composite, one
per type variable. That choice has to satisfy two opposite requirements, and the cases here are
organised around them.

It must be uninterpreted enough to be sound. If the witness sort were a SINGLETON, then any two
values of it would be equal, and a contract like `ensures a#val == b#val` — false in general,
since two boxes hold independent values — would hold vacuously and mask the bug. The
`witnessIsNotASingleton` case is what rules that out: it must FAIL.

And it must not invent obligations. A witness that imposed anything of its own would make TRUE
contracts fail, so `uncalledTrueContract` is the control.

Beyond that: the witness is emitted iff the procedure is uncalled (mixing a called and an
uncalled procedure yields exactly one failure, not two), and distinct uncalled procedures get
distinct obligations rather than being merged.
-/

/-! ## A false contract on an uncalled procedure fails at the witness -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure bad<T>(b: Box<T>) returns (r: int)
  opaque
  ensures r == 0
//        ^^^^^^ error: postcondition does not hold
{ r := 1 };
procedure main() opaque { assert 1 == 1 };
#end

-- CONTROL: a TRUE contract on an uncalled procedure must still verify. Without this, a witness
-- that imposed an obligation of its own would look correct.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure good<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 0 };
procedure main() opaque { assert 1 == 1 };
#end

-- The body reads a FRESH box rather than the parameter, so `ensures r == b#val` is false. Pins
-- that the witness's FIELDS are uninterpreted too, not just its type.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure rd<T>(b: Box<T>) returns (r: T)
  opaque
  ensures r == b#val
//        ^^^^^^^^^^ error: postcondition does not hold
{ var t: Box<T> := new Box<T>; r := t#val };
procedure main() opaque { assert 1 == 1 };
#end

/-! ## The witness sort is NOT a singleton

`ensures a#val == b#val` is false in general: `a` and `b` are independent boxes. It can only be
proved if the witness sort has at most one inhabitant — so this case FAILING is the evidence
that the witness has arbitrary cardinality, i.e. that it is a faithful stand-in for a type
variable rather than a degenerate one. If this ever starts verifying, every other witness case
in this file has become vacuous. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure f<T>(a: Box<T>, b: Box<T>) returns (r: int)
  opaque
  ensures a#val == b#val
//        ^^^^^^^^^^^^^^ error: postcondition does not hold
{ r := 0 };
procedure main() opaque { assert 1 == 1 };
#end

/-! ## A witness is emitted exactly for the uncalled procedures

`used` has a real call site, so it is cloned at `int` and gets no witness. `unused` has none,
so it is checked at the witness and its false contract fails. Exactly one failure: if a witness
were also emitted for `used`, its contract is true so nothing would change — but if witnesses
were emitted for NEITHER, this would pass, and if the called procedure's real clone were
skipped in favour of a witness, the caller's `assert got == 7` would stop being provable. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure used<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure unused<T>(b: Box<T>) returns (r: int)
  opaque
  ensures r == 5
//        ^^^^^^ error: postcondition does not hold
{ r := 6 };

procedure callsOnlyUsed()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := used(bx);
  assert got == 7
};
#end

/-! ## Distinct uncalled procedures get distinct obligations

Three uncalled procedures with three different false postconditions must yield three failures.
The obligations are keyed by source location, so a keying bug would merge them and the count
would silently drop — which is why all three are annotated rather than just one. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure b1<T>(b: Box<T>) returns (r: int)
  opaque
  ensures r == 1
//        ^^^^^^ error: postcondition does not hold
{ r := 0 };
procedure b2<T>(b: Box<T>) returns (r: int)
  opaque
  ensures r == 2
//        ^^^^^^ error: postcondition does not hold
{ r := 0 };
procedure b3<T>(b: Box<T>) returns (r: int)
  opaque
  ensures r == 3
//        ^^^^^^ error: postcondition does not hold
{ r := 0 };
procedure main() opaque { assert 1 == 1 };
#end
