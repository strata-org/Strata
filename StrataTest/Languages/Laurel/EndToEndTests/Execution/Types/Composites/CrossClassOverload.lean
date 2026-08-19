/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
open StrataTest.Util
open Strata

/-! Argument-blindness hazard in `#`-call resolution, recorded at the Laurel level:
    `obj#m` resolves by NAME to the most-specific DECLARER, ignoring argument types.
    When an overload SET spans an inheritance chain -- `BaseX.val(BB)` and
    `SubX.val(AA)`, neither overriding the other -- the nearest declarer need not be
    the overload a frontend's own (signature-aware) resolution chose, so the call
    binds a different contract.

    Not bug reports against `resolveInheritedMember`: given a name-keyed lookup,
    most-specific-declarer is the right rule and what every single-signature case
    wants. These pin the ARGUMENT-BLINDNESS as current behaviour, so a future move to
    signature-based resolution must change these expectations deliberately.

    A frontend emitting `#`-calls must therefore refuse such a call or resolve it
    itself; jverify refuses, in `refuseIfOverloadedAcrossAncestry`. -/

/-! C1: the nearest declarer wins even though the ARGUMENT fits the farther overload
    exactly. `b : BB` matches `BaseX.val(BB)` exactly, yet the call binds
    `SubX.val(AA)` (nearest declarer) and its `r == 42`. Asserting the value only
    that contract justifies records which one bound: with the argument-matching
    overload, `r` would be 0 and this fails. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite AA { }
composite BB extends AA { }
composite BaseX {
  procedure val(self: BaseX, b: BB) returns (r: int)
    opaque ensures r == 0 { return 0 };
}
composite SubX extends BaseX {
  procedure val(self: SubX, a: AA) returns (r: int)
    opaque ensures r == 42 { return 42 };
}
procedure c1(s: SubX, b: BB)
  opaque
{
  var v: int := s#val(b);
  assert v == 42
};
#end

/-! C2: the same blindness as a TYPE ERROR rather than a wrong contract. `SubZ`'s
    overload takes an unrelated `Str3`, so once the nearest declarer is selected the
    argument cannot check against it -- selection ran before, and independently of,
    argument checking. A signature-aware rule would have picked `BaseZ.val(BB3)` and
    verified. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite AA3 { }
composite BB3 extends AA3 { }
composite Str3 { }
composite BaseZ {
  procedure val(self: BaseZ, b: BB3) returns (r: int)
    opaque ensures r == 0 { return 0 };
}
composite SubZ extends BaseZ {
  procedure val(self: SubZ, x: Str3) returns (r: int)
    opaque ensures r == 42 { return 42 };
}
procedure c2(s: SubZ, b: BB3)
  opaque
{
  var v: int := s#val(b);
//                    ^ error: expected 'Str3', got 'BB3'
  assert v == 0
};
#end

/-! C3: CONTROL -- the same shape with the overloads' owners swapped, so the nearest
    declarer IS the argument-matching one. Verifies cleanly, confirming C1/C2 are
    about argument-blindness in selection, not inherited calls being broken
    generally. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite AA4 { }
composite BB4 extends AA4 { }
composite BaseW {
  procedure val(self: BaseW, a: AA4) returns (r: int)
    opaque ensures r == 7 { return 7 };
}
composite SubW extends BaseW {
  procedure val(self: SubW, b: BB4) returns (r: int)
    opaque ensures r == 9 { return 9 };
}
procedure c3(s: SubW, b: BB4)
  opaque
{
  var v: int := s#val(b);
  assert v == 9
};
#end
