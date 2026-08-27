/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
open StrataTest.Util
open Strata

/-! P1: inherited METHOD, parent declared AFTER child (order independence). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ChildP extends ParentP { }
composite ParentP {
  procedure m(self: ParentP) returns (r: int)
    opaque
    ensures r == 4
  {
    return 4
  };
}
procedure go(c: ChildP)
  opaque
{
  var x: int := c#m();
  assert x == 4
};
#end

/-! P2: DIAMOND ambiguity — D extends L, R; BOTH declare m, D does not.
    No most-specific declarer => rejected (not a silent pick). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite L2 {
  procedure m(self: L2) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite R2 {
  procedure m(self: R2) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite D2 extends L2, R2 { }
procedure go(d: D2)
  opaque
{
  var x: int := d#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'D2' inherits it from the unrelated types L2, R2
  assert x == 1
};
#end

/-! P3: diamond RESOLVED by an override on D itself — most-specific is D. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite L3 {
  procedure m(self: L3) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite R3 {
  procedure m(self: R3) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite D3 extends L3, R3 {
  procedure m(self: D3) returns (r: int)
    opaque ensures r == 3 { return 3 };
}
procedure go(d: D3)
  opaque
{
  var x: int := d#m();
  assert x == 3
};
#end

/-! P4: depth — most-specific wins along a single chain. C extends B, B extends A;
    A and B both declare m; B is more specific => B$m (r == 2). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A4 {
  procedure m(self: A4) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite B4 extends A4 {
  procedure m(self: B4) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite C4 extends B4 { }
procedure go(c: C4)
  opaque
{
  var x: int := c#m();
  assert x == 2
};
#end

/-! P5: most-specific wins along a chain of THREE declarers, and through a type reachable
    by two paths of different length.

    P4 above has two declarers, which any "compare a pair" rule also gets right. Here
    three declare `m` and `D3p` is reachable from `Rp` both directly and via `D1p`, so a
    rule that stopped after some prefix of the candidates, or that let a redundant edge
    forge a second entry for one declarer, would bind a different contract; `assert x == 3`
    names the winner, so a wrong pick changes an observable value rather than only a
    message.

    NOT pinned here: that `mostSpecific` quantifies over EVERY candidate rather than a
    prefix. `HashSet` order happens to put the winner first, so no fixture distinguishes
    the two; that wants a property test over candidate permutations. Measurements are in
    the commit message. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite D2p {
  procedure m(self: D2p) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite D1p extends D2p {
  procedure m(self: D1p) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite D3p extends D1p {
  procedure m(self: D3p) returns (r: int)
    opaque ensures r == 3 { return 3 };
}
composite Rp extends D1p, D3p { }
procedure go(r: Rp)
  opaque
{
  var x: int := r#m();
  assert x == 3
};
#end
