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

/-! P3: diamond RESOLVED by an override on D itself — most-specific is D.
    D3.m must REFINE both parents' contracts (Liskov); its `r == 3` refines the
    weaker `r >= 0` on both L3.m and R3.m, so the override is accepted. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite L3 {
  procedure m(self: L3) returns (r: int)
    opaque ensures r >= 0 { return 1 };
}
composite R3 {
  procedure m(self: R3) returns (r: int)
    opaque ensures r >= 0 { return 2 };
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
    A and B both declare m; B is more specific => B$m (r == 2). B4.m overrides A4.m
    and must REFINE it (Liskov): `r == 2` refines the weaker `r >= 0`. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A4 {
  procedure m(self: A4) returns (r: int)
    opaque ensures r >= 0 { return 1 };
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
-- Each declarer in the chain overrides the one above and must REFINE it (Liskov):
-- the two ancestors carry the weaker `r >= 0`, which `D3p.m`'s `r == 3` refines.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite D2p {
  procedure m(self: D2p) returns (r: int)
    opaque ensures r >= 0 { return 1 };
}
composite D1p extends D2p {
  procedure m(self: D1p) returns (r: int)
    opaque ensures r >= 0 { return 2 };
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

/-! ## P6: GENERIC inherited call — a method inherited (not redeclared) from a GENERIC parent,
    called on a generic subtype. The lifted `GBase$get<T>(self: GBase<T>)` must bind `T := int`
    from a `GSub<int>` receiver, which needs the ancestor remap in BOTH the subtype/coercion
    relation (`isSubtype`/`ancestorMatchesTarget`) AND monomorphization
    (`inferProcInst`/`liftActualToParamHead`). Before those, this raised an internal error
    ("expected 'GBase<T>', got 'GSub<int>'" then "'GBase$get' is not defined"). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite GBase<T> {
  procedure get(self: GBase<T>) returns (r: int)
    opaque ensures r == 0 { return 0 };
}
composite GSub<T> extends GBase<T> { }
procedure go(s: GSub<int>)
  opaque
{
  var x: int := s#get();
  assert x == 0
};
#end

/-! ## P7: the same inherited generic call must still be SOUND — a false assertion on its
    result fails (the read is real, not vacuous). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite GBase2<T> {
  procedure get(self: GBase2<T>) returns (r: int)
    opaque ensures r == 0 { return 0 };
}
composite GSub2<T> extends GBase2<T> { }
procedure go(s: GSub2<int>)
  opaque
{
  var x: int := s#get();
  assert x == 5
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## P8: type-arg-REORDERING remap. `RSub<A,B> extends RBase<B,A>`, and the inherited
    field-reading method reads `first: X` off `RBase<X,Y>`. Through `RSub<bool,int>` the
    substituted ancestor is `RBase<int,bool>`, so `first` is `int` — the remap must be
    order-EXACT (a non-substituting or mis-ordered walk would type `first` as `bool` and reject
    the `int` assignment). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite RBase<X, Y> {
  var first: X
  procedure getFirst(self: RBase<X, Y>) returns (r: X)
    opaque ensures r == self#first { r := self#first };
}
composite RSub<A, B> extends RBase<B, A> { }
procedure go()
  opaque
{
  var s: RSub<bool, int> := new RSub<bool, int>;
  s#first := 9;
  var g: int := s#getFirst();
  assert g == 9
};
#end

/-! ## P9: inherited generic-parent method through a NON-GENERIC hop. `Mid` (concrete) sits
    between the receiver and the generic declaring parent (`Sub extends Mid extends GBase<int>`).
    The ancestor walk must traverse the concrete hop to reach `GBase<int>` and bind the method's
    `self: GBase<T>` at `T := int`. Uses the shared `substitutedAncestors` (over ALL composites)
    rather than a generics-only walk, which would drop `Mid` and fail to monomorphize. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite GBase3<T> {
  procedure get(self: GBase3<T>) returns (r: int)
    opaque ensures r == 0 { return 0 };
}
composite Mid3 extends GBase3<int> { }
composite Sub3 extends Mid3 { }
procedure go()
  opaque
{
  var s: Sub3 := new Sub3;
  var x: int := s#get();
  assert x == 0
};
#end

/-! ## P10: a CONCRETE composite extending a generic INSTANTIATION (`IntBox extends GBase4<int>`),
    calling the inherited method. Same remap as P9 with the concrete child directly on the generic
    parent. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite GBase4<T> {
  procedure get(self: GBase4<T>) returns (r: int)
    opaque ensures r == 0 { return 0 };
}
composite IntBox4 extends GBase4<int> { }
procedure go()
  opaque
{
  var b: IntBox4 := new IntBox4;
  var x: int := b#get();
  assert x == 0
};
#end
