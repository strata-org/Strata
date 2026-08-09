/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
open StrataTest.Util
open Strata

/-! D1: SHARED-BASE diamond. D extends L,R; both extend A; ONLY A declares m.
    One declaration reached by two paths => resolves to A.m (NOT ambiguous). -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A1 {
  procedure m(self: A1) returns (r: int)
    opaque ensures r == 7 { return 7 };
}
composite L1 extends A1 { }
composite R1 extends A1 { }
composite D1 extends L1, R1 { }
procedure go(d: D1)
  opaque
{
  var x: int := d#m();
  assert x == 7
};
#end

/-! D2: ASYMMETRIC. C extends L,R; L extends A (A declares m); R ALSO declares m.
    R (dist 1) and A (dist 2) are incomparable => ambiguity ERROR.
    A naive nearest-BFS would silently pick R here; dominance must reject. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A2 {
  procedure m(self: A2) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite L2b extends A2 { }
composite R2b {
  procedure m(self: R2b) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite C2b extends L2b, R2b { }
procedure go(c: C2b)
  opaque
{
  var x: int := c#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'C2b' inherits it from the unrelated types A2, R2b
  assert x == 1
};
#end

/-! D3 (INTERACTION with the v5 Object-supertype edge): every composite extends a
    shared empty root (as jverify emits java.lang.Object). The
    dedup-by-declarer-identity in resolveInheritedMember must keep that shared base
    from collapsing a genuine diamond into a false winner: P and Q both extend Root
    and declare m; Z extends P, Q. Despite the common Root, {P, Q} are distinct
    incomparable declarers => ambiguous. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Root { }
composite P3 extends Root {
  procedure m(self: P3) returns (r: int) opaque ensures r == 1 { return 1 };
}
composite Q3 extends Root {
  procedure m(self: Q3) returns (r: int) opaque ensures r == 2 { return 2 };
}
composite Z3 extends P3, Q3 { }
procedure go(z: Z3)
  opaque
{
  var x: int := z#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'Z3' inherits it from the unrelated types P3, Q3
  assert x == 1
};
#end

/-! D4 (INTERACTION): a call to a method NO ancestor declares stays "not defined"
    even though the empty shared Root is a universal ancestor -- the Object edge
    must not silently absorb an undeclared call. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Root4 { }
composite A4b extends Root4 {
  procedure m(self: A4b) returns (r: int) opaque ensures r == 1 { return 1 };
}
procedure go(a: A4b)
  opaque
{
  var x: int := a#nope();
//              ^^^^^^^^ error: Resolution failed: 'A4b$nope' is not defined
  assert x == 1
};
#end

/-! D5: THREE-parent diamond. Every diamond above has exactly two incomparable
    declarers, so nothing pinned the arity-neutral shape of the machinery: that
    `mostSpecific` rejects a set of three (none dominates the other two), that
    `ambiguous` carries all three rather than a first-two pair, and that the message
    names every candidate as `A5, B5, C5d`.

    Two details of the expectation matter, each verified by mutating the
    PRODUCTION code (not the expectation -- mutating an expectation only tests the
    harness):

    * The candidate list is spelled in full. Making `resolveInheritedMember` name only
      the first two declarers fails this test, because the harness needs the annotation
      to be a substring of the actual message and `A5, B5, C5d` is not a substring of a
      message naming `A5, B5`. (The expectation also runs on into `; declare 'm' on
      'T5'`, which is harmless but NOT what closes this hole -- the full list alone does.)
    * The parents are declared OUT of alphabetical order (`C5d, A5, B5`). Without
      `mergeSort` the candidates come out in `ancestors`' frontier order, which is the
      `extending` order, so the message reads `C5d, A5, B5`; sorted it reads
      `A5, B5, C5d`. Declaring them alphabetically would make the two coincide and leave
      the sort unpinned. D3 above catches the same regression for two parents.

    The trailing assert is `x == 999`, which no candidate's contract can prove (A5
    ensures 1, B5 2, C5d 3), following `AmbiguityPreventsVerification`. This is for the
    reader rather than for coverage: `requireAllAnnotationsFire` already means a resolver
    that wrongly RESOLVED instead of reporting ambiguity fails on the unfired annotation,
    whatever the assert says. An assert matching one candidate would leave a reader
    unable to see that. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite C5d {
  procedure m(self: C5d) returns (r: int) opaque ensures r == 3 { return 3 };
}
composite A5 {
  procedure m(self: A5) returns (r: int) opaque ensures r == 1 { return 1 };
}
composite B5 {
  procedure m(self: B5) returns (r: int) opaque ensures r == 2 { return 2 };
}
composite T5 extends C5d, A5, B5 { }
procedure go(t: T5)
  opaque
{
  var x: int := t#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'T5' inherits it from the unrelated types A5, B5, C5d; declare 'm' on 'T5'
  assert x == 999
};
#end

/-! D6: MIXED dominance -- a shadowed declarer must not be named as a candidate. Every
    diamond above has pairwise INCOMPARABLE declarers, so the reported list and the full
    declarer list coincided and nothing distinguished them. Here they differ: A6 declares
    `m`, B6 extends A6 and overrides it, C6 is unrelated and also declares it, and T6
    extends B6, C6. Three ancestors of T6 declare `m`, but B6 shadows A6 along its branch,
    so the ambiguity is between B6 and C6 alone. Naming A6 would describe a choice the
    resolver does not have, and would call A6 and B6 "unrelated" although B6 <: A6.

    This also pins that dominance is quantified over ALL candidates rather than a
    prefix: with three declarers of which one is dominated, a check that looked at only
    the first two would report a different set. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A6 {
  procedure m(self: A6) returns (r: int) opaque ensures r == 1 { return 1 };
}
composite B6 extends A6 {
  procedure m(self: B6) returns (r: int) opaque ensures r == 2 { return 2 };
}
composite C6 {
  procedure m(self: C6) returns (r: int) opaque ensures r == 3 { return 3 };
}
composite T6 extends B6, C6 { }
procedure go(t: T6)
  opaque
{
  var x: int := t#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'T6' inherits it from the unrelated types B6, C6; declare 'm' on 'T6'
  assert x == 999
};
#end

/-! D7: the antichain filter must use STRICT dominance. Nothing rejects an `extending`
    cycle, and two mutually-extending names are each an ancestor of the other, so a
    non-strict "is some other declarer's ancestor" test calls each of them dominated and
    drops BOTH. Under such a test this program reports "the unrelated types Cc" -- one
    candidate for an ambiguity, with the cyclic branch the user must choose between
    missing entirely.

    A cycle is not otherwise meaningful here and is not endorsed by this test: it is the
    only shape that distinguishes strict from non-strict dominance, so it is what pins
    the distinction. `mostSpecific`'s own behaviour on a cycle (an order-dependent pick,
    since mutual reachability makes both names dominate) is a separate pre-existing gap;
    rejecting cycles belongs where composites are defined. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Ac extends Bc {
  procedure m(self: Ac) returns (r: int) opaque ensures r == 1 { return 1 };
}
composite Bc extends Ac {
  procedure m(self: Bc) returns (r: int) opaque ensures r == 2 { return 2 };
}
composite Cc {
  procedure m(self: Cc) returns (r: int) opaque ensures r == 3 { return 3 };
}
composite Tc extends Bc, Cc { }
procedure go(t: Tc)
  opaque
{
  var x: int := t#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'Tc' inherits it from the unrelated types Ac, Bc, Cc; declare 'm' on 'Tc'
  assert x == 999
};
#end
