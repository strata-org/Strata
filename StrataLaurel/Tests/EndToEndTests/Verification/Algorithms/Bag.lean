/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.EndToEndTests.Verification.Algorithms.BenchmarkOptions

open StrataTest.Util
open StrataTest.Util.Algorithms
open Strata

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure count(s: Sequence<int>, v: int, hi: int): int;

procedure countAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(v: int) => count(s, v, 0) == 0)
  && (forall(s: Sequence<int>) => forall(v: int) => forall(h: int) =>
        1 <= h ==> h <= seqLength(s) ==>
          count(s, v, h) == count(s, v, h - 1) + (if seqSelect(s, h - 1) == v then 1 else 0))
};

composite Bag {
  var items: Sequence<int>
}

procedure add(b: Bag, v: int)
  requires countAxioms()
  opaque
  ensures forall(w: int) => count(b#items, w, seqLength(b#items)) == old(count(b#items, w, seqLength(b#items))) + (if w == v then 1 else 0)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  modifies b
{
  b#items := seqBuild(b#items, v)
};

procedure remove(b: Bag, v: int) returns (found: bool)
//        ^^^^^^ error: modifies clause could not be proved
// desired: verifies
  requires countAxioms()
  opaque
  ensures found == (old(count(b#items, v, seqLength(b#items))) > 0)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures forall(w: int) => count(b#items, w, seqLength(b#items)) ==
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
    old(count(b#items, w, seqLength(b#items))) - (if w == v && found then 1 else 0)
  modifies b
{
  var i: int := 0;
  found := false;
  while (i < seqLength(b#items) && !found)
    invariant 0 <= i
    invariant i <= seqLength(b#items)
    invariant !found ==> count(b#items, v, i) == 0
  {
    if seqSelect(b#items, i) == v then {
      var last: int := seqLength(b#items) - 1;
      b#items := seqTake(seqUpdate(b#items, i, seqSelect(b#items, last)), last);
      found := true
    } else { i := i + 1 }
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure count(s: Sequence<int>, v: int, hi: int): int;

procedure countAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(v: int) => count(s, v, 0) == 0)
  && (forall(s: Sequence<int>) => forall(v: int) => forall(h: int) =>
        1 <= h ==> h <= seqLength(s) ==>
          count(s, v, h) == count(s, v, h - 1) + (if seqSelect(s, h - 1) == v then 1 else 0))
};

composite Bag {
  var items: Sequence<int>
}

procedure add(b: Bag, v: int)
  requires countAxioms()
  opaque
  ensures forall(w: int) => count(b#items, w, seqLength(b#items)) == old(count(b#items, w, seqLength(b#items))) + (if w == v then 1 else 0)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  modifies b
{
  b#items := seqBuild(b#items, v)
};

procedure remove(b: Bag, v: int) returns (found: bool)
//        ^^^^^^ error: modifies clause could not be proved
  requires countAxioms()
  opaque
  ensures found == (old(count(b#items, v, seqLength(b#items))) > 0)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures forall(w: int) => count(b#items, w, seqLength(b#items)) ==
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
    old(count(b#items, w, seqLength(b#items))) - (if w == v && found then 1 else 0)
  modifies b
{
  var i: int := 0;
  found := false;
  while (i < seqLength(b#items) && !found)
    invariant 0 <= i
    invariant i <= seqLength(b#items)
    invariant !found ==> count(b#items, v, i) == 0
  {
    if seqSelect(b#items, i) == v then {
      var last: int := seqLength(b#items) - 1;
      b#items := seqTake(seqUpdate(b#items, i, seqSelect(b#items, 0)), last);
      found := true
    } else { i := i + 1 }
  }
};
#end
