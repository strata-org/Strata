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

composite IntList {
  var data: Sequence<int>
  var modCount: int
}

composite Iter {
  var list: IntList
  var cursor: int
  var expected: int
}

procedure append(l: IntList, v: int)
  opaque
  ensures seqLength(l#data) == old(seqLength(l#data)) + 1
  ensures l#modCount == old(l#modCount) + 1
  ensures forall(k: int) => 0 <= k ==> k < old(seqLength(l#data)) ==> seqSelect(l#data, k) == old(seqSelect(l#data, k))
  modifies l
{
  l#data := seqBuild(l#data, v);
  l#modCount := l#modCount + 1
};

procedure next(it: Iter) returns (v: int)
  requires it#list#modCount == it#expected
  requires 0 <= it#cursor && it#cursor < seqLength(it#list#data)
  opaque
  ensures v == seqSelect(it#list#data, old(it#cursor))
//             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
  ensures it#cursor == old(it#cursor) + 1
  modifies it
{
  v := seqSelect(it#list#data, it#cursor);
  it#cursor := it#cursor + 1
};

procedure sumBelow(s: Sequence<int>, hi: int): int;

procedure sumAxioms(): bool
{
  (forall(s: Sequence<int>) => sumBelow(s, 0) == 0)
  && (forall(s: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(s) ==>
        sumBelow(s, h) == sumBelow(s, h - 1) + seqSelect(s, h - 1))
};

procedure total(l: IntList) returns (s: int)
//        ^^^^^ error: modifies clause could not be proved
// desired: verifies
  requires sumAxioms()
  opaque
  ensures s == sumBelow(l#data, seqLength(l#data))
  modifies l
{
  var it: Iter := new Iter;
  it#list := l;
  it#cursor := 0;
  it#expected := l#modCount;
  s := 0;
  while (it#cursor < seqLength(l#data))
    invariant 0 <= it#cursor
    invariant it#cursor <= seqLength(l#data)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant it#list == l && it#expected == l#modCount
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant s == sumBelow(l#data, it#cursor)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var v: int := next(it);
//                ^^^^^^^^ error: precondition could not be proved
// desired: verifies
    s := s + v
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite IntList {
  var data: Sequence<int>
  var modCount: int
}

composite Iter {
  var list: IntList
  var cursor: int
  var expected: int
}

procedure append(l: IntList, v: int)
  opaque
  ensures seqLength(l#data) == old(seqLength(l#data)) + 1
  ensures l#modCount == old(l#modCount) + 1
  ensures forall(k: int) => 0 <= k ==> k < old(seqLength(l#data)) ==> seqSelect(l#data, k) == old(seqSelect(l#data, k))
  modifies l
{
  l#data := seqBuild(l#data, v);
  l#modCount := l#modCount + 1
};

procedure next(it: Iter) returns (v: int)
  requires it#list#modCount == it#expected
  requires 0 <= it#cursor && it#cursor < seqLength(it#list#data)
  opaque
  ensures v == seqSelect(it#list#data, old(it#cursor))
//             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  ensures it#cursor == old(it#cursor) + 1
  modifies it
{
  v := seqSelect(it#list#data, it#cursor);
  it#cursor := it#cursor + 1
};

procedure sumBelow(s: Sequence<int>, hi: int): int;

procedure sumAxioms(): bool
{
  (forall(s: Sequence<int>) => sumBelow(s, 0) == 0)
  && (forall(s: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(s) ==>
        sumBelow(s, h) == sumBelow(s, h - 1) + seqSelect(s, h - 1))
};

procedure total(l: IntList) returns (s: int)
//        ^^^^^ error: modifies clause could not be proved
  requires sumAxioms()
  opaque
  ensures s == sumBelow(l#data, seqLength(l#data))
  modifies l
{
  var it: Iter := new Iter;
  it#list := l;
  it#cursor := 0;
  it#expected := l#modCount;
  s := 0;
  while (it#cursor < seqLength(l#data))
    invariant 0 <= it#cursor
//            ^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant it#cursor <= seqLength(l#data)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant it#list == l && it#expected == l#modCount
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion could not be proved
    invariant s == sumBelow(l#data, it#cursor)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var v: int := next(it);
//                ^^^^^^^^ error: precondition could not be proved
    append(l, 0);
    s := s + v
  }
};
#end
