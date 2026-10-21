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

procedure sortedBetween(s: Sequence<int>, lo: int, hi: int): bool
{
  forall(i: int) => forall(j: int) =>
    0 <= lo ==> lo <= i ==> i <= j ==> j < hi ==> hi <= seqLength(s) ==> seqSelect(s, i) <= seqSelect(s, j)
};

procedure count(s: Sequence<int>, v: int, hi: int): int;

procedure countAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(v: int) => count(s, v, 0) == 0)
  && (forall(s: Sequence<int>) => forall(v: int) => forall(h: int) =>
        1 <= h ==> h <= seqLength(s) ==>
          count(s, v, h) == count(s, v, h - 1) + (if seqSelect(s, h - 1) == v then 1 else 0))
};

procedure permutation(s: Sequence<int>, t: Sequence<int>): bool
{
  seqLength(s) == seqLength(t) && (forall(v: int) => count(s, v, seqLength(s)) == count(t, v, seqLength(t)))
};

procedure heapBetween(s: Sequence<int>, lo: int, hi: int): bool
{
  forall(k: int) => lo <= k ==> k < hi ==> 0 <= k ==> hi <= seqLength(s) ==>
    (2 * k + 1 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 1))
    && (2 * k + 2 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 2))
};

procedure heapExceptAt(s: Sequence<int>, lo: int, hi: int, root: int): bool
{
  (forall(k: int) => lo <= k ==> k < hi ==> k != root ==> 0 <= k ==> hi <= seqLength(s) ==>
     (2 * k + 1 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 1))
     && (2 * k + 2 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 2)))
  && (root > lo ==> 0 <= root ==> root < hi ==> hi <= seqLength(s) ==>
     (2 * root + 1 >= hi || seqSelect(s, (root - 1) / 2) >= seqSelect(s, 2 * root + 1))
//                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
     && (2 * root + 2 >= hi || seqSelect(s, (root - 1) / 2) >= seqSelect(s, 2 * root + 2)))
//                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
};

procedure prefixBelowSuffix(s: Sequence<int>, e: int): bool
{
  forall(k: int) => forall(m: int) => 0 <= k ==> k < e ==> e <= m ==> m < seqLength(s) ==>
    seqSelect(s, k) <= seqSelect(s, m)
};

procedure sameOutside(s: Sequence<int>, t: Sequence<int>, lo: int, hi: int): bool
{
  seqLength(s) == seqLength(t)
  && (forall(k: int) => 0 <= k ==> k < seqLength(s) ==> (k < lo || hi <= k) ==> seqSelect(s, k) == seqSelect(t, k))
};

procedure siftDown(a: Sequence<int>, start: int, stop: int) returns (res: Sequence<int>)
  requires 0 <= start
  requires start < stop
  requires stop <= seqLength(a)
  requires heapBetween(a, start + 1, stop)
  requires countAxioms()
  opaque
  ensures heapBetween(res, start, stop)
  ensures sameOutside(res, a, start, stop)
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var root: int := start;
  var done: bool := false;
  while (2 * root + 1 < stop && !done)
    invariant start <= root
    invariant root < stop
    invariant seqLength(s) == seqLength(a)
    invariant done ==> heapBetween(s, start, stop)
    invariant !done ==> heapExceptAt(s, start, stop, root)
    invariant sameOutside(s, a, start, stop)
    invariant permutation(s, a)
//            ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var child: int := 2 * root + 1;
    if child + 1 < stop && seqSelect(s, child) < seqSelect(s, child + 1) then { child := child + 1 };
    if seqSelect(s, root) < seqSelect(s, child) then {
      var tmp: int := seqSelect(s, root);
      s := seqUpdate(s, root, seqSelect(s, child));
      s := seqUpdate(s, child, tmp);
      root := child
    } else {
      done := true
    }
  };
  res := s
};

procedure heapSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var n: int := seqLength(a);
  var start: int := n / 2 - 1;
  while (start >= 0)
    invariant -1 <= start
    invariant start < n
    invariant seqLength(s) == n
    invariant heapBetween(s, start + 1, n)
    invariant permutation(s, a)
  {
    s := siftDown(s, start, n);
    start := start - 1
  };
  var stop: int := n - 1;
  while (stop > 0)
    invariant 0 <= stop || n == 0
    invariant stop < n || n == 0
    invariant seqLength(s) == n
    invariant heapBetween(s, 0, stop + 1)
    invariant sortedBetween(s, stop + 1, n)
    invariant prefixBelowSuffix(s, stop + 1)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant permutation(s, a)
//            ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var tmp: int := seqSelect(s, 0);
    s := seqUpdate(s, 0, seqSelect(s, stop));
    s := seqUpdate(s, stop, tmp);
    s := siftDown(s, 0, stop);
    stop := stop - 1
  };
  res := s
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure sortedBetween(s: Sequence<int>, lo: int, hi: int): bool
{
  forall(i: int) => forall(j: int) =>
    0 <= lo ==> lo <= i ==> i <= j ==> j < hi ==> hi <= seqLength(s) ==> seqSelect(s, i) <= seqSelect(s, j)
};

procedure count(s: Sequence<int>, v: int, hi: int): int;

procedure countAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(v: int) => count(s, v, 0) == 0)
  && (forall(s: Sequence<int>) => forall(v: int) => forall(h: int) =>
        1 <= h ==> h <= seqLength(s) ==>
          count(s, v, h) == count(s, v, h - 1) + (if seqSelect(s, h - 1) == v then 1 else 0))
};

procedure permutation(s: Sequence<int>, t: Sequence<int>): bool
{
  seqLength(s) == seqLength(t) && (forall(v: int) => count(s, v, seqLength(s)) == count(t, v, seqLength(t)))
};

procedure heapBetween(s: Sequence<int>, lo: int, hi: int): bool
{
  forall(k: int) => lo <= k ==> k < hi ==> 0 <= k ==> hi <= seqLength(s) ==>
    (2 * k + 1 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 1))
    && (2 * k + 2 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 2))
};

procedure heapExceptAt(s: Sequence<int>, lo: int, hi: int, root: int): bool
{
  (forall(k: int) => lo <= k ==> k < hi ==> k != root ==> 0 <= k ==> hi <= seqLength(s) ==>
     (2 * k + 1 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 1))
     && (2 * k + 2 >= hi || seqSelect(s, k) >= seqSelect(s, 2 * k + 2)))
  && (root > lo ==> 0 <= root ==> root < hi ==> hi <= seqLength(s) ==>
     (2 * root + 1 >= hi || seqSelect(s, (root - 1) / 2) >= seqSelect(s, 2 * root + 1))
//                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
     && (2 * root + 2 >= hi || seqSelect(s, (root - 1) / 2) >= seqSelect(s, 2 * root + 2)))
//                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure prefixBelowSuffix(s: Sequence<int>, e: int): bool
{
  forall(k: int) => forall(m: int) => 0 <= k ==> k < e ==> e <= m ==> m < seqLength(s) ==>
    seqSelect(s, k) <= seqSelect(s, m)
};

procedure sameOutside(s: Sequence<int>, t: Sequence<int>, lo: int, hi: int): bool
{
  seqLength(s) == seqLength(t)
  && (forall(k: int) => 0 <= k ==> k < seqLength(s) ==> (k < lo || hi <= k) ==> seqSelect(s, k) == seqSelect(t, k))
};

procedure siftDown(a: Sequence<int>, start: int, stop: int) returns (res: Sequence<int>)
  requires 0 <= start
  requires start < stop
  requires stop <= seqLength(a)
  requires heapBetween(a, start + 1, stop)
  requires countAxioms()
  opaque
  ensures heapBetween(res, start, stop)
  ensures sameOutside(res, a, start, stop)
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var root: int := start;
  var done: bool := false;
  while (2 * root + 1 < stop && !done)
    invariant start <= root
    invariant root < stop
    invariant seqLength(s) == seqLength(a)
    invariant done ==> heapBetween(s, start, stop)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant !done ==> heapExceptAt(s, start, stop, root)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant sameOutside(s, a, start, stop)
    invariant permutation(s, a)
//            ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var child: int := 2 * root;
    if child + 1 < stop && seqSelect(s, child) < seqSelect(s, child + 1) then { child := child + 1 };
    if seqSelect(s, root) < seqSelect(s, child) then {
      var tmp: int := seqSelect(s, root);
      s := seqUpdate(s, root, seqSelect(s, child));
      s := seqUpdate(s, child, tmp);
      root := child
    } else {
      done := true
    }
  };
  res := s
};

procedure heapSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var n: int := seqLength(a);
  var start: int := n / 2 - 1;
  while (start >= 0)
    invariant -1 <= start
    invariant start < n
    invariant seqLength(s) == n
    invariant heapBetween(s, start + 1, n)
    invariant permutation(s, a)
  {
    s := siftDown(s, start, n);
    start := start - 1
  };
  var stop: int := n - 1;
  while (stop > 0)
    invariant 0 <= stop || n == 0
    invariant stop < n || n == 0
    invariant seqLength(s) == n
    invariant heapBetween(s, 0, stop + 1)
    invariant sortedBetween(s, stop + 1, n)
    invariant prefixBelowSuffix(s, stop + 1)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant permutation(s, a)
//            ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var tmp: int := seqSelect(s, 0);
    s := seqUpdate(s, 0, seqSelect(s, stop));
    s := seqUpdate(s, stop, tmp);
    s := siftDown(s, 0, stop);
    stop := stop - 1
  };
  res := s
};
#end
