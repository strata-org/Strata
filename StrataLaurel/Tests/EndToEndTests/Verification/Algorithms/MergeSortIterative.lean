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

procedure blocksSorted(s: Sequence<int>, w: int, lo: int): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i <= j ==> j < seqLength(s) ==> w >= 1 ==>
    ((j < lo && i / (2 * w) == j / (2 * w)) || (lo <= i && i / w == j / w)) ==>
      seqSelect(s, i) <= seqSelect(s, j)
};

procedure sameOutside(s: Sequence<int>, t: Sequence<int>, lo: int, hi: int): bool
{
  seqLength(s) == seqLength(t)
  && (forall(k: int) => 0 <= k ==> k < seqLength(s) ==> (k < lo || hi <= k) ==> seqSelect(s, k) == seqSelect(t, k))
};

procedure mergeRuns(s: Sequence<int>, lo: int, mid: int, hi: int) returns (res: Sequence<int>)
  requires 0 <= lo
  requires lo <= mid
  requires mid <= hi
  requires hi <= seqLength(s)
  requires sortedBetween(s, lo, mid)
  requires sortedBetween(s, mid, hi)
  requires countAxioms()
  opaque
  ensures sameOutside(res, s, lo, hi)
  ensures sortedBetween(res, lo, hi)
  ensures permutation(res, s)
//        ^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var merged: Sequence<int> := seqEmpty();
  var i: int := lo;
  var j: int := mid;
  while (i < mid || j < hi)
    invariant lo <= i
    invariant i <= mid
    invariant mid <= j
    invariant j <= hi
    invariant seqLength(merged) == (i - lo) + (j - mid)
    invariant sortedBetween(merged, 0, seqLength(merged))
    invariant seqLength(merged) > 0 ==> i < mid ==> seqSelect(merged, seqLength(merged) - 1) <= seqSelect(s, i)
    invariant seqLength(merged) > 0 ==> j < hi ==> seqSelect(merged, seqLength(merged) - 1) <= seqSelect(s, j)
  {
    if j >= hi || (i < mid && seqSelect(s, i) <= seqSelect(s, j)) then {
      merged := seqBuild(merged, seqSelect(s, i));
      i := i + 1
    } else {
      merged := seqBuild(merged, seqSelect(s, j));
      j := j + 1
    }
  };
  res := seqAppend(seqAppend(seqTake(s, lo), merged), seqDrop(s, hi))
};

procedure mergeSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var n: int := seqLength(a);
  var width: int := 1;
  while (width < n)
    invariant 1 <= width
    invariant seqLength(s) == n
    invariant blocksSorted(s, width, 0)
    invariant permutation(s, a)
  {
    var lo: int := 0;
    while (lo < n)
      invariant 0 <= lo
      invariant lo % (2 * width) == 0 || lo == n
      invariant seqLength(s) == n
      invariant blocksSorted(s, width, lo)
      invariant permutation(s, a)
    {
      var mid: int := if lo + width < n then lo + width else n;
      var hi: int := if lo + 2 * width < n then lo + 2 * width else n;
      s := mergeRuns(s, lo, mid, hi);
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      lo := hi
    };
    width := width * 2
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

procedure blocksSorted(s: Sequence<int>, w: int, lo: int): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i <= j ==> j < seqLength(s) ==> w >= 1 ==>
    ((j < lo && i / (2 * w) == j / (2 * w)) || (lo <= i && i / w == j / w)) ==>
      seqSelect(s, i) <= seqSelect(s, j)
};

procedure sameOutside(s: Sequence<int>, t: Sequence<int>, lo: int, hi: int): bool
{
  seqLength(s) == seqLength(t)
  && (forall(k: int) => 0 <= k ==> k < seqLength(s) ==> (k < lo || hi <= k) ==> seqSelect(s, k) == seqSelect(t, k))
};

procedure mergeRuns(s: Sequence<int>, lo: int, mid: int, hi: int) returns (res: Sequence<int>)
  requires 0 <= lo
  requires lo <= mid
  requires mid <= hi
  requires hi <= seqLength(s)
  requires sortedBetween(s, lo, mid)
  requires sortedBetween(s, mid, hi)
  requires countAxioms()
  opaque
  ensures sameOutside(res, s, lo, hi)
  ensures sortedBetween(res, lo, hi)
  ensures permutation(res, s)
//        ^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var merged: Sequence<int> := seqEmpty();
  var i: int := lo;
  var j: int := mid;
  while (i < mid || j < hi)
    invariant lo <= i
    invariant i <= mid
    invariant mid <= j
    invariant j <= hi
    invariant seqLength(merged) == (i - lo) + (j - mid)
    invariant sortedBetween(merged, 0, seqLength(merged))
    invariant seqLength(merged) > 0 ==> i < mid ==> seqSelect(merged, seqLength(merged) - 1) <= seqSelect(s, i)
    invariant seqLength(merged) > 0 ==> j < hi ==> seqSelect(merged, seqLength(merged) - 1) <= seqSelect(s, j)
  {
    if j >= hi || (i < mid && seqSelect(s, i) <= seqSelect(s, j)) then {
      merged := seqBuild(merged, seqSelect(s, i));
      i := i + 1
    } else {
      merged := seqBuild(merged, seqSelect(s, j));
      j := j + 1
    }
  };
  res := seqAppend(seqAppend(seqTake(s, lo), merged), seqDrop(s, hi))
};

procedure mergeSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var n: int := seqLength(a);
  var width: int := 1;
  while (width < n)
    invariant 1 <= width
    invariant seqLength(s) == n
    invariant blocksSorted(s, width, 0)
    invariant permutation(s, a)
  {
    var lo: int := 0;
    while (lo < n)
      invariant 0 <= lo
      invariant lo % (2 * width) == 0 || lo == n
      invariant seqLength(s) == n
      invariant blocksSorted(s, width, lo)
      invariant permutation(s, a)
    {
      var mid: int := lo + width;
      var hi: int := if lo + 2 * width < n then lo + 2 * width else n;
      s := mergeRuns(s, lo, mid, hi);
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
      lo := hi
    };
    width := width * 2
  };
  res := s
};
#end
