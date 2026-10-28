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

procedure leqAcross(s: Sequence<int>, j: int, i: int): bool
{
  forall(k: int) => forall(m: int) => 0 <= k ==> k < j ==> j < m ==> m <= i ==> i < seqLength(s) ==>
    seqSelect(s, k) <= seqSelect(s, m)
};

procedure insertionSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var i: int := 0;
  while (i < seqLength(s))
    invariant 0 <= i
    invariant i <= seqLength(s)
    invariant seqLength(s) == seqLength(a)
    invariant sortedBetween(s, 0, i)
    invariant permutation(s, a)
  {
    var j: int := i;
    while (j > 0 && seqSelect(s, j - 1) > seqSelect(s, j))
      invariant 0 <= j
//              ^^^^^^ error: assertion could not be proved
// desired: verifies
      invariant j <= i
      invariant i < seqLength(s)
      invariant seqLength(s) == seqLength(a)
      invariant sortedBetween(s, 0, j)
      invariant sortedBetween(s, j, i + 1)
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
      invariant leqAcross(s, j, i)
      invariant permutation(s, a)
//              ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    {
      var tmp: int := seqSelect(s, j - 1);
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      s := seqUpdate(s, j - 1, seqSelect(s, j));
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      s := seqUpdate(s, j, tmp);
      j := j - 1
    };
    i := i + 1
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

procedure leqAcross(s: Sequence<int>, j: int, i: int): bool
{
  forall(k: int) => forall(m: int) => 0 <= k ==> k < j ==> j < m ==> m <= i ==> i < seqLength(s) ==>
    seqSelect(s, k) <= seqSelect(s, m)
};

procedure insertionSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var i: int := 0;
  while (i < seqLength(s))
    invariant 0 <= i
    invariant i <= seqLength(s)
    invariant seqLength(s) == seqLength(a)
    invariant sortedBetween(s, 0, i)
//            ^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant permutation(s, a)
  {
    var j: int := i;
    while (j > 1 && seqSelect(s, j - 1) > seqSelect(s, j))
      invariant 0 <= j
//              ^^^^^^ error: assertion could not be proved
      invariant j <= i
      invariant i < seqLength(s)
      invariant seqLength(s) == seqLength(a)
      invariant sortedBetween(s, 0, j)
      invariant sortedBetween(s, j, i + 1)
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
      invariant leqAcross(s, j, i)
      invariant permutation(s, a)
//              ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    {
      var tmp: int := seqSelect(s, j - 1);
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
      s := seqUpdate(s, j - 1, seqSelect(s, j));
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
      s := seqUpdate(s, j, tmp);
      j := j - 1
    };
    i := i + 1
  };
  res := s
};
#end
