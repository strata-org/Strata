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

procedure prefixBelowSuffix(s: Sequence<int>, i: int): bool
{
  forall(k: int) => forall(m: int) => 0 <= k ==> k < i ==> i <= m ==> m < seqLength(s) ==>
    seqSelect(s, k) <= seqSelect(s, m)
};

procedure maxAt(s: Sequence<int>, j: int): bool
{
  forall(k: int) => 0 <= k ==> k <= j ==> j < seqLength(s) ==> seqSelect(s, k) <= seqSelect(s, j)
};

procedure bubbleSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var i: int := seqLength(s);
  while (i > 1)
    invariant 0 <= i
    invariant i <= seqLength(s)
    invariant seqLength(s) == seqLength(a)
    invariant sortedBetween(s, i, seqLength(s))
    invariant prefixBelowSuffix(s, i)
    invariant permutation(s, a)
  {
    var j: int := 0;
    while (j < i - 1)
      invariant 0 <= j
      invariant j < i
      invariant seqLength(s) == seqLength(a)
      invariant maxAt(s, j)
      invariant sortedBetween(s, i, seqLength(s))
      invariant prefixBelowSuffix(s, i)
      invariant permutation(s, a)
//              ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    {
      if seqSelect(s, j) > seqSelect(s, j + 1) then {
        var tmp: int := seqSelect(s, j);
        s := seqUpdate(s, j, seqSelect(s, j + 1));
        s := seqUpdate(s, j + 1, tmp)
      };
      j := j + 1
    };
    i := i - 1
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

procedure prefixBelowSuffix(s: Sequence<int>, i: int): bool
{
  forall(k: int) => forall(m: int) => 0 <= k ==> k < i ==> i <= m ==> m < seqLength(s) ==>
    seqSelect(s, k) <= seqSelect(s, m)
};

procedure maxAt(s: Sequence<int>, j: int): bool
{
  forall(k: int) => 0 <= k ==> k <= j ==> j < seqLength(s) ==> seqSelect(s, k) <= seqSelect(s, j)
};

procedure bubbleSort(a: Sequence<int>) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures sortedBetween(res, 0, seqLength(res))
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var i: int := seqLength(s);
  while (i > 1)
    invariant 0 <= i
    invariant i <= seqLength(s)
    invariant seqLength(s) == seqLength(a)
    invariant sortedBetween(s, i, seqLength(s))
    invariant prefixBelowSuffix(s, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant permutation(s, a)
  {
    var j: int := 0;
    while (j < i - 2)
      invariant 0 <= j
      invariant j < i
      invariant seqLength(s) == seqLength(a)
      invariant maxAt(s, j)
      invariant sortedBetween(s, i, seqLength(s))
      invariant prefixBelowSuffix(s, i)
      invariant permutation(s, a)
//              ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    {
      if seqSelect(s, j) > seqSelect(s, j + 1) then {
        var tmp: int := seqSelect(s, j);
        s := seqUpdate(s, j, seqSelect(s, j + 1));
        s := seqUpdate(s, j + 1, tmp)
      };
      j := j + 1
    };
    i := i - 1
  };
  res := s
};
#end
