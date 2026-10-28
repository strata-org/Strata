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

procedure countsMerged(c: Sequence<int>, a: Sequence<int>, b: Sequence<int>, i: int, j: int): bool
{
  forall(v: int) => count(c, v, i + j) == count(a, v, i) + count(b, v, j)
};

procedure merge(a: Sequence<int>, b: Sequence<int>) returns (c: Sequence<int>)
  requires sortedBetween(a, 0, seqLength(a))
  requires sortedBetween(b, 0, seqLength(b))
  requires countAxioms()
  opaque
  ensures seqLength(c) == seqLength(a) + seqLength(b)
  ensures sortedBetween(c, 0, seqLength(c))
  ensures countsMerged(c, a, b, seqLength(a), seqLength(b))
{
  var out: Sequence<int> := seqEmpty();
  var i: int := 0;
  var j: int := 0;
  while (i < seqLength(a) || j < seqLength(b))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant 0 <= j
    invariant j <= seqLength(b)
    invariant seqLength(out) == i + j
    invariant sortedBetween(out, 0, i + j)
    invariant i + j > 0 ==> i < seqLength(a) ==> seqSelect(out, i + j - 1) <= seqSelect(a, i)
    invariant i + j > 0 ==> j < seqLength(b) ==> seqSelect(out, i + j - 1) <= seqSelect(b, j)
    invariant countsMerged(out, a, b, i, j)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    if j >= seqLength(b) || (i < seqLength(a) && seqSelect(a, i) <= seqSelect(b, j)) then {
      out := seqBuild(out, seqSelect(a, i));
      i := i + 1
    } else {
      out := seqBuild(out, seqSelect(b, j));
      j := j + 1
    }
  };
  c := out
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

procedure countsMerged(c: Sequence<int>, a: Sequence<int>, b: Sequence<int>, i: int, j: int): bool
{
  forall(v: int) => count(c, v, i + j) == count(a, v, i) + count(b, v, j)
};

procedure merge(a: Sequence<int>, b: Sequence<int>) returns (c: Sequence<int>)
  requires sortedBetween(a, 0, seqLength(a))
  requires sortedBetween(b, 0, seqLength(b))
  requires countAxioms()
  opaque
  ensures seqLength(c) == seqLength(a) + seqLength(b)
  ensures sortedBetween(c, 0, seqLength(c))
  ensures countsMerged(c, a, b, seqLength(a), seqLength(b))
{
  var out: Sequence<int> := seqEmpty();
  var i: int := 0;
  var j: int := 0;
  while (i < seqLength(a) || j < seqLength(b))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant 0 <= j
    invariant j <= seqLength(b)
    invariant seqLength(out) == i + j
    invariant sortedBetween(out, 0, i + j)
    invariant i + j > 0 ==> i < seqLength(a) ==> seqSelect(out, i + j - 1) <= seqSelect(a, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant i + j > 0 ==> j < seqLength(b) ==> seqSelect(out, i + j - 1) <= seqSelect(b, j)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant countsMerged(out, a, b, i, j)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    if j >= seqLength(b) || (i < seqLength(a) && seqSelect(a, i) > seqSelect(b, j)) then {
      out := seqBuild(out, seqSelect(a, i));
      i := i + 1
    } else {
      out := seqBuild(out, seqSelect(b, j));
      j := j + 1
    }
  };
  c := out
};
#end
