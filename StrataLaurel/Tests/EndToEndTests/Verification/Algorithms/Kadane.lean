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

procedure sumRange(s: Sequence<int>, lo: int, hi: int): int;

procedure sumAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(lo: int) => forall(hi: int) => hi <= lo ==> sumRange(s, lo, hi) == 0)
  && (forall(s: Sequence<int>) => forall(lo: int) => forall(hi: int) =>
        0 <= lo ==> lo < hi ==> hi <= seqLength(s) ==>
          sumRange(s, lo, hi) == sumRange(s, lo, hi - 1) + seqSelect(s, hi - 1))
};

procedure isBestUpTo(a: Sequence<int>, best: int, i: int): bool
{
  (forall(lo: int) => forall(hi: int) => 0 <= lo ==> lo <= hi ==> hi <= i ==> sumRange(a, lo, hi) <= best)
  && (exists(lo: int) => exists(hi: int) => 0 <= lo && lo <= hi && hi <= i && sumRange(a, lo, hi) == best)
};

procedure isBestEndingAt(a: Sequence<int>, cur: int, i: int): bool
{
  (forall(lo: int) => 0 <= lo ==> lo <= i ==> sumRange(a, lo, i) <= cur)
  && (exists(lo: int) => 0 <= lo && lo <= i && sumRange(a, lo, i) == cur)
};

procedure maxSubarray(a: Sequence<int>) returns (r: int)
  requires sumAxioms()
  opaque
  ensures isBestUpTo(a, r, seqLength(a))
{
  var best: int := 0;
  var cur: int := 0;
  var i: int := 0;
  while (i < seqLength(a))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant isBestEndingAt(a, cur, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
//            ^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant isBestUpTo(a, best, i)
//            ^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
//            ^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    cur := if cur + seqSelect(a, i) > 0 then cur + seqSelect(a, i) else 0;
    best := if cur > best then cur else best;
    i := i + 1
  };
  r := best
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure sumRange(s: Sequence<int>, lo: int, hi: int): int;

procedure sumAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(lo: int) => forall(hi: int) => hi <= lo ==> sumRange(s, lo, hi) == 0)
  && (forall(s: Sequence<int>) => forall(lo: int) => forall(hi: int) =>
        0 <= lo ==> lo < hi ==> hi <= seqLength(s) ==>
          sumRange(s, lo, hi) == sumRange(s, lo, hi - 1) + seqSelect(s, hi - 1))
};

procedure isBestUpTo(a: Sequence<int>, best: int, i: int): bool
{
  (forall(lo: int) => forall(hi: int) => 0 <= lo ==> lo <= hi ==> hi <= i ==> sumRange(a, lo, hi) <= best)
  && (exists(lo: int) => exists(hi: int) => 0 <= lo && lo <= hi && hi <= i && sumRange(a, lo, hi) == best)
};

procedure isBestEndingAt(a: Sequence<int>, cur: int, i: int): bool
{
  (forall(lo: int) => 0 <= lo ==> lo <= i ==> sumRange(a, lo, i) <= cur)
  && (exists(lo: int) => 0 <= lo && lo <= i && sumRange(a, lo, i) == cur)
};

procedure maxSubarray(a: Sequence<int>) returns (r: int)
  requires sumAxioms()
  opaque
  ensures isBestUpTo(a, r, seqLength(a))
{
  var best: int := 0;
  var cur: int := 0;
  var i: int := 0;
  while (i < seqLength(a))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant isBestEndingAt(a, cur, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
//            ^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant isBestUpTo(a, best, i)
//            ^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
//            ^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    cur := cur + seqSelect(a, i);
    best := if cur > best then cur else best;
    i := i + 1
  };
  r := best
};
#end
