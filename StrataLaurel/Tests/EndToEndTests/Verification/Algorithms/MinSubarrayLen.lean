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

procedure noWindowShorterThan(a: Sequence<int>, target: int, len: int, endBefore: int): bool
{
  forall(lo: int) => forall(hi: int) => 0 <= lo ==> lo < hi ==> hi <= endBefore ==> hi - lo < len ==>
    sumRange(a, lo, hi) < target
};

procedure someWindowOfLength(a: Sequence<int>, target: int, len: int): bool
{
  exists(lo: int) => 0 <= lo && lo + len <= seqLength(a) && sumRange(a, lo, lo + len) >= target
};

procedure minSubarrayLen(a: Sequence<int>, target: int) returns (r: int)
  requires target >= 1
  requires forall(k: int) => 0 <= k ==> k < seqLength(a) ==> seqSelect(a, k) >= 1
  requires sumAxioms()
  opaque
  ensures r == 0 ==> noWindowShorterThan(a, target, seqLength(a) + 1, seqLength(a))
  ensures r != 0 ==> 1 <= r && r <= seqLength(a)
  ensures r != 0 ==> someWindowOfLength(a, target, r)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures r != 0 ==> noWindowShorterThan(a, target, r, seqLength(a))
{
  var n: int := seqLength(a);
  var best: int := n + 1;
  var lo: int := 0;
  var sum: int := 0;
  var hi: int := 0;
  while (hi < n)
    invariant 0 <= lo
    invariant lo <= hi
    invariant hi <= n
    invariant sum == sumRange(a, lo, hi)
    invariant 1 <= best
//            ^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant best <= n + 1
//            ^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant noWindowShorterThan(a, target, best, hi)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant best <= n ==> someWindowOfLength(a, target, best)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    sum := sum + seqSelect(a, hi);
    hi := hi + 1;
    while (sum >= target)
      invariant 0 <= lo
      invariant lo <= hi
      invariant sum == sumRange(a, lo, hi)
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    {
      if hi - lo < best then { best := hi - lo };
      sum := sum - seqSelect(a, lo);
      lo := lo + 1
    }
  };
  r := if best == n + 1 then 0 else best
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

procedure noWindowShorterThan(a: Sequence<int>, target: int, len: int, endBefore: int): bool
{
  forall(lo: int) => forall(hi: int) => 0 <= lo ==> lo < hi ==> hi <= endBefore ==> hi - lo < len ==>
    sumRange(a, lo, hi) < target
};

procedure someWindowOfLength(a: Sequence<int>, target: int, len: int): bool
{
  exists(lo: int) => 0 <= lo && lo + len <= seqLength(a) && sumRange(a, lo, lo + len) >= target
};

procedure minSubarrayLen(a: Sequence<int>, target: int) returns (r: int)
  requires target >= 1
  requires forall(k: int) => 0 <= k ==> k < seqLength(a) ==> seqSelect(a, k) >= 1
  requires sumAxioms()
  opaque
  ensures r == 0 ==> noWindowShorterThan(a, target, seqLength(a) + 1, seqLength(a))
  ensures r != 0 ==> 1 <= r && r <= seqLength(a)
  ensures r != 0 ==> someWindowOfLength(a, target, r)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures r != 0 ==> noWindowShorterThan(a, target, r, seqLength(a))
{
  var n: int := seqLength(a);
  var best: int := n + 1;
  var lo: int := 0;
  var sum: int := 0;
  var hi: int := 0;
  while (hi < n)
    invariant 0 <= lo
    invariant lo <= hi
    invariant hi <= n
    invariant sum == sumRange(a, lo, hi)
    invariant 1 <= best
//            ^^^^^^^^^ error: assertion could not be proved
    invariant best <= n + 1
//            ^^^^^^^^^^^^^ error: assertion could not be proved
    invariant noWindowShorterThan(a, target, best, hi)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant best <= n ==> someWindowOfLength(a, target, best)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    sum := sum + seqSelect(a, hi);
    hi := hi + 1;
    while (sum > target)
      invariant 0 <= lo
      invariant lo <= hi
      invariant sum == sumRange(a, lo, hi)
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    {
      if hi - lo < best then { best := hi - lo };
      sum := sum - seqSelect(a, lo);
      lo := lo + 1
    }
  };
  r := if best == n + 1 then 0 else best
};
#end
