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

procedure permutation(s: Sequence<int>, t: Sequence<int>): bool
{
  seqLength(s) == seqLength(t) && (forall(v: int) => count(s, v, seqLength(s)) == count(t, v, seqLength(t)))
};

procedure rank(x: int, p: int): int
{
  if x < p then 0 else if x == p then 1 else 2
};

procedure classified(s: Sequence<int>, p: int): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i <= j ==> j < seqLength(s) ==>
    rank(seqSelect(s, i), p) <= rank(seqSelect(s, j), p)
};

procedure regions(s: Sequence<int>, p: int, lt: int, i: int, gt: int): bool
{
  (forall(k: int) => 0 <= k ==> k < lt ==> k < seqLength(s) ==> seqSelect(s, k) < p)
  && (forall(k: int) => lt <= k ==> k < i ==> 0 <= k ==> k < seqLength(s) ==> seqSelect(s, k) == p)
  && (forall(k: int) => gt <= k ==> k < seqLength(s) ==> 0 <= k ==> seqSelect(s, k) > p)
};

procedure partition(a: Sequence<int>, p: int) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures classified(res, p)
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var lt: int := 0;
  var i: int := 0;
  var gt: int := seqLength(a);
  while (i < gt)
    invariant 0 <= lt
    invariant lt <= i
    invariant i <= gt
    invariant gt <= seqLength(s)
    invariant seqLength(s) == seqLength(a)
    invariant regions(s, p, lt, i, gt)
    invariant permutation(s, a)
//            ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    if seqSelect(s, i) < p then {
      var tmp: int := seqSelect(s, lt);
      s := seqUpdate(s, lt, seqSelect(s, i));
      s := seqUpdate(s, i, tmp);
      lt := lt + 1;
      i := i + 1
    } else if seqSelect(s, i) > p then {
      gt := gt - 1;
      var tmp: int := seqSelect(s, gt);
      s := seqUpdate(s, gt, seqSelect(s, i));
      s := seqUpdate(s, i, tmp)
    } else {
      i := i + 1
    }
  };
  res := s
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

procedure permutation(s: Sequence<int>, t: Sequence<int>): bool
{
  seqLength(s) == seqLength(t) && (forall(v: int) => count(s, v, seqLength(s)) == count(t, v, seqLength(t)))
};

procedure rank(x: int, p: int): int
{
  if x < p then 0 else if x == p then 1 else 2
};

procedure classified(s: Sequence<int>, p: int): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i <= j ==> j < seqLength(s) ==>
    rank(seqSelect(s, i), p) <= rank(seqSelect(s, j), p)
};

procedure regions(s: Sequence<int>, p: int, lt: int, i: int, gt: int): bool
{
  (forall(k: int) => 0 <= k ==> k < lt ==> k < seqLength(s) ==> seqSelect(s, k) < p)
  && (forall(k: int) => lt <= k ==> k < i ==> 0 <= k ==> k < seqLength(s) ==> seqSelect(s, k) == p)
  && (forall(k: int) => gt <= k ==> k < seqLength(s) ==> 0 <= k ==> seqSelect(s, k) > p)
};

procedure partition(a: Sequence<int>, p: int) returns (res: Sequence<int>)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(a)
  ensures classified(res, p)
  ensures permutation(res, a)
{
  var s: Sequence<int> := a;
  var lt: int := 0;
  var i: int := 0;
  var gt: int := seqLength(a);
  while (i < gt)
    invariant 0 <= lt
    invariant lt <= i
    invariant i <= gt
//            ^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant gt <= seqLength(s)
    invariant seqLength(s) == seqLength(a)
    invariant regions(s, p, lt, i, gt)
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant permutation(s, a)
//            ^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    if seqSelect(s, i) < p then {
      var tmp: int := seqSelect(s, lt);
      s := seqUpdate(s, lt, seqSelect(s, i));
      s := seqUpdate(s, i, tmp);
      lt := lt + 1;
      i := i + 1
    } else if seqSelect(s, i) > p then {
      gt := gt - 1;
      var tmp: int := seqSelect(s, gt);
      s := seqUpdate(s, gt, seqSelect(s, i));
      s := seqUpdate(s, i, tmp);
      i := i + 1
    } else {
      i := i + 1
    }
  };
  res := s
};
#end
