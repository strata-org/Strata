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

procedure filledBelow(s: Sequence<int>, v: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(s) ==> seqSelect(s, k) == v
};

procedure copiedBelow(dst: Sequence<int>, src: Sequence<int>, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(dst) ==> k < seqLength(src) ==>
    seqSelect(dst, k) == seqSelect(src, k)
};

procedure fill(n: int, v: int) returns (res: Sequence<int>)
  requires n >= 0
  opaque
  ensures seqLength(res) == n
  ensures filledBelow(res, v, n)
{
  var s: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    invariant seqLength(s) == i
    invariant filledBelow(s, v, i)
  {
    s := seqBuild(s, v);
    i := i + 1
  };
  res := s
};

procedure copy(src: Sequence<int>) returns (res: Sequence<int>)
  opaque
  ensures seqLength(res) == seqLength(src)
  ensures copiedBelow(res, src, seqLength(src))
{
  var s: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < seqLength(src))
    invariant 0 <= i
    invariant i <= seqLength(src)
    invariant seqLength(s) == i
    invariant copiedBelow(s, src, i)
  {
    s := seqBuild(s, seqSelect(src, i));
    i := i + 1
  };
  res := s
};

procedure sum(a: Sequence<int>) returns (r: int)
  requires sumAxioms()
  opaque
  ensures r == sumRange(a, 0, seqLength(a))
{
  var acc: int := 0;
  var i: int := 0;
  while (i < seqLength(a))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant acc == sumRange(a, 0, i)
  {
    acc := acc + seqSelect(a, i);
    i := i + 1
  };
  r := acc
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

procedure filledBelow(s: Sequence<int>, v: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(s) ==> seqSelect(s, k) == v
};

procedure copiedBelow(dst: Sequence<int>, src: Sequence<int>, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(dst) ==> k < seqLength(src) ==>
    seqSelect(dst, k) == seqSelect(src, k)
};

procedure fill(n: int, v: int) returns (res: Sequence<int>)
  requires n >= 0
  opaque
  ensures seqLength(res) == n
  ensures filledBelow(res, v, n)
{
  var s: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    invariant seqLength(s) == i
    invariant filledBelow(s, v, i)
  {
    s := seqBuild(s, v);
    i := i + 1
  };
  res := s
};

procedure copy(src: Sequence<int>) returns (res: Sequence<int>)
  opaque
  ensures seqLength(res) == seqLength(src)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures copiedBelow(res, src, seqLength(src))
{
  var s: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < seqLength(src) - 1)
    invariant 0 <= i
    invariant i <= seqLength(src)
    invariant seqLength(s) == i
    invariant copiedBelow(s, src, i)
  {
    s := seqBuild(s, seqSelect(src, i));
    i := i + 1
  };
  res := s
};

procedure sum(a: Sequence<int>) returns (r: int)
  requires sumAxioms()
  opaque
  ensures r == sumRange(a, 0, seqLength(a))
{
  var acc: int := 0;
  var i: int := 0;
  while (i < seqLength(a))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant acc == sumRange(a, 0, i)
  {
    acc := acc + seqSelect(a, i);
    i := i + 1
  };
  r := acc
};
#end
