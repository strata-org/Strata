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

procedure sameBetween(s: Sequence<int>, a: Sequence<int>, lo: int, hi: int): bool
{
  forall(k: int) => lo <= k ==> k <= hi ==> 0 <= k ==> k < seqLength(s) ==> k < seqLength(a) ==>
    seqSelect(s, k) == seqSelect(a, k)
};

procedure swappedBelow(s: Sequence<int>, a: Sequence<int>, i: int): bool
{
  forall(k: int) => 0 <= k ==> k < i ==> k < seqLength(a) ==> seqLength(s) == seqLength(a) ==>
    seqSelect(s, k) == seqSelect(a, seqLength(a) - 1 - k)
    && seqSelect(s, seqLength(a) - 1 - k) == seqSelect(a, k)
};

procedure isReverse(s: Sequence<int>, a: Sequence<int>): bool
{
  seqLength(s) == seqLength(a)
  && (forall(k: int) => 0 <= k ==> k < seqLength(a) ==> seqSelect(s, k) == seqSelect(a, seqLength(a) - 1 - k))
};

procedure reverse(a: Sequence<int>) returns (res: Sequence<int>)
  opaque
  ensures isReverse(res, a)
{
  var s: Sequence<int> := a;
  var i: int := 0;
  var j: int := seqLength(a) - 1;
  while (i < j)
    invariant 0 <= i
    invariant j == seqLength(a) - 1 - i
    invariant i <= j + 1
    invariant seqLength(s) == seqLength(a)
    invariant swappedBelow(s, a, i)
    invariant sameBetween(s, a, i, j)
  {
    var tmp: int := seqSelect(s, i);
    s := seqUpdate(s, i, seqSelect(s, j));
    s := seqUpdate(s, j, tmp);
    i := i + 1;
    j := j - 1
  };
  res := s
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure sameBetween(s: Sequence<int>, a: Sequence<int>, lo: int, hi: int): bool
{
  forall(k: int) => lo <= k ==> k <= hi ==> 0 <= k ==> k < seqLength(s) ==> k < seqLength(a) ==>
    seqSelect(s, k) == seqSelect(a, k)
};

procedure swappedBelow(s: Sequence<int>, a: Sequence<int>, i: int): bool
{
  forall(k: int) => 0 <= k ==> k < i ==> k < seqLength(a) ==> seqLength(s) == seqLength(a) ==>
    seqSelect(s, k) == seqSelect(a, seqLength(a) - 1 - k)
    && seqSelect(s, seqLength(a) - 1 - k) == seqSelect(a, k)
};

procedure isReverse(s: Sequence<int>, a: Sequence<int>): bool
{
  seqLength(s) == seqLength(a)
  && (forall(k: int) => 0 <= k ==> k < seqLength(a) ==> seqSelect(s, k) == seqSelect(a, seqLength(a) - 1 - k))
};

procedure reverse(a: Sequence<int>) returns (res: Sequence<int>)
  opaque
  ensures isReverse(res, a)
{
  var s: Sequence<int> := a;
  var i: int := 0;
  var j: int := seqLength(a) - 1;
  while (i < seqLength(a))
    invariant 0 <= i
    invariant j == seqLength(a) - 1 - i
    invariant i <= j + 1
//            ^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant seqLength(s) == seqLength(a)
    invariant swappedBelow(s, a, i)
//            ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant sameBetween(s, a, i, j)
  {
    var tmp: int := seqSelect(s, i);
    s := seqUpdate(s, i, seqSelect(s, j));
    s := seqUpdate(s, j, tmp);
    i := i + 1;
    j := j - 1
  };
  res := s
};
#end
