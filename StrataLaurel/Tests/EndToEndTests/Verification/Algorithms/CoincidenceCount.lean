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

procedure strictlyIncreasing(s: Sequence<int>): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i < j ==> j < seqLength(s) ==> seqSelect(s, i) < seqSelect(s, j)
};

procedure contains(b: Sequence<int>, x: int): bool
{
  exists(k: int) => 0 <= k && k < seqLength(b) && seqSelect(b, k) == x
};

procedure common(a: Sequence<int>, b: Sequence<int>, hi: int): int;

procedure commonAxioms(): bool
{
  (forall(a: Sequence<int>) => forall(b: Sequence<int>) => common(a, b, 0) == 0)
  && (forall(a: Sequence<int>) => forall(b: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(a) ==>
        common(a, b, h) == common(a, b, h - 1) + (if contains(b, seqSelect(a, h - 1)) then 1 else 0))
};

procedure bBelowAi(a: Sequence<int>, b: Sequence<int>, i: int, j: int): bool
{
  0 <= i ==> i < seqLength(a) ==>
    (forall(m: int) => 0 <= m ==> m < j ==> m < seqLength(b) ==> seqSelect(b, m) < seqSelect(a, i))
};

procedure aBelowBj(a: Sequence<int>, b: Sequence<int>, i: int, j: int): bool
{
  0 <= j ==> j < seqLength(b) ==>
    (forall(k: int) => 0 <= k ==> k < i ==> k < seqLength(a) ==> seqSelect(a, k) < seqSelect(b, j))
};

procedure coincidences(a: Sequence<int>, b: Sequence<int>) returns (r: int)
  requires strictlyIncreasing(a)
  requires strictlyIncreasing(b)
  requires commonAxioms()
  opaque
  ensures r == common(a, b, seqLength(a))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var i: int := 0;
  var j: int := 0;
  var c: int := 0;
  while (i < seqLength(a) && j < seqLength(b))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant 0 <= j
    invariant j <= seqLength(b)
    invariant c == common(a, b, i)
    invariant bBelowAi(a, b, i, j)
    invariant aBelowBj(a, b, i, j)
  {
    if seqSelect(a, i) == seqSelect(b, j) then {
      c := c + 1;
      i := i + 1;
      j := j + 1
    } else if seqSelect(a, i) < seqSelect(b, j) then {
      i := i + 1
    } else {
      j := j + 1
    }
  };
  r := c
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure strictlyIncreasing(s: Sequence<int>): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i < j ==> j < seqLength(s) ==> seqSelect(s, i) < seqSelect(s, j)
};

procedure contains(b: Sequence<int>, x: int): bool
{
  exists(k: int) => 0 <= k && k < seqLength(b) && seqSelect(b, k) == x
};

procedure common(a: Sequence<int>, b: Sequence<int>, hi: int): int;

procedure commonAxioms(): bool
{
  (forall(a: Sequence<int>) => forall(b: Sequence<int>) => common(a, b, 0) == 0)
  && (forall(a: Sequence<int>) => forall(b: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(a) ==>
        common(a, b, h) == common(a, b, h - 1) + (if contains(b, seqSelect(a, h - 1)) then 1 else 0))
};

procedure bBelowAi(a: Sequence<int>, b: Sequence<int>, i: int, j: int): bool
{
  0 <= i ==> i < seqLength(a) ==>
    (forall(m: int) => 0 <= m ==> m < j ==> m < seqLength(b) ==> seqSelect(b, m) < seqSelect(a, i))
};

procedure aBelowBj(a: Sequence<int>, b: Sequence<int>, i: int, j: int): bool
{
  0 <= j ==> j < seqLength(b) ==>
    (forall(k: int) => 0 <= k ==> k < i ==> k < seqLength(a) ==> seqSelect(a, k) < seqSelect(b, j))
};

procedure coincidences(a: Sequence<int>, b: Sequence<int>) returns (r: int)
  requires strictlyIncreasing(a)
  requires strictlyIncreasing(b)
  requires commonAxioms()
  opaque
  ensures r == common(a, b, seqLength(a))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var i: int := 0;
  var j: int := 0;
  var c: int := 0;
  while (i < seqLength(a) && j < seqLength(b))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant 0 <= j
    invariant j <= seqLength(b)
    invariant c == common(a, b, i)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant bBelowAi(a, b, i, j)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant aBelowBj(a, b, i, j)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  {
    if seqSelect(a, i) == seqSelect(b, j) then {
      c := c + 1;
      i := i + 1;
      j := j + 1
    } else if seqSelect(a, i) > seqSelect(b, j) then {
      i := i + 1
    } else {
      j := j + 1
    }
  };
  r := c
};
#end
