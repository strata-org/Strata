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

procedure bytes(s: Sequence<int>): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(s) ==> 0 <= seqSelect(s, k) && seqSelect(s, k) <= 255
};

procedure sumA(s: Sequence<int>, n: int): int;
procedure sumB(s: Sequence<int>, n: int): int;

procedure adlerAxioms(): bool
{
  (forall(s: Sequence<int>) => sumA(s, 0) == 1 && sumB(s, 0) == 0)
  && (forall(s: Sequence<int>) => forall(n: int) => 1 <= n ==> n <= seqLength(s) ==>
        sumA(s, n) == (sumA(s, n - 1) + seqSelect(s, n - 1)) % 65521
        && sumB(s, n) == (sumB(s, n - 1) + sumA(s, n)) % 65521)
};

procedure checksum(data: Sequence<int>) returns (r: int)
  requires bytes(data)
  requires adlerAxioms()
  opaque
  ensures r == sumB(data, seqLength(data)) * 65536 + sumA(data, seqLength(data))
{
  var a: int := 1;
  var b: int := 0;
  var i: int := 0;
  while (i < seqLength(data))
    invariant 0 <= i
    invariant i <= seqLength(data)
    invariant a == sumA(data, i)
    invariant b == sumB(data, i)
  {
    a := (a + seqSelect(data, i)) % 65521;
    b := (b + a) % 65521;
    i := i + 1
  };
  r := b * 65536 + a
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure bytes(s: Sequence<int>): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(s) ==> 0 <= seqSelect(s, k) && seqSelect(s, k) <= 255
};

procedure sumA(s: Sequence<int>, n: int): int;
procedure sumB(s: Sequence<int>, n: int): int;

procedure adlerAxioms(): bool
{
  (forall(s: Sequence<int>) => sumA(s, 0) == 1 && sumB(s, 0) == 0)
  && (forall(s: Sequence<int>) => forall(n: int) => 1 <= n ==> n <= seqLength(s) ==>
        sumA(s, n) == (sumA(s, n - 1) + seqSelect(s, n - 1)) % 65521
        && sumB(s, n) == (sumB(s, n - 1) + sumA(s, n)) % 65521)
};

procedure checksum(data: Sequence<int>) returns (r: int)
  requires bytes(data)
  requires adlerAxioms()
  opaque
  ensures r == sumB(data, seqLength(data)) * 65536 + sumA(data, seqLength(data))
{
  var a: int := 1;
  var b: int := 0;
  var i: int := 0;
  while (i < seqLength(data))
    invariant 0 <= i
    invariant i <= seqLength(data)
    invariant a == sumA(data, i)
    invariant b == sumB(data, i)
//            ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  {
    a := (a + seqSelect(data, i)) % 65521;
    b := (b + seqSelect(data, i)) % 65521;
    i := i + 1
  };
  r := b * 65536 + a
};
#end
