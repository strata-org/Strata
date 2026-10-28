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

procedure ones(s: Sequence<bool>, hi: int): int;

procedure onesAxioms(): bool
{
  (forall(s: Sequence<bool>) => ones(s, 0) == 0)
  && (forall(s: Sequence<bool>) => forall(h: int) => 1 <= h ==> h <= seqLength(s) ==>
        ones(s, h) == ones(s, h - 1) + (if seqSelect(s, h - 1) then 1 else 0))
};

procedure countOnes(a: Sequence<bool>) returns (r: int)
  requires onesAxioms()
  opaque
  ensures r == ones(a, seqLength(a))
{
  var c: int := 0;
  var i: int := 0;
  while (i < seqLength(a))
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant c == ones(a, i)
  {
    if seqSelect(a, i) then { c := c + 1 };
    i := i + 1
  };
  r := c
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure ones(s: Sequence<bool>, hi: int): int;

procedure onesAxioms(): bool
{
  (forall(s: Sequence<bool>) => ones(s, 0) == 0)
  && (forall(s: Sequence<bool>) => forall(h: int) => 1 <= h ==> h <= seqLength(s) ==>
        ones(s, h) == ones(s, h - 1) + (if seqSelect(s, h - 1) then 1 else 0))
};

procedure countOnes(a: Sequence<bool>) returns (r: int)
  requires onesAxioms()
  opaque
  ensures r == ones(a, seqLength(a))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
{
  var c: int := 0;
  var i: int := 0;
  while (i < seqLength(a) - 1)
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant c == ones(a, i)
  {
    if seqSelect(a, i) then { c := c + 1 };
    i := i + 1
  };
  r := c
};
#end
