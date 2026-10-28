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

procedure boundsBelow(a: Sequence<int>, m: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(a) ==> seqSelect(a, k) <= m
};

procedure occursBelow(a: Sequence<int>, m: int, hi: int): bool
{
  exists(k: int) => 0 <= k && k < hi && k < seqLength(a) && seqSelect(a, k) == m
};

procedure maximum(a: Sequence<int>) returns (r: int)
  requires seqLength(a) > 0
  opaque
  ensures boundsBelow(a, r, seqLength(a))
  ensures occursBelow(a, r, seqLength(a))
{
  var m: int := seqSelect(a, 0);
  var i: int := 1;
  while (i < seqLength(a))
    invariant 1 <= i
    invariant i <= seqLength(a)
    invariant boundsBelow(a, m, i)
    invariant occursBelow(a, m, i)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    if seqSelect(a, i) > m then { m := seqSelect(a, i) };
    i := i + 1
  };
  r := m
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure boundsBelow(a: Sequence<int>, m: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(a) ==> seqSelect(a, k) <= m
};

procedure occursBelow(a: Sequence<int>, m: int, hi: int): bool
{
  exists(k: int) => 0 <= k && k < hi && k < seqLength(a) && seqSelect(a, k) == m
};

procedure maximum(a: Sequence<int>) returns (r: int)
  requires seqLength(a) > 0
  opaque
  ensures boundsBelow(a, r, seqLength(a))
  ensures occursBelow(a, r, seqLength(a))
{
  var m: int := seqSelect(a, 0);
  var i: int := 1;
  while (i < seqLength(a))
    invariant 1 <= i
    invariant i <= seqLength(a)
    invariant boundsBelow(a, m, i)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant occursBelow(a, m, i)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    if seqSelect(a, i) < m then { m := seqSelect(a, i) };
    i := i + 1
  };
  r := m
};
#end
