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

procedure absentBelow(a: Sequence<int>, key: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(a) ==> seqSelect(a, k) != key
};

procedure linearSearch(a: Sequence<int>, key: int) returns (r: int)
  opaque
  ensures (r == -1 && absentBelow(a, key, seqLength(a)))
       || (0 <= r && r < seqLength(a) && seqSelect(a, r) == key)
{
  var i: int := 0;
  var found: bool := false;
  while (i < seqLength(a) && !found)
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant found ==> i < seqLength(a) && seqSelect(a, i) == key
    invariant absentBelow(a, key, i)
  {
    if seqSelect(a, i) == key then { found := true } else { i := i + 1 }
  };
  if found then { r := i } else { r := -1 }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure absentBelow(a: Sequence<int>, key: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(a) ==> seqSelect(a, k) != key
};

procedure linearSearch(a: Sequence<int>, key: int) returns (r: int)
  opaque
  ensures (r == -1 && absentBelow(a, key, seqLength(a)))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
       || (0 <= r && r < seqLength(a) && seqSelect(a, r) == key)
{
  var i: int := 0;
  var found: bool := false;
  while (i < seqLength(a) - 1 && !found)
    invariant 0 <= i
    invariant i <= seqLength(a)
    invariant found ==> i < seqLength(a) && seqSelect(a, i) == key
    invariant absentBelow(a, key, i)
  {
    if seqSelect(a, i) == key then { found := true } else { i := i + 1 }
  };
  if found then { r := i } else { r := -1 }
};
#end
