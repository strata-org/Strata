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

procedure sortedBetween(s: Sequence<int>, lo: int, hi: int): bool
{
  forall(i: int) => forall(j: int) =>
    0 <= lo ==> lo <= i ==> i <= j ==> j < hi ==> hi <= seqLength(s) ==> seqSelect(s, i) <= seqSelect(s, j)
};

procedure absentIn(a: Sequence<int>, key: int, lo: int, hi: int): bool
{
  forall(k: int) => lo <= k ==> k < hi ==> 0 <= k ==> k < seqLength(a) ==> seqSelect(a, k) != key
};

procedure binarySearch(a: Sequence<int>, key: int) returns (r: int)
  requires sortedBetween(a, 0, seqLength(a))
  opaque
  ensures (r == -1 && absentIn(a, key, 0, seqLength(a)))
       || (0 <= r && r < seqLength(a) && seqSelect(a, r) == key)
{
  var lo: int := 0;
  var hi: int := seqLength(a);
  var found: int := -1;
  while (lo < hi && found == -1)
    invariant 0 <= lo
    invariant lo <= hi
    invariant hi <= seqLength(a)
    invariant found == -1 || (0 <= found && found < seqLength(a) && seqSelect(a, found) == key)
    invariant found == -1 ==> absentIn(a, key, 0, lo)
    invariant found == -1 ==> absentIn(a, key, hi, seqLength(a))
  {
    var mid: int := lo + (hi - lo) / 2;
    if seqSelect(a, mid) < key then { lo := mid + 1 }
    else if seqSelect(a, mid) > key then { hi := mid }
    else { found := mid }
  };
  r := found
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure sortedBetween(s: Sequence<int>, lo: int, hi: int): bool
{
  forall(i: int) => forall(j: int) =>
    0 <= lo ==> lo <= i ==> i <= j ==> j < hi ==> hi <= seqLength(s) ==> seqSelect(s, i) <= seqSelect(s, j)
};

procedure absentIn(a: Sequence<int>, key: int, lo: int, hi: int): bool
{
  forall(k: int) => lo <= k ==> k < hi ==> 0 <= k ==> k < seqLength(a) ==> seqSelect(a, k) != key
};

procedure binarySearch(a: Sequence<int>, key: int) returns (r: int)
  requires sortedBetween(a, 0, seqLength(a))
  opaque
  ensures (r == -1 && absentIn(a, key, 0, seqLength(a)))
       || (0 <= r && r < seqLength(a) && seqSelect(a, r) == key)
{
  var lo: int := 0;
  var hi: int := seqLength(a);
  var found: int := -1;
  while (lo < hi && found == -1)
    invariant 0 <= lo
    invariant lo <= hi
//            ^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant hi <= seqLength(a)
    invariant found == -1 || (0 <= found && found < seqLength(a) && seqSelect(a, found) == key)
    invariant found == -1 ==> absentIn(a, key, 0, lo)
    invariant found == -1 ==> absentIn(a, key, hi, seqLength(a))
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  {
    var mid: int := lo + (hi - lo) / 2;
    if seqSelect(a, mid) < key then { lo := mid + 1 }
    else if seqSelect(a, mid) > key then { hi := mid - 1 }
    else { found := mid }
  };
  r := found
};
#end
