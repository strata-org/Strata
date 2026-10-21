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

procedure bucketOf(key: int, n: int): int
  requires n > 0
{
  ((key % n) + n) % n
};

procedure placed(t: Sequence<Sequence<int>>): bool
{
  seqLength(t) > 0
  && (forall(b: int) => forall(k: int) => 0 <= b ==> b < seqLength(t) ==> 0 <= k ==> k < seqLength(seqSelect(t, b)) ==>
        bucketOf(seqSelect(seqSelect(t, b), k), seqLength(t)) == b)
};

procedure inChain(c: Sequence<int>, key: int): bool
{
  exists(k: int) => 0 <= k && k < seqLength(c) && seqSelect(c, k) == key
};

procedure put(t: Sequence<Sequence<int>>, key: int) returns (res: Sequence<Sequence<int>>)
  requires placed(t)
  opaque
  ensures seqLength(res) == seqLength(t)
  ensures placed(res)
//        ^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures inChain(seqSelect(res, bucketOf(key, seqLength(t))), key)
{
  var b: int := bucketOf(key, seqLength(t));
  var c: Sequence<int> := seqSelect(t, b);
  if inChain(c, key) then { res := t }
  else { res := seqUpdate(t, b, seqBuild(c, key)) }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure bucketOf(key: int, n: int): int
  requires n > 0
{
  ((key % n) + n) % n
};

procedure placed(t: Sequence<Sequence<int>>): bool
{
  seqLength(t) > 0
  && (forall(b: int) => forall(k: int) => 0 <= b ==> b < seqLength(t) ==> 0 <= k ==> k < seqLength(seqSelect(t, b)) ==>
        bucketOf(seqSelect(seqSelect(t, b), k), seqLength(t)) == b)
};

procedure inChain(c: Sequence<int>, key: int): bool
{
  exists(k: int) => 0 <= k && k < seqLength(c) && seqSelect(c, k) == key
};

procedure put(t: Sequence<Sequence<int>>, key: int) returns (res: Sequence<Sequence<int>>)
  requires placed(t)
  opaque
  ensures seqLength(res) == seqLength(t)
  ensures placed(res)
//        ^^^^^^^^^^^ error: postcondition could not be proved
  ensures inChain(seqSelect(res, bucketOf(key, seqLength(t))), key)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
{
  var b: int := bucketOf(key, seqLength(t));
  var c: Sequence<int> := seqSelect(t, b);
  if inChain(c, key) then { res := t }
  else { res := seqUpdate(t, 0, seqBuild(seqSelect(t, 0), key)) }
};
#end
