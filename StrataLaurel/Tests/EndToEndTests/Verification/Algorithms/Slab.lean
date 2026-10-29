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

composite Slab {
  var values: Sequence<int>
  var occupied: Sequence<bool>
  var nextFree: Sequence<int>
  var freeHead: int
}

procedure wellFormed(s: Slab): bool
{
  seqLength(s#values) == seqLength(s#occupied) && seqLength(s#occupied) == seqLength(s#nextFree)
  && -1 <= s#freeHead && s#freeHead < seqLength(s#occupied)
  && (s#freeHead != -1 ==> !seqSelect(s#occupied, s#freeHead))
};

procedure insert(s: Slab, v: int) returns (key: int)
  requires wellFormed(s)
  opaque
  ensures wellFormed(s)
  ensures 0 <= key && key < seqLength(s#occupied)
  ensures seqSelect(s#occupied, key) && seqSelect(s#values, key) == v
  modifies s
{
  if s#freeHead != -1 then {
    var k: int := s#freeHead;
    var nf: int := seqSelect(s#nextFree, k);
    s#values := seqUpdate(s#values, k, v);
    s#occupied := seqUpdate(s#occupied, k, true);
    s#freeHead := if 0 <= nf && nf < seqLength(s#occupied) && !seqSelect(s#occupied, nf) then nf else -1;
    key := k
  } else {
    var k: int := seqLength(s#values);
    s#values := seqBuild(s#values, v);
    s#occupied := seqBuild(s#occupied, true);
    s#nextFree := seqBuild(s#nextFree, -1);
    key := k
  }
};

procedure remove(s: Slab, key: int) returns (v: int)
  requires wellFormed(s)
  requires 0 <= key && key < seqLength(s#occupied)
  requires seqSelect(s#occupied, key)
  opaque
  ensures wellFormed(s)
  ensures v == old(seqSelect(s#values, key))
  ensures !seqSelect(s#occupied, key)
//         ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
  modifies s
{
  v := seqSelect(s#values, key);
  s#occupied := seqUpdate(s#occupied, key, false);
  s#nextFree := seqUpdate(s#nextFree, key, s#freeHead);
  s#freeHead := key
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite Slab {
  var values: Sequence<int>
  var occupied: Sequence<bool>
  var nextFree: Sequence<int>
  var freeHead: int
}

procedure wellFormed(s: Slab): bool
{
  seqLength(s#values) == seqLength(s#occupied) && seqLength(s#occupied) == seqLength(s#nextFree)
  && -1 <= s#freeHead && s#freeHead < seqLength(s#occupied)
  && (s#freeHead != -1 ==> !seqSelect(s#occupied, s#freeHead))
};

procedure insert(s: Slab, v: int) returns (key: int)
  requires wellFormed(s)
  opaque
  ensures wellFormed(s)
  ensures 0 <= key && key < seqLength(s#occupied)
  ensures seqSelect(s#occupied, key) && seqSelect(s#values, key) == v
  modifies s
{
  if s#freeHead != -1 then {
    var k: int := s#freeHead;
    var nf: int := seqSelect(s#nextFree, k);
    s#values := seqUpdate(s#values, k, v);
    s#occupied := seqUpdate(s#occupied, k, true);
    s#freeHead := if 0 <= nf && nf < seqLength(s#occupied) && !seqSelect(s#occupied, nf) then nf else -1;
    key := k
  } else {
    var k: int := seqLength(s#values);
    s#values := seqBuild(s#values, v);
    s#occupied := seqBuild(s#occupied, true);
    s#nextFree := seqBuild(s#nextFree, -1);
    key := k
  }
};

procedure remove(s: Slab, key: int) returns (v: int)
  requires wellFormed(s)
  requires 0 <= key && key < seqLength(s#occupied)
  requires seqSelect(s#occupied, key)
  opaque
  ensures wellFormed(s)
//        ^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures v == old(seqSelect(s#values, key))
  ensures !seqSelect(s#occupied, key)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
//         ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: postcondition does not hold
  modifies s
{
  v := seqSelect(s#values, key);
  s#nextFree := seqUpdate(s#nextFree, key, s#freeHead);
  s#freeHead := key
};
#end
