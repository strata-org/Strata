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

procedure wellFormed(n: int, eu: Sequence<int>, ev: Sequence<int>, ew: Sequence<int>): bool
{
  seqLength(eu) == seqLength(ev) && seqLength(ev) == seqLength(ew)
  && (forall(e: int) => 0 <= e ==> e < seqLength(eu) ==>
        0 <= seqSelect(eu, e) && seqSelect(eu, e) < n && 0 <= seqSelect(ev, e) && seqSelect(ev, e) < n)
};

procedure relaxedBelow(dist: Sequence<int>, reach: Sequence<bool>, eu: Sequence<int>, ev: Sequence<int>, ew: Sequence<int>, hi: int): bool
{
  forall(e: int) => 0 <= e ==> e < hi ==> e < seqLength(eu) ==> e < seqLength(ev) ==> e < seqLength(ew) ==>
    0 <= seqSelect(eu, e) ==> seqSelect(eu, e) < seqLength(dist) ==> seqSelect(eu, e) < seqLength(reach) ==>
    0 <= seqSelect(ev, e) ==> seqSelect(ev, e) < seqLength(dist) ==> seqSelect(ev, e) < seqLength(reach) ==>
    seqSelect(reach, seqSelect(eu, e)) ==>
      (seqSelect(reach, seqSelect(ev, e))
       && seqSelect(dist, seqSelect(ev, e)) <= seqSelect(dist, seqSelect(eu, e)) + seqSelect(ew, e))
};

procedure bellmanFord(n: int, eu: Sequence<int>, ev: Sequence<int>, ew: Sequence<int>, src: int)
  returns (ok: bool, dist: Sequence<int>, reach: Sequence<bool>)
  requires 1 <= n
  requires wellFormed(n, eu, ev, ew)
  requires 0 <= src
  requires src < n
  opaque
  ensures seqLength(dist) == n
  ensures seqLength(reach) == n
  ensures ok ==> relaxedBelow(dist, reach, eu, ev, ew, seqLength(eu))
{
  var d: Sequence<int> := seqEmpty();
  var rc: Sequence<bool> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(d) == x
    invariant seqLength(rc) == x
  {
    d := seqBuild(d, 0);
    rc := seqBuild(rc, x == src);
    x := x + 1
  };
  var round: int := 1;
  while (round < n)
    invariant 1 <= round
    invariant seqLength(d) == n
    invariant seqLength(rc) == n
  {
    var e: int := 0;
    while (e < seqLength(eu))
      invariant 0 <= e
      invariant e <= seqLength(eu)
      invariant seqLength(d) == n
      invariant seqLength(rc) == n
    {
      var u: int := seqSelect(eu, e);
      var v: int := seqSelect(ev, e);
      if seqSelect(rc, u) && (!seqSelect(rc, v) || seqSelect(d, u) + seqSelect(ew, e) < seqSelect(d, v)) then {
        d := seqUpdate(d, v, seqSelect(d, u) + seqSelect(ew, e));
        rc := seqUpdate(rc, v, true)
      };
      e := e + 1
    };
    round := round + 1
  };
  var good: bool := true;
  var e: int := 0;
  while (e < seqLength(eu) && good)
    invariant 0 <= e
    invariant e <= seqLength(eu)
    invariant good ==> relaxedBelow(d, rc, eu, ev, ew, e)
  {
    var u: int := seqSelect(eu, e);
    var v: int := seqSelect(ev, e);
    if seqSelect(rc, u) && (!seqSelect(rc, v) || seqSelect(d, u) + seqSelect(ew, e) < seqSelect(d, v)) then {
      good := false
    } else {
      e := e + 1
    }
  };
  ok := good;
  dist := d;
  reach := rc
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure wellFormed(n: int, eu: Sequence<int>, ev: Sequence<int>, ew: Sequence<int>): bool
{
  seqLength(eu) == seqLength(ev) && seqLength(ev) == seqLength(ew)
  && (forall(e: int) => 0 <= e ==> e < seqLength(eu) ==>
        0 <= seqSelect(eu, e) && seqSelect(eu, e) < n)
};

procedure relaxedBelow(dist: Sequence<int>, reach: Sequence<bool>, eu: Sequence<int>, ev: Sequence<int>, ew: Sequence<int>, hi: int): bool
{
  forall(e: int) => 0 <= e ==> e < hi ==> e < seqLength(eu) ==> e < seqLength(ev) ==> e < seqLength(ew) ==>
    0 <= seqSelect(eu, e) ==> seqSelect(eu, e) < seqLength(dist) ==> seqSelect(eu, e) < seqLength(reach) ==>
    0 <= seqSelect(ev, e) ==> seqSelect(ev, e) < seqLength(dist) ==> seqSelect(ev, e) < seqLength(reach) ==>
    seqSelect(reach, seqSelect(eu, e)) ==>
      (seqSelect(reach, seqSelect(ev, e))
       && seqSelect(dist, seqSelect(ev, e)) <= seqSelect(dist, seqSelect(eu, e)) + seqSelect(ew, e))
};

procedure bellmanFord(n: int, eu: Sequence<int>, ev: Sequence<int>, ew: Sequence<int>, src: int)
  returns (ok: bool, dist: Sequence<int>, reach: Sequence<bool>)
  requires 1 <= n
  requires wellFormed(n, eu, ev, ew)
  requires 0 <= src
  requires src < n
  opaque
  ensures seqLength(dist) == n
  ensures seqLength(reach) == n
  ensures ok ==> relaxedBelow(dist, reach, eu, ev, ew, seqLength(eu))
{
  var d: Sequence<int> := seqEmpty();
  var rc: Sequence<bool> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(d) == x
    invariant seqLength(rc) == x
  {
    d := seqBuild(d, 0);
    rc := seqBuild(rc, x == src);
    x := x + 1
  };
  var round: int := 1;
  while (round < n)
    invariant 1 <= round
    invariant seqLength(d) == n
    invariant seqLength(rc) == n
  {
    var e: int := 0;
    while (e < seqLength(eu))
      invariant 0 <= e
      invariant e <= seqLength(eu)
      invariant seqLength(d) == n
      invariant seqLength(rc) == n
    {
      var u: int := seqSelect(eu, e);
      var v: int := seqSelect(ev, e);
      if seqSelect(rc, u) && (!seqSelect(rc, v) || seqSelect(d, u) + seqSelect(ew, e) < seqSelect(d, v)) then {
//                             ^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                                      ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
        d := seqUpdate(d, v, seqSelect(d, u) + seqSelect(ew, e));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
        rc := seqUpdate(rc, v, true)
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
      };
      e := e + 1
    };
    round := round + 1
  };
  var good: bool := true;
  var e: int := 0;
  while (e < seqLength(eu) && good)
    invariant 0 <= e
    invariant e <= seqLength(eu)
    invariant good ==> relaxedBelow(d, rc, eu, ev, ew, e)
  {
    var u: int := seqSelect(eu, e);
    var v: int := seqSelect(ev, e);
    if seqSelect(rc, u) && (!seqSelect(rc, v) || seqSelect(d, u) + seqSelect(ew, e) < seqSelect(d, v)) then {
//                           ^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                                    ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
      good := false
    } else {
      e := e + 1
    }
  };
  ok := good;
  dist := d;
  reach := rc
};
#end
