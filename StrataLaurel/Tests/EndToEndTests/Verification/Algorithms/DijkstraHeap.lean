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

procedure weights(w: Sequence<Sequence<int>>, n: int): bool
{
  seqLength(w) == n
  && (forall(u: int) => 0 <= u ==> u < n ==> seqLength(seqSelect(w, u)) == n)
  && (forall(u: int) => forall(v: int) => 0 <= u ==> u < n ==> 0 <= v ==> v < n ==> seqSelect(seqSelect(w, u), v) >= -1)
};

procedure relaxed(w: Sequence<Sequence<int>>, d: Sequence<int>, reach: Sequence<bool>, n: int): bool
{
  forall(u: int) => forall(v: int) => 0 <= u ==> u < n ==> 0 <= v ==> v < n ==> u < seqLength(reach) ==> v < seqLength(reach) ==>
    seqSelect(reach, u) ==> seqSelect(seqSelect(w, u), v) >= 0 ==>
//                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                    ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      seqSelect(reach, v) && seqSelect(d, v) <= seqSelect(d, u) + seqSelect(seqSelect(w, u), v)
//                           ^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                              ^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                          ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
};

procedure heapOrdered(key: Sequence<int>): bool
{
  forall(k: int) => 0 < k ==> k < seqLength(key) ==> seqSelect(key, (k - 1) / 2) <= seqSelect(key, k)
};

procedure push(key: Sequence<int>, vert: Sequence<int>, k: int, v: int) returns (key2: Sequence<int>, vert2: Sequence<int>)
  requires seqLength(key) == seqLength(vert)
  requires heapOrdered(key)
  opaque
  ensures seqLength(key2) == seqLength(key) + 1
  ensures seqLength(vert2) == seqLength(key2)
  ensures heapOrdered(key2)
{
  var ks: Sequence<int> := seqBuild(key, k);
  var vs: Sequence<int> := seqBuild(vert, v);
  var i: int := seqLength(key);
  while (i > 0 && seqSelect(ks, (i - 1) / 2) > seqSelect(ks, i))
    invariant 0 <= i
//            ^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant i < seqLength(ks)
    invariant seqLength(vs) == seqLength(ks)
  {
    var p: int := (i - 1) / 2;
    var tk: int := seqSelect(ks, p);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    ks := seqUpdate(seqUpdate(ks, p, seqSelect(ks, i)), i, tk);
//                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    var tv: int := seqSelect(vs, p);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    vs := seqUpdate(seqUpdate(vs, p, seqSelect(vs, i)), i, tv);
//                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    i := p
  };
  key2 := ks;
  vert2 := vs
};

procedure pop(key: Sequence<int>, vert: Sequence<int>) returns (key2: Sequence<int>, vert2: Sequence<int>)
  requires seqLength(key) == seqLength(vert)
  requires seqLength(key) > 0
  requires heapOrdered(key)
  opaque
  ensures seqLength(key2) == seqLength(key) - 1
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures seqLength(vert2) == seqLength(key2)
  ensures heapOrdered(key2)
//        ^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var last: int := seqLength(key) - 1;
  var ks: Sequence<int> := seqTake(seqUpdate(key, 0, seqSelect(key, last)), last);
  var vs: Sequence<int> := seqTake(seqUpdate(vert, 0, seqSelect(vert, last)), last);
  var i: int := 0;
  var done: bool := false;
  while (2 * i + 1 < seqLength(ks) && !done)
    invariant 0 <= i
    invariant seqLength(vs) == seqLength(ks)
  {
    var c: int := 2 * i + 1;
    if c + 1 < seqLength(ks) && seqSelect(ks, c + 1) < seqSelect(ks, c) then { c := c + 1 };
    if seqSelect(ks, i) <= seqSelect(ks, c) then { done := true }
    else {
      var tk: int := seqSelect(ks, i);
      ks := seqUpdate(seqUpdate(ks, i, seqSelect(ks, c)), c, tk);
      var tv: int := seqSelect(vs, i);
      vs := seqUpdate(seqUpdate(vs, i, seqSelect(vs, c)), c, tv);
      i := c
    }
  };
  key2 := ks;
  vert2 := vs
};

procedure shortestPaths(w: Sequence<Sequence<int>>, n: int, src: int) returns (d: Sequence<int>, reach: Sequence<bool>)
  requires 1 <= n
  requires weights(w, n)
  requires 0 <= src && src < n
  opaque
  ensures seqLength(d) == n
  ensures seqLength(reach) == n
  ensures relaxed(w, d, reach, n)
//        ^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var dist: Sequence<int> := seqEmpty();
  var rc: Sequence<bool> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(dist) == x
    invariant seqLength(rc) == x
  {
    dist := seqBuild(dist, 0);
    rc := seqBuild(rc, x == src);
    x := x + 1
  };
  var key: Sequence<int> := seqEmpty();
  var vert: Sequence<int> := seqEmpty();
  assign key, vert := push(key, vert, 0, src);
  while (seqLength(key) > 0)
    invariant seqLength(dist) == n
    invariant seqLength(rc) == n
    invariant seqLength(vert) == seqLength(key)
    invariant heapOrdered(key)
//            ^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var u: int := seqSelect(vert, 0);
    var du: int := seqSelect(key, 0);
    assign key, vert := pop(key, vert);
    if du == seqSelect(dist, u) then {
//           ^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      var v: int := 0;
      while (v < n)
        invariant 0 <= v
        invariant seqLength(dist) == n
        invariant seqLength(rc) == n
        invariant seqLength(vert) == seqLength(key)
      {
        var wt: int := seqSelect(seqSelect(w, u), v);
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                               ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        if wt >= 0 && (!seqSelect(rc, v) || seqSelect(dist, u) + wt < seqSelect(dist, v)) then {
//                                          ^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
          dist := seqUpdate(dist, v, seqSelect(dist, u) + wt);
//                                   ^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
          rc := seqUpdate(rc, v, true);
          assign key, vert := push(key, vert, seqSelect(dist, v), v)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        };
        v := v + 1
      }
    }
  };
  d := dist;
  reach := rc
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure weights(w: Sequence<Sequence<int>>, n: int): bool
{
  seqLength(w) == n
  && (forall(u: int) => 0 <= u ==> u < n ==> seqLength(seqSelect(w, u)) == n)
  && (forall(u: int) => forall(v: int) => 0 <= u ==> u < n ==> 0 <= v ==> v < n ==> seqSelect(seqSelect(w, u), v) >= -1)
};

procedure relaxed(w: Sequence<Sequence<int>>, d: Sequence<int>, reach: Sequence<bool>, n: int): bool
{
  forall(u: int) => forall(v: int) => 0 <= u ==> u < n ==> 0 <= v ==> v < n ==> u < seqLength(reach) ==> v < seqLength(reach) ==>
    seqSelect(reach, u) ==> seqSelect(seqSelect(w, u), v) >= 0 ==>
//                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                    ^^^^^^^^^^^^^^^ error: precondition could not be proved
      seqSelect(reach, v) && seqSelect(d, v) <= seqSelect(d, u) + seqSelect(seqSelect(w, u), v)
//                           ^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                              ^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                          ^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure heapOrdered(key: Sequence<int>): bool
{
  forall(k: int) => 0 < k ==> k < seqLength(key) ==> seqSelect(key, (k - 1) / 2) <= seqSelect(key, k)
};

procedure push(key: Sequence<int>, vert: Sequence<int>, k: int, v: int) returns (key2: Sequence<int>, vert2: Sequence<int>)
  requires seqLength(key) == seqLength(vert)
  requires heapOrdered(key)
  opaque
  ensures seqLength(key2) == seqLength(key) + 1
  ensures seqLength(vert2) == seqLength(key2)
  ensures heapOrdered(key2)
{
  var ks: Sequence<int> := seqBuild(key, k);
  var vs: Sequence<int> := seqBuild(vert, v);
  var i: int := seqLength(key);
  while (i > 0 && seqSelect(ks, (i - 1) / 2) > seqSelect(ks, i))
    invariant 0 <= i
//            ^^^^^^ error: assertion could not be proved
    invariant i < seqLength(ks)
    invariant seqLength(vs) == seqLength(ks)
  {
    var p: int := (i - 1) / 2;
    var tk: int := seqSelect(ks, p);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    ks := seqUpdate(seqUpdate(ks, p, seqSelect(ks, i)), i, tk);
//                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    var tv: int := seqSelect(vs, p);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    vs := seqUpdate(seqUpdate(vs, p, seqSelect(vs, i)), i, tv);
//                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    i := p
  };
  key2 := ks;
  vert2 := vs
};

procedure pop(key: Sequence<int>, vert: Sequence<int>) returns (key2: Sequence<int>, vert2: Sequence<int>)
  requires seqLength(key) == seqLength(vert)
  requires seqLength(key) > 0
  requires heapOrdered(key)
  opaque
  ensures seqLength(key2) == seqLength(key) - 1
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures seqLength(vert2) == seqLength(key2)
  ensures heapOrdered(key2)
//        ^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var last: int := seqLength(key) - 1;
  var ks: Sequence<int> := seqTake(seqUpdate(key, 0, seqSelect(key, last)), last);
  var vs: Sequence<int> := seqTake(seqUpdate(vert, 0, seqSelect(vert, last)), last);
  var i: int := 0;
  var done: bool := false;
  while (2 * i + 1 < seqLength(ks) && !done)
    invariant 0 <= i
    invariant seqLength(vs) == seqLength(ks)
  {
    var c: int := 2 * i + 1;
    if c + 1 < seqLength(ks) && seqSelect(ks, c + 1) < seqSelect(ks, c) then { c := c + 1 };
    if seqSelect(ks, i) <= seqSelect(ks, c) then { done := true }
    else {
      var tk: int := seqSelect(ks, i);
      ks := seqUpdate(seqUpdate(ks, i, seqSelect(ks, c)), c, tk);
      var tv: int := seqSelect(vs, i);
      vs := seqUpdate(seqUpdate(vs, i, seqSelect(vs, c)), c, tv);
      i := c
    }
  };
  key2 := ks;
  vert2 := vs
};

procedure shortestPaths(w: Sequence<Sequence<int>>, n: int, src: int) returns (d: Sequence<int>, reach: Sequence<bool>)
  requires 1 <= n
  requires weights(w, n)
  requires 0 <= src && src < n
  opaque
  ensures seqLength(d) == n
  ensures seqLength(reach) == n
  ensures relaxed(w, d, reach, n)
//        ^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition could not be proved
{
  var dist: Sequence<int> := seqEmpty();
  var rc: Sequence<bool> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(dist) == x
    invariant seqLength(rc) == x
  {
    dist := seqBuild(dist, 0);
    rc := seqBuild(rc, x == src);
    x := x + 1
  };
  var key: Sequence<int> := seqEmpty();
  var vert: Sequence<int> := seqEmpty();
  assign key, vert := push(key, vert, 0, src);
  while (seqLength(key) > 0)
    invariant seqLength(dist) == n
    invariant seqLength(rc) == n
    invariant seqLength(vert) == seqLength(key)
    invariant heapOrdered(key)
//            ^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var u: int := seqSelect(vert, 0);
    var du: int := seqSelect(key, 0);
    assign key, vert := pop(key, vert);
    if du == seqSelect(dist, u) then {
//           ^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
      var v: int := 0;
      while (v < n)
        invariant 0 <= v
        invariant seqLength(dist) == n
        invariant seqLength(rc) == n
        invariant seqLength(vert) == seqLength(key)
      {
        var wt: int := seqSelect(seqSelect(w, u), v);
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                               ^^^^^^^^^^^^^^^ error: precondition could not be proved
        if wt > 0 && (!seqSelect(rc, v) || seqSelect(dist, u) + wt < seqSelect(dist, v)) then {
//                                         ^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
          dist := seqUpdate(dist, v, seqSelect(dist, u) + wt);
//                                   ^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
          rc := seqUpdate(rc, v, true);
          assign key, vert := push(key, vert, seqSelect(dist, v), v)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
        };
        v := v + 1
      }
    }
  };
  d := dist;
  reach := rc
};
#end
