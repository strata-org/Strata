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

procedure wellFormed(adj: Sequence<Sequence<int>>): bool
{
  forall(u: int) => forall(k: int) => 0 <= u ==> u < seqLength(adj) ==> 0 <= k ==> k < seqLength(seqSelect(adj, u)) ==>
    0 <= seqSelect(seqSelect(adj, u), k) && seqSelect(seqSelect(adj, u), k) < seqLength(adj)
};

procedure edge(adj: Sequence<Sequence<int>>, u: int, v: int): bool
{
  0 <= u && u < seqLength(adj) && (exists(k: int) => 0 <= k && k < seqLength(seqSelect(adj, u)) && seqSelect(seqSelect(adj, u), k) == v)
};

procedure justified(adj: Sequence<Sequence<int>>, vis: Sequence<bool>, parent: Sequence<int>, src: int): bool
{
  forall(v: int) => 0 <= v ==> v < seqLength(adj) ==> v < seqLength(vis) ==> v < seqLength(parent) ==> seqSelect(vis, v) ==> v != src ==>
    0 <= seqSelect(parent, v) && seqSelect(parent, v) < seqLength(vis) && seqSelect(vis, seqSelect(parent, v)) && edge(adj, seqSelect(parent, v), v)
};

procedure queueValid(q: Sequence<int>, n: int): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(q) ==> 0 <= seqSelect(q, k) && seqSelect(q, k) < n
};

procedure bfs(adj: Sequence<Sequence<int>>, src: int) returns (vis: Sequence<bool>, parent: Sequence<int>)
  requires wellFormed(adj)
  requires 0 <= src && src < seqLength(adj)
  opaque
  ensures seqLength(vis) == seqLength(adj)
  ensures seqSelect(vis, src)
  ensures justified(adj, vis, parent, src)
{
  var n: int := seqLength(adj);
  var v0: Sequence<bool> := seqEmpty();
  var p0: Sequence<int> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(v0) == x
    invariant seqLength(p0) == x
  {
    v0 := seqBuild(v0, x == src);
    p0 := seqBuild(p0, -1);
    x := x + 1
  };
  var queue: Sequence<int> := seqBuild(seqEmpty(), src);
  var head: int := 0;
  while (head < seqLength(queue))
    invariant 0 <= head
    invariant head <= seqLength(queue)
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant seqLength(v0) == n
    invariant seqLength(p0) == n
    invariant seqSelect(v0, src)
//            ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant justified(adj, v0, p0, src)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant queueValid(queue, n)
  {
    var u: int := seqSelect(queue, head);
    head := head + 1;
    var k: int := 0;
    while (k < seqLength(seqSelect(adj, u)))
      invariant 0 <= k
      invariant seqLength(v0) == n
      invariant seqLength(p0) == n
      invariant seqSelect(v0, src)
      invariant justified(adj, v0, p0, src)
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
      invariant queueValid(queue, n)
    {
      var w: int := seqSelect(seqSelect(adj, u), k);
      if !seqSelect(v0, w) then {
        v0 := seqUpdate(v0, w, true);
        p0 := seqUpdate(p0, w, u);
        queue := seqBuild(queue, w)
      };
      k := k + 1
    }
  };
  vis := v0;
  parent := p0
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure wellFormed(adj: Sequence<Sequence<int>>): bool
{
  forall(u: int) => forall(k: int) => 0 <= u ==> u < seqLength(adj) ==> 0 <= k ==> k < seqLength(seqSelect(adj, u)) ==>
    0 <= seqSelect(seqSelect(adj, u), k) && seqSelect(seqSelect(adj, u), k) < seqLength(adj)
};

procedure edge(adj: Sequence<Sequence<int>>, u: int, v: int): bool
{
  0 <= u && u < seqLength(adj) && (exists(k: int) => 0 <= k && k < seqLength(seqSelect(adj, u)) && seqSelect(seqSelect(adj, u), k) == v)
};

procedure justified(adj: Sequence<Sequence<int>>, vis: Sequence<bool>, parent: Sequence<int>, src: int): bool
{
  forall(v: int) => 0 <= v ==> v < seqLength(adj) ==> v < seqLength(vis) ==> v < seqLength(parent) ==> seqSelect(vis, v) ==> v != src ==>
    0 <= seqSelect(parent, v) && seqSelect(parent, v) < seqLength(vis) && seqSelect(vis, seqSelect(parent, v)) && edge(adj, seqSelect(parent, v), v)
};

procedure queueValid(q: Sequence<int>, n: int): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(q) ==> 0 <= seqSelect(q, k) && seqSelect(q, k) < n
};

procedure bfs(adj: Sequence<Sequence<int>>, src: int) returns (vis: Sequence<bool>, parent: Sequence<int>)
  requires wellFormed(adj)
  requires 0 <= src && src < seqLength(adj)
  opaque
  ensures seqLength(vis) == seqLength(adj)
  ensures seqSelect(vis, src)
  ensures justified(adj, vis, parent, src)
{
  var n: int := seqLength(adj);
  var v0: Sequence<bool> := seqEmpty();
  var p0: Sequence<int> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(v0) == x
    invariant seqLength(p0) == x
  {
    v0 := seqBuild(v0, x == src);
    p0 := seqBuild(p0, -1);
    x := x + 1
  };
  var queue: Sequence<int> := seqBuild(seqEmpty(), src);
  var head: int := 0;
  while (head < seqLength(queue))
    invariant 0 <= head
    invariant head <= seqLength(queue)
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant seqLength(v0) == n
    invariant seqLength(p0) == n
    invariant seqSelect(v0, src)
//            ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant justified(adj, v0, p0, src)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant queueValid(queue, n)
  {
    var u: int := seqSelect(queue, head);
    head := head + 1;
    var k: int := 0;
    while (k < seqLength(seqSelect(adj, u)))
      invariant 0 <= k
      invariant seqLength(v0) == n
      invariant seqLength(p0) == n
      invariant seqSelect(v0, src)
      invariant justified(adj, v0, p0, src)
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
      invariant queueValid(queue, n)
    {
      var w: int := seqSelect(seqSelect(adj, u), k);
      if !seqSelect(v0, w) then {
        v0 := seqUpdate(v0, w, true);
        queue := seqBuild(queue, w)
      };
      k := k + 1
    }
  };
  vis := v0;
  parent := p0
};
#end
