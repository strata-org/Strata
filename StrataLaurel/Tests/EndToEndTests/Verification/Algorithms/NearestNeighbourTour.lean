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

procedure at(m: Sequence<Sequence<int>>, r: int, c: int): int
  requires 0 <= r && r < seqLength(m) && 0 <= c && c < seqLength(seqSelect(m, r))
{
  seqSelect(seqSelect(m, r), c)
};

procedure square(d: Sequence<Sequence<int>>, n: int): bool
{
  seqLength(d) == n && (forall(r: int) => 0 <= r ==> r < n ==> seqLength(seqSelect(d, r)) == n)
};

procedure distinctValidBelow(tour: Sequence<int>, n: int, hi: int): bool
{
  (forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(tour) ==> 0 <= seqSelect(tour, k) && seqSelect(tour, k) < n)
  && (forall(k: int) => forall(m: int) => 0 <= k ==> k < m ==> m < hi ==> m < seqLength(tour) ==>
        seqSelect(tour, k) != seqSelect(tour, m))
};

procedure visitedMatches(visited: Sequence<bool>, tour: Sequence<int>, hi: int): bool
{
  forall(c: int) => 0 <= c ==> c < seqLength(visited) ==>
    (seqSelect(visited, c) ==> (exists(k: int) => 0 <= k && k < hi && k < seqLength(tour) && seqSelect(tour, k) == c))
    && ((exists(k: int) => 0 <= k && k < hi && k < seqLength(tour) && seqSelect(tour, k) == c) ==> seqSelect(visited, c))
};

procedure noneVisitedBelow(visited: Sequence<bool>, hi: int): bool
{
  forall(c: int) => 0 <= c ==> c < hi ==> c < seqLength(visited) ==> !seqSelect(visited, c)
};

procedure allVisitedBelow(visited: Sequence<bool>, hi: int): bool
{
  forall(c: int) => 0 <= c ==> c < hi ==> c < seqLength(visited) ==> seqSelect(visited, c)
};

procedure tour(d: Sequence<Sequence<int>>, n: int) returns (res: Sequence<int>)
  requires 1 <= n
  requires square(d, n)
  opaque
  ensures seqLength(res) == n
  ensures seqSelect(res, 0) == 0
  ensures distinctValidBelow(res, n, n)
{
  var visited: Sequence<bool> := seqEmpty();
  var x: int := 0;
  while (x < n)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(visited) == x
    invariant noneVisitedBelow(visited, x)
  {
    visited := seqBuild(visited, false);
    x := x + 1
  };
  var t: Sequence<int> := seqBuild(seqEmpty(), 0);
  visited := seqUpdate(visited, 0, true);
  var step: int := 1;
  while (step < n)
    invariant 1 <= step
    invariant step <= n
    invariant seqLength(t) == step
    invariant seqLength(visited) == n
    invariant seqSelect(t, 0) == 0
    invariant distinctValidBelow(t, n, step)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant visitedMatches(visited, t, step)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var last: int := seqSelect(t, step - 1);
    var best: int := -1;
    var c: int := 0;
    while (c < n)
      invariant 0 <= c
      invariant c <= n
      invariant -1 <= best
      invariant best < c
      invariant best >= 0 ==> !seqSelect(visited, best)
      invariant best == -1 ==> allVisitedBelow(visited, c)
    {
      if !seqSelect(visited, c) && (best == -1 || at(d, last, c) < at(d, last, best)) then { best := c };
      c := c + 1
    };
    t := seqBuild(t, best);
    visited := seqUpdate(visited, best, true);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    step := step + 1
  };
  res := t
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure at(m: Sequence<Sequence<int>>, r: int, c: int): int
  requires 0 <= r && r < seqLength(m) && 0 <= c && c < seqLength(seqSelect(m, r))
{
  seqSelect(seqSelect(m, r), c)
};

procedure square(d: Sequence<Sequence<int>>, n: int): bool
{
  seqLength(d) == n && (forall(r: int) => 0 <= r ==> r < n ==> seqLength(seqSelect(d, r)) == n)
};

procedure distinctValidBelow(tour: Sequence<int>, n: int, hi: int): bool
{
  (forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(tour) ==> 0 <= seqSelect(tour, k) && seqSelect(tour, k) < n)
  && (forall(k: int) => forall(m: int) => 0 <= k ==> k < m ==> m < hi ==> m < seqLength(tour) ==>
        seqSelect(tour, k) != seqSelect(tour, m))
};

procedure visitedMatches(visited: Sequence<bool>, tour: Sequence<int>, hi: int): bool
{
  forall(c: int) => 0 <= c ==> c < seqLength(visited) ==>
    (seqSelect(visited, c) ==> (exists(k: int) => 0 <= k && k < hi && k < seqLength(tour) && seqSelect(tour, k) == c))
    && ((exists(k: int) => 0 <= k && k < hi && k < seqLength(tour) && seqSelect(tour, k) == c) ==> seqSelect(visited, c))
};

procedure noneVisitedBelow(visited: Sequence<bool>, hi: int): bool
{
  forall(c: int) => 0 <= c ==> c < hi ==> c < seqLength(visited) ==> !seqSelect(visited, c)
};

procedure allVisitedBelow(visited: Sequence<bool>, hi: int): bool
{
  forall(c: int) => 0 <= c ==> c < hi ==> c < seqLength(visited) ==> seqSelect(visited, c)
};

procedure tour(d: Sequence<Sequence<int>>, n: int) returns (res: Sequence<int>)
  requires 1 <= n
  requires square(d, n)
  opaque
  ensures seqLength(res) == n
  ensures seqSelect(res, 0) == 0
  ensures distinctValidBelow(res, n, n)
{
  var visited: Sequence<bool> := seqEmpty();
  var x: int := 0;
  while (x < n - 1)
    invariant 0 <= x
    invariant x <= n
    invariant seqLength(visited) == x
    invariant noneVisitedBelow(visited, x)
  {
    visited := seqBuild(visited, false);
    x := x + 1
  };
  var t: Sequence<int> := seqBuild(seqEmpty(), 0);
  visited := seqUpdate(visited, 0, true);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
  var step: int := 1;
  while (step < n)
    invariant 1 <= step
    invariant step <= n
    invariant seqLength(t) == step
    invariant seqLength(visited) == n
//            ^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant seqSelect(t, 0) == 0
    invariant distinctValidBelow(t, n, step)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant visitedMatches(visited, t, step)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var last: int := seqSelect(t, step - 1);
    var best: int := -1;
    var c: int := 0;
    while (c < n)
      invariant 0 <= c
      invariant c <= n
      invariant -1 <= best
      invariant best < c
      invariant best >= 0 ==> !seqSelect(visited, best)
      invariant best == -1 ==> allVisitedBelow(visited, c)
    {
      if !seqSelect(visited, c) && (best == -1 || at(d, last, c) < at(d, last, best)) then { best := c };
      c := c + 1
    };
    t := seqBuild(t, best);
    visited := seqUpdate(visited, best, true);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    step := step + 1
  };
  res := t
};
#end
