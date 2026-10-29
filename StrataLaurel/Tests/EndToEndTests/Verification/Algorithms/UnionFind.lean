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

procedure ranked(parent: Sequence<int>, rank: Sequence<int>): bool
{
  seqLength(parent) == seqLength(rank)
  && (forall(i: int) => 0 <= i ==> i < seqLength(parent) ==>
        0 <= seqSelect(parent, i) && seqSelect(parent, i) < seqLength(parent)
        && (seqSelect(parent, i) == i || seqSelect(rank, seqSelect(parent, i)) > seqSelect(rank, i)))
};

procedure rootOf(parent: Sequence<int>, i: int): int;

procedure rootAxioms(rank: Sequence<int>): bool
{
  forall(parent: Sequence<int>) => forall(i: int) => ranked(parent, rank) ==> 0 <= i ==> i < seqLength(parent) ==>
    rootOf(parent, i) == (if seqSelect(parent, i) == i then i else rootOf(parent, seqSelect(parent, i)))
};

procedure sameRoots(p: Sequence<int>, q: Sequence<int>): bool
{
  seqLength(p) == seqLength(q) && (forall(i: int) => 0 <= i ==> i < seqLength(p) ==> rootOf(p, i) == rootOf(q, i))
};

procedure find(parent: Sequence<int>, rank: Sequence<int>, x: int) returns (root: int, res: Sequence<int>)
  requires ranked(parent, rank)
  requires rootAxioms(rank)
  requires 0 <= x && x < seqLength(parent)
  opaque
  ensures ranked(res, rank)
  ensures root == rootOf(parent, x)
  ensures sameRoots(res, parent)
{
  var r: int := x;
  while (seqSelect(parent, r) != r)
    invariant 0 <= r
    invariant r < seqLength(parent)
    invariant rootOf(parent, r) == rootOf(parent, x)
  {
    r := seqSelect(parent, r)
  };
  var p: Sequence<int> := parent;
  var cur: int := x;
  while (seqSelect(p, cur) != r)
    invariant 0 <= cur
    invariant cur < seqLength(p)
    invariant ranked(p, rank)
    invariant sameRoots(p, parent)
    invariant rootOf(p, cur) == r
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var next: int := seqSelect(p, cur);
    p := seqUpdate(p, cur, r);
    cur := next
  };
  root := r;
  res := p
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure ranked(parent: Sequence<int>, rank: Sequence<int>): bool
{
  seqLength(parent) == seqLength(rank)
  && (forall(i: int) => 0 <= i ==> i < seqLength(parent) ==>
        0 <= seqSelect(parent, i) && seqSelect(parent, i) < seqLength(parent)
        && (seqSelect(parent, i) == i || seqSelect(rank, seqSelect(parent, i)) > seqSelect(rank, i)))
};

procedure rootOf(parent: Sequence<int>, i: int): int;

procedure rootAxioms(rank: Sequence<int>): bool
{
  forall(parent: Sequence<int>) => forall(i: int) => ranked(parent, rank) ==> 0 <= i ==> i < seqLength(parent) ==>
    rootOf(parent, i) == (if seqSelect(parent, i) == i then i else rootOf(parent, seqSelect(parent, i)))
};

procedure sameRoots(p: Sequence<int>, q: Sequence<int>): bool
{
  seqLength(p) == seqLength(q) && (forall(i: int) => 0 <= i ==> i < seqLength(p) ==> rootOf(p, i) == rootOf(q, i))
};

procedure find(parent: Sequence<int>, rank: Sequence<int>, x: int) returns (root: int, res: Sequence<int>)
  requires ranked(parent, rank)
  requires rootAxioms(rank)
  requires 0 <= x && x < seqLength(parent)
  opaque
  ensures ranked(res, rank)
  ensures root == rootOf(parent, x)
  ensures sameRoots(res, parent)
{
  var r: int := x;
  while (seqSelect(parent, r) != r)
    invariant 0 <= r
    invariant r < seqLength(parent)
    invariant rootOf(parent, r) == rootOf(parent, x)
  {
    r := seqSelect(parent, r)
  };
  var p: Sequence<int> := parent;
  var cur: int := x;
  while (seqSelect(p, cur) != r)
    invariant 0 <= cur
    invariant cur < seqLength(p)
    invariant ranked(p, rank)
    invariant sameRoots(p, parent)
// desired: assertion could not be proved
    invariant rootOf(p, cur) == r
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var next: int := seqSelect(p, cur);
    p := seqUpdate(p, cur, cur);
    cur := next
  };
  root := r;
  res := p
};
#end
