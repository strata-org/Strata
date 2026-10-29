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

procedure depth(ev: Sequence<int>, hi: int): int;
procedure openAt(ev: Sequence<int>, hi: int, d: int): int;

procedure nestAxioms(): bool
{
  (forall(ev: Sequence<int>) => depth(ev, 0) == 0)
  && (forall(ev: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(ev) ==>
        depth(ev, h) == depth(ev, h - 1) + (if seqSelect(ev, h - 1) > 0 then 1 else -1))
  && (forall(ev: Sequence<int>) => forall(d: int) => openAt(ev, 0, d) == 0)
  && (forall(ev: Sequence<int>) => forall(h: int) => forall(d: int) => 1 <= h ==> h <= seqLength(ev) ==>
        openAt(ev, h, d) == (if seqSelect(ev, h - 1) > 0 && d == depth(ev, h - 1) then seqSelect(ev, h - 1) else openAt(ev, h - 1, d)))
};

procedure matchedBelow(ev: Sequence<int>, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(ev) ==> seqSelect(ev, k) < 0 ==>
    depth(ev, k) > 0 && openAt(ev, k, depth(ev, k) - 1) == -seqSelect(ev, k)
};

procedure stackModels(ev: Sequence<int>, st: Sequence<int>, hi: int): bool
{
  forall(d: int) => 0 <= d ==> d < seqLength(st) ==> seqSelect(st, d) == openAt(ev, hi, d)
};

procedure wellNested(ev: Sequence<int>) returns (ok: bool)
  requires nestAxioms()
  requires forall(k: int) => 0 <= k ==> k < seqLength(ev) ==> seqSelect(ev, k) != 0
  opaque
  ensures ok == (matchedBelow(ev, seqLength(ev)) && depth(ev, seqLength(ev)) == 0)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var st: Sequence<int> := seqEmpty();
  var i: int := 0;
  var bad: bool := false;
  while (i < seqLength(ev) && !bad)
    invariant 0 <= i
    invariant i <= seqLength(ev)
    invariant !bad ==> seqLength(st) == depth(ev, i)
    invariant !bad ==> matchedBelow(ev, i)
    invariant !bad ==> stackModels(ev, st, i)
  {
    var e: int := seqSelect(ev, i);
    if e > 0 then { st := seqBuild(st, e); i := i + 1 }
    else if seqLength(st) == 0 || seqSelect(st, seqLength(st) - 1) != -e then { bad := true }
    else { st := seqTake(st, seqLength(st) - 1); i := i + 1 }
  };
  ok := !bad && seqLength(st) == 0
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure depth(ev: Sequence<int>, hi: int): int;
procedure openAt(ev: Sequence<int>, hi: int, d: int): int;

procedure nestAxioms(): bool
{
  (forall(ev: Sequence<int>) => depth(ev, 0) == 0)
  && (forall(ev: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(ev) ==>
        depth(ev, h) == depth(ev, h - 1) + (if seqSelect(ev, h - 1) > 0 then 1 else -1))
  && (forall(ev: Sequence<int>) => forall(d: int) => openAt(ev, 0, d) == 0)
  && (forall(ev: Sequence<int>) => forall(h: int) => forall(d: int) => 1 <= h ==> h <= seqLength(ev) ==>
        openAt(ev, h, d) == (if seqSelect(ev, h - 1) > 0 && d == depth(ev, h - 1) then seqSelect(ev, h - 1) else openAt(ev, h - 1, d)))
};

procedure matchedBelow(ev: Sequence<int>, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(ev) ==> seqSelect(ev, k) < 0 ==>
    depth(ev, k) > 0 && openAt(ev, k, depth(ev, k) - 1) == -seqSelect(ev, k)
};

procedure stackModels(ev: Sequence<int>, st: Sequence<int>, hi: int): bool
{
  forall(d: int) => 0 <= d ==> d < seqLength(st) ==> seqSelect(st, d) == openAt(ev, hi, d)
};

procedure wellNested(ev: Sequence<int>) returns (ok: bool)
  requires nestAxioms()
  requires forall(k: int) => 0 <= k ==> k < seqLength(ev) ==> seqSelect(ev, k) != 0
  opaque
  ensures ok == (matchedBelow(ev, seqLength(ev)) && depth(ev, seqLength(ev)) == 0)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var st: Sequence<int> := seqEmpty();
  var i: int := 0;
  var bad: bool := false;
  while (i < seqLength(ev) && !bad)
    invariant 0 <= i
    invariant i <= seqLength(ev)
    invariant !bad ==> seqLength(st) == depth(ev, i)
    invariant !bad ==> matchedBelow(ev, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant !bad ==> stackModels(ev, st, i)
  {
    var e: int := seqSelect(ev, i);
    if e > 0 then { st := seqBuild(st, e); i := i + 1 }
    else if seqLength(st) == 0 then { bad := true }
    else { st := seqTake(st, seqLength(st) - 1); i := i + 1 }
  };
  ok := !bad && seqLength(st) == 0
};
#end
