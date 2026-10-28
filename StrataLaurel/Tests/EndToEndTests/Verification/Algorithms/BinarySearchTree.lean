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

procedure bst(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, n: int, lo: int, hi: int, h: int): bool;
procedure inTree(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, n: int, x: int, h: int): bool;

procedure treeAxioms(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>): bool
{
  seqLength(key) == seqLength(lf) && seqLength(lf) == seqLength(rt)
  && (forall(lo: int) => forall(hi: int) => forall(h: int) => bst(key, lf, rt, -1, lo, hi, h))
  && (forall(n: int) => forall(lo: int) => forall(hi: int) => forall(h: int) => n != -1 ==>
        bst(key, lf, rt, n, lo, hi, h) ==
          (h >= 1 && 0 <= n && n < seqLength(key)
           && lo < seqSelect(key, n) && seqSelect(key, n) < hi
           && bst(key, lf, rt, seqSelect(lf, n), lo, seqSelect(key, n), h - 1)
           && bst(key, lf, rt, seqSelect(rt, n), seqSelect(key, n), hi, h - 1)))
  && (forall(x: int) => forall(h: int) => !inTree(key, lf, rt, -1, x, h))
  && (forall(n: int) => forall(x: int) => forall(h: int) => n != -1 ==> 0 <= n ==> n < seqLength(key) ==> h >= 1 ==>
        inTree(key, lf, rt, n, x, h) ==
          (seqSelect(key, n) == x || inTree(key, lf, rt, seqSelect(lf, n), x, h - 1) || inTree(key, lf, rt, seqSelect(rt, n), x, h - 1)))
};

procedure contains(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, root: int, x: int, h: int, lo: int, hi: int) returns (r: bool)
  requires treeAxioms(key, lf, rt)
  requires bst(key, lf, rt, root, lo, hi, h)
  requires lo < x
  requires x < hi
  requires h >= 0
  opaque
  ensures r == inTree(key, lf, rt, root, x, h)
{
  var cur: int := root;
  var d: int := h;
  var clo: int := lo;
  var chi: int := hi;
  var found: bool := false;
  while (cur != -1 && !found)
    invariant 0 <= d
    invariant d <= h
    invariant bst(key, lf, rt, cur, clo, chi, d)
    invariant clo < x
    invariant x < chi
    invariant found ==> inTree(key, lf, rt, root, x, h)
    invariant !found ==> inTree(key, lf, rt, root, x, h) == inTree(key, lf, rt, cur, x, d)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    if seqSelect(key, cur) == x then { found := true }
    else if x < seqSelect(key, cur) then { chi := seqSelect(key, cur); cur := seqSelect(lf, cur); d := d - 1 }
    else { clo := seqSelect(key, cur); cur := seqSelect(rt, cur); d := d - 1 }
  };
  r := found
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure bst(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, n: int, lo: int, hi: int, h: int): bool;
procedure inTree(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, n: int, x: int, h: int): bool;

procedure treeAxioms(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>): bool
{
  seqLength(key) == seqLength(lf) && seqLength(lf) == seqLength(rt)
  && (forall(lo: int) => forall(hi: int) => forall(h: int) => bst(key, lf, rt, -1, lo, hi, h))
  && (forall(n: int) => forall(lo: int) => forall(hi: int) => forall(h: int) => n != -1 ==>
        bst(key, lf, rt, n, lo, hi, h) ==
          (h >= 1 && 0 <= n && n < seqLength(key)
           && lo < seqSelect(key, n) && seqSelect(key, n) < hi
           && bst(key, lf, rt, seqSelect(lf, n), lo, seqSelect(key, n), h - 1)
           && bst(key, lf, rt, seqSelect(rt, n), seqSelect(key, n), hi, h - 1)))
  && (forall(x: int) => forall(h: int) => !inTree(key, lf, rt, -1, x, h))
  && (forall(n: int) => forall(x: int) => forall(h: int) => n != -1 ==> 0 <= n ==> n < seqLength(key) ==> h >= 1 ==>
        inTree(key, lf, rt, n, x, h) ==
          (seqSelect(key, n) == x || inTree(key, lf, rt, seqSelect(lf, n), x, h - 1) || inTree(key, lf, rt, seqSelect(rt, n), x, h - 1)))
};

procedure contains(key: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, root: int, x: int, h: int, lo: int, hi: int) returns (r: bool)
  requires treeAxioms(key, lf, rt)
  requires bst(key, lf, rt, root, lo, hi, h)
  requires lo < x
  requires x < hi
  requires h >= 0
  opaque
  ensures r == inTree(key, lf, rt, root, x, h)
{
  var cur: int := root;
  var d: int := h;
  var clo: int := lo;
  var chi: int := hi;
  var found: bool := false;
  while (cur != -1 && !found)
    invariant 0 <= d
    invariant d <= h
    invariant bst(key, lf, rt, cur, clo, chi, d)
    invariant clo < x
//            ^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant x < chi
//            ^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant found ==> inTree(key, lf, rt, root, x, h)
    invariant !found ==> inTree(key, lf, rt, root, x, h) == inTree(key, lf, rt, cur, x, d)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    if seqSelect(key, cur) == x then { found := true }
    else if x > seqSelect(key, cur) then { chi := seqSelect(key, cur); cur := seqSelect(lf, cur); d := d - 1 }
    else { clo := seqSelect(key, cur); cur := seqSelect(rt, cur); d := d - 1 }
  };
  r := found
};
#end
