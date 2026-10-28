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

procedure count(s: Sequence<int>, v: int, hi: int): int;

procedure countAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(v: int) => count(s, v, 0) == 0)
  && (forall(s: Sequence<int>) => forall(v: int) => forall(h: int) =>
        1 <= h ==> h <= seqLength(s) ==>
          count(s, v, h) == count(s, v, h - 1) + (if seqSelect(s, h - 1) == v then 1 else 0))
};

procedure heapExcept(h: Sequence<int>, size: int, hole: int): bool
{
  forall(k: int) => 0 < k ==> k < size ==> size <= seqLength(h) ==> k != hole ==>
    seqSelect(h, (k - 1) / 2) >= seqSelect(h, k)
};

procedure insert(h: Sequence<int>, size: int, v: int) returns (res: Sequence<int>)
  requires 0 <= size
  requires size < seqLength(h)
  requires heapExcept(h, size, -1)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(h)
  ensures heapExcept(res, size + 1, -1)
{
  var s: Sequence<int> := seqUpdate(h, size, v);
  var i: int := size;
  while (i > 0 && seqSelect(s, (i - 1) / 2) < seqSelect(s, i))
    invariant 0 <= i
//            ^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant i <= size
    invariant seqLength(s) == seqLength(h)
    invariant heapExcept(s, size + 1, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant i > 0 ==> 2 * i + 1 <= size ==> seqSelect(s, (i - 1) / 2) >= seqSelect(s, 2 * i + 1)
    invariant i > 0 ==> 2 * i + 2 <= size ==> seqSelect(s, (i - 1) / 2) >= seqSelect(s, 2 * i + 2)
  {
    var p: int := (i - 1) / 2;
    var tmp: int := seqSelect(s, p);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    s := seqUpdate(s, p, seqSelect(s, i));
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    s := seqUpdate(s, i, tmp);
    i := p
  };
  res := s
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure count(s: Sequence<int>, v: int, hi: int): int;

procedure countAxioms(): bool
{
  (forall(s: Sequence<int>) => forall(v: int) => count(s, v, 0) == 0)
  && (forall(s: Sequence<int>) => forall(v: int) => forall(h: int) =>
        1 <= h ==> h <= seqLength(s) ==>
          count(s, v, h) == count(s, v, h - 1) + (if seqSelect(s, h - 1) == v then 1 else 0))
};

procedure heapExcept(h: Sequence<int>, size: int, hole: int): bool
{
  forall(k: int) => 0 < k ==> k < size ==> size <= seqLength(h) ==> k != hole ==>
    seqSelect(h, (k - 1) / 2) >= seqSelect(h, k)
};

procedure insert(h: Sequence<int>, size: int, v: int) returns (res: Sequence<int>)
  requires 0 <= size
  requires size < seqLength(h)
  requires heapExcept(h, size, -1)
  requires countAxioms()
  opaque
  ensures seqLength(res) == seqLength(h)
  ensures heapExcept(res, size + 1, -1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
{
  var s: Sequence<int> := seqUpdate(h, size, v);
  var i: int := size;
  while (i > 1 && seqSelect(s, (i - 1) / 2) < seqSelect(s, i))
    invariant 0 <= i
//            ^^^^^^ error: assertion could not be proved
    invariant i <= size
    invariant seqLength(s) == seqLength(h)
    invariant heapExcept(s, size + 1, i)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant i > 0 ==> 2 * i + 1 <= size ==> seqSelect(s, (i - 1) / 2) >= seqSelect(s, 2 * i + 1)
    invariant i > 0 ==> 2 * i + 2 <= size ==> seqSelect(s, (i - 1) / 2) >= seqSelect(s, 2 * i + 2)
  {
    var p: int := (i - 1) / 2;
    var tmp: int := seqSelect(s, p);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    s := seqUpdate(s, p, seqSelect(s, i));
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    s := seqUpdate(s, i, tmp);
    i := p
  };
  res := s
};
#end
