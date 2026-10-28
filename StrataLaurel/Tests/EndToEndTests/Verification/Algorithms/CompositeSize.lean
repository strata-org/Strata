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

procedure sizeOf(sz: Sequence<int>, n: int): int
{
  if n == -1 then 0 else seqSelect(sz, n)
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
};

procedure consistent(parent: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, sz: Sequence<int>): bool
{
  seqLength(parent) == seqLength(lf) && seqLength(lf) == seqLength(rt) && seqLength(rt) == seqLength(sz)
  && (forall(i: int) => 0 <= i ==> i < seqLength(sz) ==>
        -1 <= seqSelect(parent, i) && seqSelect(parent, i) < seqLength(sz)
        && -1 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(sz)
        && -1 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(sz)
        && seqSelect(sz, i) == 1 + sizeOf(sz, seqSelect(lf, i)) + sizeOf(sz, seqSelect(rt, i))
        && (seqSelect(lf, i) == -1 || seqSelect(parent, seqSelect(lf, i)) == i)
        && (seqSelect(rt, i) == -1 || seqSelect(parent, seqSelect(rt, i)) == i)
        && (seqSelect(parent, i) == -1 || seqSelect(lf, seqSelect(parent, i)) == i || seqSelect(rt, seqSelect(parent, i)) == i))
};

procedure addLeft(parent: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, sz: Sequence<int>, p: int, c: int)
  returns (par2: Sequence<int>, lf2: Sequence<int>, sz2: Sequence<int>)
  requires consistent(parent, lf, rt, sz)
  requires 0 <= p && p < seqLength(sz) && seqSelect(lf, p) == -1
  requires 0 <= c && c < seqLength(sz) && c != p
  requires seqSelect(parent, c) == -1 && seqSelect(lf, c) == -1 && seqSelect(rt, c) == -1
  opaque
  ensures consistent(par2, lf2, rt, sz2)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures seqSelect(lf2, p) == c
{
  var pa: Sequence<int> := seqUpdate(parent, c, p);
  var l: Sequence<int> := seqUpdate(lf, p, c);
  var s: Sequence<int> := sz;
  var cur: int := p;
  while (cur != -1)
    invariant -1 <= cur && cur < seqLength(s)
    invariant seqLength(s) == seqLength(sz)
  {
    s := seqUpdate(s, cur, seqSelect(s, cur) + 1);
    cur := seqSelect(pa, cur)
  };
  par2 := pa;
  lf2 := l;
  sz2 := s
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure sizeOf(sz: Sequence<int>, n: int): int
{
  if n == -1 then 0 else seqSelect(sz, n)
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure consistent(parent: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, sz: Sequence<int>): bool
{
  seqLength(parent) == seqLength(lf) && seqLength(lf) == seqLength(rt) && seqLength(rt) == seqLength(sz)
  && (forall(i: int) => 0 <= i ==> i < seqLength(sz) ==>
        -1 <= seqSelect(parent, i) && seqSelect(parent, i) < seqLength(sz)
        && -1 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(sz)
        && -1 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(sz)
        && seqSelect(sz, i) == 1 + sizeOf(sz, seqSelect(lf, i)) + sizeOf(sz, seqSelect(rt, i))
        && (seqSelect(lf, i) == -1 || seqSelect(parent, seqSelect(lf, i)) == i)
        && (seqSelect(rt, i) == -1 || seqSelect(parent, seqSelect(rt, i)) == i)
        && (seqSelect(parent, i) == -1 || seqSelect(lf, seqSelect(parent, i)) == i || seqSelect(rt, seqSelect(parent, i)) == i))
};

procedure addLeft(parent: Sequence<int>, lf: Sequence<int>, rt: Sequence<int>, sz: Sequence<int>, p: int, c: int)
  returns (par2: Sequence<int>, lf2: Sequence<int>, sz2: Sequence<int>)
  requires consistent(parent, lf, rt, sz)
  requires 0 <= p && p < seqLength(sz) && seqSelect(lf, p) == -1
  requires 0 <= c && c < seqLength(sz) && c != p
  requires seqSelect(parent, c) == -1 && seqSelect(lf, c) == -1 && seqSelect(rt, c) == -1
  opaque
  ensures consistent(par2, lf2, rt, sz2)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition could not be proved
  ensures seqSelect(lf2, p) == c
{
  var pa: Sequence<int> := seqUpdate(parent, c, p);
  var l: Sequence<int> := seqUpdate(lf, p, c);
  var s: Sequence<int> := sz;
  var cur: int := p;
  while (cur != -1 && seqSelect(pa, cur) != -1)
    invariant -1 <= cur && cur < seqLength(s)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant seqLength(s) == seqLength(sz)
  {
    s := seqUpdate(s, cur, seqSelect(s, cur) + 1);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                         ^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    cur := seqSelect(pa, cur)
//  ^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  };
  par2 := pa;
  lf2 := l;
  sz2 := s
};
#end
