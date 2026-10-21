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

procedure linked(nx: Sequence<int>, pv: Sequence<int>, prev: int, s: int, len: int): bool;
procedure nodeAt(nx: Sequence<int>, s: int, i: int): int;

procedure linkAxioms(): bool
{
  (forall(nx: Sequence<int>) => forall(pv: Sequence<int>) => forall(p: int) => forall(s: int) =>
     linked(nx, pv, p, s, 0) == (s == -1))
  && (forall(nx: Sequence<int>) => forall(pv: Sequence<int>) => forall(p: int) => forall(s: int) => forall(len: int) => len >= 1 ==>
     linked(nx, pv, p, s, len) ==
       (0 <= s && s < seqLength(nx) && s < seqLength(pv) && seqSelect(pv, s) == p
        && linked(nx, pv, s, seqSelect(nx, s), len - 1)))
  && (forall(nx: Sequence<int>) => forall(s: int) => nodeAt(nx, s, 0) == s)
  && (forall(nx: Sequence<int>) => forall(s: int) => forall(i: int) => i >= 1 ==> 0 <= s ==> s < seqLength(nx) ==>
     nodeAt(nx, s, i) == nodeAt(nx, seqSelect(nx, s), i - 1))
};

procedure insertAfter(nx: Sequence<int>, pv: Sequence<int>, head: int, len: int, at: int, atPos: int)
  returns (nx2: Sequence<int>, pv2: Sequence<int>)
  requires linkAxioms()
  requires seqLength(nx) == seqLength(pv)
  requires linked(nx, pv, -1, head, len)
  requires 0 <= at && at < seqLength(nx)
  requires 0 <= atPos && atPos < len
  requires at == nodeAt(nx, head, atPos)
  opaque
  ensures linked(nx2, pv2, -1, head, len + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var k: int := seqLength(nx);
  var after: int := seqSelect(nx, at);
  var n1: Sequence<int> := seqUpdate(seqBuild(nx, after), at, k);
  var p1: Sequence<int> := seqBuild(pv, at);
  if after != -1 then { p1 := seqUpdate(p1, after, k) };
//                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
  nx2 := n1;
  pv2 := p1
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure linked(nx: Sequence<int>, pv: Sequence<int>, prev: int, s: int, len: int): bool;
procedure nodeAt(nx: Sequence<int>, s: int, i: int): int;

procedure linkAxioms(): bool
{
  (forall(nx: Sequence<int>) => forall(pv: Sequence<int>) => forall(p: int) => forall(s: int) =>
     linked(nx, pv, p, s, 0) == (s == -1))
  && (forall(nx: Sequence<int>) => forall(pv: Sequence<int>) => forall(p: int) => forall(s: int) => forall(len: int) => len >= 1 ==>
     linked(nx, pv, p, s, len) ==
       (0 <= s && s < seqLength(nx) && s < seqLength(pv) && seqSelect(pv, s) == p
        && linked(nx, pv, s, seqSelect(nx, s), len - 1)))
  && (forall(nx: Sequence<int>) => forall(s: int) => nodeAt(nx, s, 0) == s)
  && (forall(nx: Sequence<int>) => forall(s: int) => forall(i: int) => i >= 1 ==> 0 <= s ==> s < seqLength(nx) ==>
     nodeAt(nx, s, i) == nodeAt(nx, seqSelect(nx, s), i - 1))
};

procedure insertAfter(nx: Sequence<int>, pv: Sequence<int>, head: int, len: int, at: int, atPos: int)
  returns (nx2: Sequence<int>, pv2: Sequence<int>)
  requires linkAxioms()
  requires seqLength(nx) == seqLength(pv)
  requires linked(nx, pv, -1, head, len)
  requires 0 <= at && at < seqLength(nx)
  requires 0 <= atPos && atPos < len
  requires at == nodeAt(nx, head, atPos)
  opaque
  ensures linked(nx2, pv2, -1, head, len + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var k: int := seqLength(nx);
  var after: int := seqSelect(nx, at);
  var n1: Sequence<int> := seqUpdate(seqBuild(nx, after), at, k);
  var p1: Sequence<int> := seqBuild(pv, at);
  if after != -1 then { p1 := seqUpdate(p1, after, at) };
//                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  nx2 := n1;
  pv2 := p1
};
#end
