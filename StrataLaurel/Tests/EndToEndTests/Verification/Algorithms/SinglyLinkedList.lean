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

procedure path(nx: Sequence<int>, s: int, len: int): bool;

procedure pathAxioms(): bool
{
  (forall(nx: Sequence<int>) => forall(s: int) => path(nx, s, 0) == (s == -1))
  && (forall(nx: Sequence<int>) => forall(s: int) => forall(len: int) => len >= 1 ==>
        path(nx, s, len) == (0 <= s && s < seqLength(nx) && path(nx, seqSelect(nx, s), len - 1)))
};

procedure reverse(nx: Sequence<int>, head: int, len: int) returns (res: Sequence<int>, newHead: int)
  requires len >= 0
  requires pathAxioms()
  requires path(nx, head, len)
  opaque
  ensures seqLength(res) == seqLength(nx)
  ensures path(res, newHead, len)
{
  var m: Sequence<int> := nx;
  var prev: int := -1;
  var cur: int := head;
  var done: int := 0;
  while (cur != -1)
    invariant 0 <= done
    invariant done <= len
    invariant seqLength(m) == seqLength(nx)
    invariant path(m, prev, done)
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant path(m, cur, len - done)
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    var nxt: int := seqSelect(m, cur);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    m := seqUpdate(m, cur, prev);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    prev := cur;
    cur := nxt;
    done := done + 1
  };
  res := m;
  newHead := prev
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure path(nx: Sequence<int>, s: int, len: int): bool;

procedure pathAxioms(): bool
{
  (forall(nx: Sequence<int>) => forall(s: int) => path(nx, s, 0) == (s == -1))
  && (forall(nx: Sequence<int>) => forall(s: int) => forall(len: int) => len >= 1 ==>
        path(nx, s, len) == (0 <= s && s < seqLength(nx) && path(nx, seqSelect(nx, s), len - 1)))
};

procedure reverse(nx: Sequence<int>, head: int, len: int) returns (res: Sequence<int>, newHead: int)
  requires len >= 0
  requires pathAxioms()
  requires path(nx, head, len)
  opaque
  ensures seqLength(res) == seqLength(nx)
  ensures path(res, newHead, len)
{
  var m: Sequence<int> := nx;
  var prev: int := -1;
  var cur: int := head;
  var done: int := 0;
  while (cur != -1)
    invariant 0 <= done
    invariant done <= len
    invariant seqLength(m) == seqLength(nx)
    invariant path(m, prev, done)
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion could not be proved
    invariant path(m, cur, len - done)
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    var nxt: int := seqSelect(m, cur);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    m := seqUpdate(m, cur, nxt);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
    prev := cur;
    cur := nxt;
    done := done + 1
  };
  res := m;
  newHead := prev
};
#end
