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

procedure sortedPath(nx: Sequence<int>, val: Sequence<int>, s: int, len: int): bool;

procedure sortedAxioms(): bool
{
  (forall(nx: Sequence<int>) => forall(val: Sequence<int>) => forall(s: int) => sortedPath(nx, val, s, 0) == (s == -1))
  && (forall(nx: Sequence<int>) => forall(val: Sequence<int>) => forall(s: int) => forall(len: int) => len >= 1 ==>
        sortedPath(nx, val, s, len) ==
          (0 <= s && s < seqLength(nx) && s < seqLength(val)
           && (len >= 2 ==> 0 <= seqSelect(nx, s) && seqSelect(nx, s) < seqLength(val)
                            && seqSelect(val, s) <= seqSelect(val, seqSelect(nx, s)))
           && sortedPath(nx, val, seqSelect(nx, s), len - 1)))
};

procedure insert(nx: Sequence<int>, val: Sequence<int>, head: int, len: int, v: int)
  returns (nx2: Sequence<int>, val2: Sequence<int>, head2: int)
  requires len >= 0
  requires seqLength(nx) == seqLength(val)
  requires sortedAxioms()
  requires sortedPath(nx, val, head, len)
  opaque
  ensures seqLength(nx2) == seqLength(nx) + 1
  ensures seqLength(val2) == seqLength(val) + 1
  ensures sortedPath(nx2, val2, head2, len + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var k: int := seqLength(nx);
  var vs: Sequence<int> := seqBuild(val, v);
  if head == -1 || v <= seqSelect(val, head) then {
    nx2 := seqBuild(nx, head);
    val2 := vs;
    head2 := k
  } else {
    var cur: int := head;
    var steps: int := 1;
    while (seqSelect(nx, cur) != -1 && seqSelect(val, seqSelect(nx, cur)) < v)
//                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      invariant 1 <= steps
      invariant steps <= len
//              ^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
      invariant 0 <= cur
//              ^^^^^^^^ error: assertion could not be proved
// desired: verifies
      invariant cur < seqLength(nx)
//              ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
      invariant seqSelect(val, cur) < v
//              ^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    {
      cur := seqSelect(nx, cur);
      steps := steps + 1
    };
    var m: Sequence<int> := seqBuild(nx, seqSelect(nx, cur));
    nx2 := seqUpdate(m, cur, k);
    val2 := vs;
    head2 := head
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure sortedPath(nx: Sequence<int>, val: Sequence<int>, s: int, len: int): bool;

procedure sortedAxioms(): bool
{
  (forall(nx: Sequence<int>) => forall(val: Sequence<int>) => forall(s: int) => sortedPath(nx, val, s, 0) == (s == -1))
  && (forall(nx: Sequence<int>) => forall(val: Sequence<int>) => forall(s: int) => forall(len: int) => len >= 1 ==>
        sortedPath(nx, val, s, len) ==
          (0 <= s && s < seqLength(nx) && s < seqLength(val)
           && (len >= 2 ==> 0 <= seqSelect(nx, s) && seqSelect(nx, s) < seqLength(val)
                            && seqSelect(val, s) <= seqSelect(val, seqSelect(nx, s)))
           && sortedPath(nx, val, seqSelect(nx, s), len - 1)))
};

procedure insert(nx: Sequence<int>, val: Sequence<int>, head: int, len: int, v: int)
  returns (nx2: Sequence<int>, val2: Sequence<int>, head2: int)
  requires len >= 0
  requires seqLength(nx) == seqLength(val)
  requires sortedAxioms()
  requires sortedPath(nx, val, head, len)
  opaque
  ensures seqLength(nx2) == seqLength(nx) + 1
  ensures seqLength(val2) == seqLength(val) + 1
  ensures sortedPath(nx2, val2, head2, len + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var k: int := seqLength(nx);
  var vs: Sequence<int> := seqBuild(val, v);
  if head == -1 || v <= seqSelect(val, head) then {
    nx2 := seqBuild(nx, head);
    val2 := vs;
    head2 := k
  } else {
    var cur: int := head;
    var steps: int := 1;
    while (seqSelect(nx, cur) != -1 && seqSelect(val, seqSelect(nx, cur)) > v)
//                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
      invariant 1 <= steps
      invariant steps <= len
//              ^^^^^^^^^^^^ error: assertion could not be proved
      invariant 0 <= cur
//              ^^^^^^^^ error: assertion could not be proved
      invariant cur < seqLength(nx)
//              ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
      invariant seqSelect(val, cur) < v
//              ^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    {
      cur := seqSelect(nx, cur);
      steps := steps + 1
    };
    var m: Sequence<int> := seqBuild(nx, seqSelect(nx, cur));
    nx2 := seqUpdate(m, cur, k);
    val2 := vs;
    head2 := head
  }
};
#end
