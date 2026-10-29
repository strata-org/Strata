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

procedure closed(nx: Sequence<int>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(nx) ==> 0 <= seqSelect(nx, i) && seqSelect(nx, i) < seqLength(nx)
};

procedure iterate(nx: Sequence<int>, x: int, k: int): int;

procedure iterAxioms(nx: Sequence<int>): bool
{
  (forall(x: int) => iterate(nx, x, 0) == x)
  && (forall(x: int) => forall(k: int) => k >= 1 ==> 0 <= x ==> x < seqLength(nx) ==>
        iterate(nx, x, k) == iterate(nx, seqSelect(nx, x), k - 1))
};

procedure cycleLength(nx: Sequence<int>, x0: int) returns (lambda: int)
  requires closed(nx)
  requires iterAxioms(nx)
  requires 0 <= x0 && x0 < seqLength(nx)
  opaque
  ensures 1 <= lambda
{
  var t: int := seqSelect(nx, x0);
  var h: int := seqSelect(nx, seqSelect(nx, x0));
  var steps: int := 1;
  while (t != h)
    invariant 1 <= steps
    invariant 0 <= t && t < seqLength(nx)
    invariant 0 <= h && h < seqLength(nx)
    invariant t == iterate(nx, x0, steps)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant h == iterate(nx, x0, 2 * steps)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    t := seqSelect(nx, t);
    h := seqSelect(nx, seqSelect(nx, h));
    steps := steps + 1
  };
  var len: int := 1;
  var probe: int := seqSelect(nx, t);
  while (probe != t)
    invariant 1 <= len
    invariant 0 <= probe && probe < seqLength(nx)
    invariant probe == iterate(nx, t, len)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    probe := seqSelect(nx, probe);
    len := len + 1
  };
  lambda := len
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure closed(nx: Sequence<int>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(nx) ==> 0 <= seqSelect(nx, i) && seqSelect(nx, i) < seqLength(nx)
};

procedure iterate(nx: Sequence<int>, x: int, k: int): int;

procedure iterAxioms(nx: Sequence<int>): bool
{
  (forall(x: int) => iterate(nx, x, 0) == x)
  && (forall(x: int) => forall(k: int) => k >= 1 ==> 0 <= x ==> x < seqLength(nx) ==>
        iterate(nx, x, k) == iterate(nx, seqSelect(nx, x), k - 1))
};

procedure cycleLength(nx: Sequence<int>, x0: int) returns (lambda: int)
  requires closed(nx)
  requires iterAxioms(nx)
  requires 0 <= x0 && x0 < seqLength(nx)
  opaque
  ensures 1 <= lambda
{
  var t: int := seqSelect(nx, x0);
  var h: int := seqSelect(nx, seqSelect(nx, x0));
  var steps: int := 1;
  while (t != h)
    invariant 1 <= steps
    invariant 0 <= t && t < seqLength(nx)
    invariant 0 <= h && h < seqLength(nx)
    invariant t == iterate(nx, x0, steps)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant h == iterate(nx, x0, 2 * steps)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    t := seqSelect(nx, t);
    h := seqSelect(nx, h);
    steps := steps + 1
  };
  var len: int := 1;
  var probe: int := seqSelect(nx, t);
  while (probe != t)
    invariant 1 <= len
    invariant 0 <= probe && probe < seqLength(nx)
    invariant probe == iterate(nx, t, len)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    probe := seqSelect(nx, probe);
    len := len + 1
  };
  lambda := len
};
#end
