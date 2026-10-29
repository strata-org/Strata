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

procedure fib(n: int): int;

procedure fibIter(n: int) returns (r: int)
  requires n >= 0
  requires fib(0) == 0
  requires fib(1) == 1
  requires forall(k: int) => k >= 2 ==> fib(k) == fib(k - 1) + fib(k - 2)
  opaque
  ensures r == fib(n)
{
  if n == 0 then { r := 0 }
  else {
    var prev: int := 0;
    var cur: int := 1;
    var i: int := 1;
    while (i < n)
      invariant 1 <= i
      invariant i <= n
      invariant cur == fib(i)
      invariant prev == fib(i - 1)
    {
      i := i + 1;
      var next: int := cur + prev;
      prev := cur;
      cur := next
    };
    r := cur
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure fib(n: int): int;

procedure fibIter(n: int) returns (r: int)
  requires n >= 0
  requires fib(0) == 0
  requires fib(1) == 1
  requires forall(k: int) => k >= 2 ==> fib(k) == fib(k - 1) + fib(k - 2)
  opaque
  ensures r == fib(n)
{
  if n == 0 then { r := 0 }
  else {
    var prev: int := 0;
    var cur: int := 1;
    var i: int := 1;
    while (i < n)
      invariant 1 <= i
      invariant i <= n
      invariant cur == fib(i)
      invariant prev == fib(i - 1)
//              ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    {
      i := i + 1;
      var next: int := cur + prev;
      cur := next;
      prev := cur
    };
    r := cur
  }
};
#end
