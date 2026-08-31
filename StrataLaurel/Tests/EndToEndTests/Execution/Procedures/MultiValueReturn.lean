/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `return e1, …, en` supplies one value per output

Each case runs on the verifier and on both interpreters. -/

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure swap(a: int, b: int) returns (x: int, y: int)
  opaque
  ensures x == b && y == a
{
  return b, a
};

// The values are read before any output is written: on outputs `(p, q)`,
// `return q, p` swaps them rather than yielding `q, q`.
procedure swapOwnOutputs() returns (p: int, q: int)
  opaque
  ensures p == 2 && q == 1
{
  p := 1;
  q := 2;
  return q, p
};

procedure firstPositive(n: int) returns (found: bool, value: int)
  opaque
  ensures (n > 0) == found
  ensures found ==> value == n
{
  if n > 0 then {
    return true, n
  };
  return false, 0
};

procedure transparentPair(a: int) returns (lo: int, hi: int)
{
  return a, a + 1
};

// An inout among the outputs: `x` is both an input and an output.
procedure bumpAndReport(x: int) returns (x: int, prev: int)
  opaque
  ensures prev == old(x)
  ensures x == prev + 1
{
  return x + 1, x
};

procedure main() entry
{
  assign var x: int, var y: int := swap(1, 2);
  assert x == 2;
  assert y == 1;

  assign var p: int, var q: int := swapOwnOutputs();
  assert p == 2;
  assert q == 1;

  assign var f1: bool, var v1: int := firstPositive(5);
  assert f1;
  assert v1 == 5;
  assign var f2: bool, var v2: int := firstPositive(-3);
  assert !f2;

  assign var lo: int, var hi: int := transparentPair(7);
  assert lo == 7;
  assert hi == 8;

  var c: int := 10;
  var o: int;
  assign c, o := bumpAndReport(c);
  assert c == 11;
  assert o == 10
};
#end

/-! A wrong expectation fails on every path, so the cases above are not passing
vacuously. -/

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure swap(a: int, b: int) returns (x: int, y: int)
  opaque
  ensures x == b && y == a
{
  return b, a
};

procedure main() entry
{
  assign var x: int, var y: int := swap(1, 2);
  assert x == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end
