/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 53:4-17  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure testDecimalLiterals()
  opaque
{
    var a: real := 1.5;
    var b: real := 2.5;
    assert a == 1.5;
    assert b == 2.5;
    assert a != b
};

procedure testDecimalArithmetic()
  opaque
{
    var a: real := 1.5;
    var b: real := 2.5;
    var sum: real := a + b;
    assert sum == 4.0;
    var diff: real := b - a;
    assert diff == 1.0;
    var prod: real := a * b;
    assert prod == 3.75;
    var quot: real := b / a;
    assert quot == 5.0 / 3.0
};

procedure testDecimalNeg()
  opaque
{
    var a: real := 1.5;
    var neg: real := -a;
    assert neg == 0.0 - 1.5
};

procedure testDecimalComparisons()
  opaque
{
    var a: real := 1.5;
    var b: real := 2.5;
    assert a < b;
    assert a <= b;
    assert b > a;
    assert b >= a;
    assert a <= a;
    assert a >= a
};

procedure testDecimalAssertFails()
  opaque
{
    var a: real := 1.5;
    var b: real := 2.5;
    assert a == b
};
#end
