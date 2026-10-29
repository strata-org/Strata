/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Integer arithmetic (`+ - * / %`) and unary negation (`-x`) -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testArithmetic()
  entry
  opaque
{
    var a: int := 10;
    var b: int := 3;
    assert (a + b) == 13;
    var x: int := a - b;
    assert x == 7;
    var y: int := x * 2;
    assert y == 14;
    var z: int := y / 2;
    assert z == 7;
    var r: int := 17 % 5;
    assert r == 2
};

procedure testUnary()
  entry
  opaque
{
    var x: int := 5;
    var y: int := -x;
    assert y == 0 - 5
};

procedure testEuclideanDivMod()
  entry
  opaque
{
    assert (0 - 7) / 3 == 0 - 3;
    assert (0 - 7) % 3 == 2
};

procedure testArithmeticNegative()
  entry
  opaque
{
    var x: int := 10;
    var y: int := 4;
    assert (x + y) == 99
//  ^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testUnaryNegative()
  entry
  opaque
{
    var x: int := 10;
    var n: int := -x;
    assert n == 10
//  ^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Inequality (`!=`) on `bool` and `string` -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testInequality()
  entry
  opaque
{
  assert (true != false) == true;
  assert ("hello" != "world") == true
};

procedure testInequalityNegative()
  entry
  opaque
{
  assert (true != true) == true
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Logical operators -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testLogical()
  entry
  opaque
{
    var t: bool := true;
    var f: bool := false;
    var a: bool := t && f;
    assert a == false;
    var b: bool := t || f;
    assert b == true;
    var c: bool := !f;
    assert c == true;
    assert (t == t) == true
};
#end

/-! `==>` (implies) -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testImplies()
  entry
  opaque
{
    var t: bool := true;
    var f: bool := false;
    assert t ==> t;
    assert f ==> t
};
#end

/-! `/t` and `%t` (truncating division / remainder) -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testTruncatingDiv()
  entry
  opaque
{
    assert 7 /t 3 == 2;
    assert 7 %t 3 == 1;
    assert (0 - 7) /t 3 == 0 - 2;
    assert (0 - 7) %t 3 == 0 - 1
};
#end
