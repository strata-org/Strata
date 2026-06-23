/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
End-to-end verification of C-style compound assignment (`+=`, `-=`, `*=`,
`/=`, `%=`, and `^=` for string concatenation), on locals (first program) and on composite-type fields
including chained targets (second program), in both statement and expression
positions.

`x op= e` lowers (in `EliminateIncrDecr`) to `x := x op e` and yields the new
value. The accepted element types are per-operator: `+= -= *= /=` work on `int`
and `real`; `%=` is `int`-only; `^=` is `string`-only. (Rejections are covered in
`CompoundAssignTypeRejectionTest.lean`; the `++`/`--`-vs-`+=` real asymmetry is
pinned there too.)

Field targets go through Laurel's heap parameterization: `EliminateIncrDecr`
(pass 1) lowers `(c#n) += e` to `c#n := c#n + e`; `HeapParameterization` (pass 5)
rewrites the field-assign into `$tmp`/`$heap` local-target sequences, so by the
time `LiftImperativeExpressions` (pass 11) runs every assignment target is a
local. `c#n += e` parses paren-free because `fieldAccess` (prec 95) binds tighter
than `+=` (prec 10).
-/

#eval testLaurel <|
#strata
program Laurel;
constrained nat = v: int where v >= 0 witness 0
procedure intOperators()
  opaque
{
  var x: int := 10;
  x += 5;
  assert x == 15;
  x -= 3;
  assert x == 12;
  x *= 2;
  assert x == 24;
  x /= 4;
  assert x == 6;
  x %= 4;
  assert x == 2
};

procedure exprYieldsNewValue()
  opaque
{
  var x: int := 5;
  // Compound assignment in expression position yields the NEW value.
  var y: int := (x += 2);
  assert x == 7;
  assert y == 7
};

procedure exprYieldsNewValueNonPlus()
  opaque
{
  // The yielded value is the new value for every operator, not just `+=`.
  var x: int := 10;
  var y: int := (x -= 3);
  assert x == 7;
  assert y == 7;
  var s: string := "a";
  var t: string := (s ^= "b");
  assert s == "ab";
  assert t == "ab"
};

procedure intDivMod()
  opaque
{
  // Integer `/=` truncates and `%=` is the matching remainder (not exact division).
  var x: int := 7;
  x /= 2;
  assert x == 3;
  var w: int := 7;
  w %= 3;
  assert w == 1
};

procedure nestedRhs()
  opaque
{
  var x: int := 1;
  var y: int := 10;
  // RHS itself contains a compound assignment; lowered bottom-up.
  x += (y += 1);
  assert y == 11;
  assert x == 12
};

procedure realOperators()
  opaque
{
  var r: real := 1.5;
  r += 2.5;
  assert r == 4.0;
  r -= 1.0;
  assert r == 3.0;
  r *= 2.0;
  assert r == 6.0;
  r /= 2.0;
  assert r == 3.0
};

procedure stringConcat()
  opaque
{
  var s: string := "foo";
  s ^= "bar";
  assert s == "foobar"
};

procedure constrainedInt()
  opaque
{
  var n: nat := 3;
  n += 2;
  assert n == 5
};

procedure rightAssocChain()
  opaque
{
  // The ops are `rightassoc`, so `a += b += c` groups as `a += (b += c)`.
  var a: int := 1;
  var b: int := 2;
  var c: int := 3;
  a += b += c;
  // b += c : b becomes 5, yields 5; a += 5 : a becomes 6.
  assert b == 5;
  assert a == 6
};
#end

-- Compound assignment on composite-type fields, including chained targets.
#eval testLaurel <|
#strata
program Laurel;
composite Counter {
  var n: int
}

composite Inner {
  var count: int
}

composite Outer {
  var inner: Inner
}

composite RBox {
  var r: real
}

composite SBox {
  var s: string
}

procedure fieldStatement()
  opaque
{
  var c: Counter := new Counter;
  c#n := 10;
  c#n += 5;
  assert c#n == 15;
  c#n -= 3;
  assert c#n == 12;
  c#n *= 2;
  assert c#n == 24
};

procedure fieldInExpression()
  opaque
{
  var c: Counter := new Counter;
  c#n := 5;
  // Yields the NEW field value (7); c#n is updated to 7.
  var y: int := (c#n += 2);
  assert c#n == 7;
  assert y == 7
};

// Compound assign through a chained field target (`o#inner#count += e`).
procedure chainedFieldStatement()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;
  o#inner#count := 10;
  o#inner#count += 5;
  assert o#inner#count == 15
};

procedure chainedFieldInExpression()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;
  o#inner#count := 5;
  var y: int := (o#inner#count += 2);
  assert o#inner#count == 7;
  assert y == 7
};

// Non-`+=`/`int` operators on field targets: real `/=`, string `^=`, and an
// int field `/=` (whose lowered division-by-zero VC must discharge for a
// constant nonzero divisor). These exercise the field heap-rewrite path for
// the operators the single `c#n += …` cases above don't reach.
procedure realFieldDiv()
  opaque
{
  var b: RBox := new RBox;
  b#r := 6.0;
  b#r /= 2.0;
  assert b#r == 3.0
};

procedure stringFieldConcat()
  opaque
{
  var b: SBox := new SBox;
  b#s := "foo";
  b#s ^= "bar";
  assert b#s == "foobar"
};

procedure intFieldDiv()
  opaque
{
  var c: Counter := new Counter;
  c#n := 7;
  c#n /= 2;
  assert c#n == 3
};
#end
