/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
A field store evaluates its receiver before its value, on every path: the verifier, the
Laurel→Core interpreter and the Laurel interpreter. `x#g := { x := y; 5 }`, used as a value,
stores into the box `x` held before the value reassigned it, and `a#r#b := { a#r := c; false }`
into the box `a#r` held before the value replaced it. `assign x, x#g := boxAndFive(y)`
stores into the box `x` held before the first target reassigned it, and `gb#g := { setGb(c); 5 }`
into the box the global `gb` held before the call replaced it. An update operator does the same:
`a#r#g += setR(a, c)` updates the box `a#r` held before the call replaced it.
-/

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box {
  var b: bool
  var g: int
}
composite A {
  var r: Box
}
procedure setR(a: A, c: Box) returns (o: int)
  opaque
  ensures a#r == c && o == 1
  modifies a
{
  a#r := c;
  o := 1
};
procedure boxAndFive(y: Box) returns (o: Box, v: int)
  opaque
  ensures o == y && v == 5
{
  o := y;
  v := 5
};
procedure storeTakesTheReceiverBeforeTheValueReplacesIt()
  entry
  opaque
  modifies *
{
  var a: A := new A;
  var b0: Box := new Box;
  var c: Box := new Box;
  a#r := b0;
  b0#b := true;
  c#b := true;
  a#r#b := { a#r := c; false };
  assert !b0#b && c#b
};
procedure storeAsValueTakesTheReceiverFirst()
  entry
  opaque
  modifies *
{
  var x: Box := new Box;
  var y: Box := new Box;
  y#g := 0;
  var v: int := x#g := { x := y; 5 };
  assert v == 5 && y#g == 0
};
procedure storeTakesTheReceiverBeforeAnEarlierTargetReassignsIt()
  entry
  opaque
  modifies *
{
  var a: Box := new Box;
  var y: Box := new Box;
  var x: Box := a;
  a#g := 0;
  y#g := 0;
  assign x, x#g := boxAndFive(y);
  assert a#g == 5 && y#g == 0
};
procedure updateTakesTheReceiverBeforeTheValueReplacesIt()
  entry
  opaque
  modifies *
{
  var a: A := new A;
  var b0: Box := new Box;
  var c: Box := new Box;
  b0#g := 10;
  c#g := 20;
  a#r := b0;
  a#r#g += setR(a, c);
  assert b0#g == 11 && c#g == 20
};
#end

/-! The global case runs in verification only: an `entry` procedure that assigns a global
    composite stops at an internal error in GlobalParameterization. -/
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box {
  var g: int
}
var gb: Box := <?>
procedure setGb(b: Box)
  opaque
  ensures gb == b
{
  gb := b
};
procedure storeTakesTheGlobalBeforeACallReplacesIt()
  opaque
  modifies *
{
  var a: Box := new Box;
  var c: Box := new Box;
  gb := a;
  a#g := 0;
  c#g := 0;
  gb#g := { setGb(c); 5 };
  assert a#g == 5 && c#g == 0
};
#end
