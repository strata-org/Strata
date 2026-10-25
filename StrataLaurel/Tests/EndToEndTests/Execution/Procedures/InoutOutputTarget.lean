/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## An inout output may be assigned to any target

An inout parameter is declared by giving an input and an output the same name. Call
arguments are passed by value and the outputs are assigned to the targets by position,
so the target at an inout position need not be the variable passed as the argument.
`assign t, u := f(x)` sets `t` and `u` and leaves `x` unchanged, and
`assign a, x := f(x)` sets `a` from the inout output and `x` from the ordinary one.

The same holds where an earlier pass picks the targets: `ContractPass` binds each output
of a call with a postcondition to a fresh temp, and `EliminateExceptions` binds a
throwing call's inout outputs alongside its `Result`.
-/

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure f(x: int) returns (x: int, a: int)
  opaque
  ensures x == 5 && a == 7
{
  x := 5;
  a := 7
};
procedure otherTarget()
  entry
  opaque
{
  var x: int := 1;
  var t: int := 0;
  var u: int := 0;
  assign t, u := f(x);
  assert t == 5;
  assert u == 7;
  assert x == 1;
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
procedure swappedTargets()
  entry
  opaque
{
  var x: int := 1;
  var a: int := 0;
  assign a, x := f(x);
  assert a == 5;
  assert x == 7;
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
procedure declaredTargets()
  entry
  opaque
{
  var x: int := 1;
  assign var t: int, var u: int := f(x);
  assert t == 5 && u == 7 && x == 1
};
procedure sameTarget()
  entry
  opaque
{
  var x: int := 1;
  var u: int := 0;
  assign x, u := f(x);
  assert x == 5 && u == 7
};
#end

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite E {}
procedure g(x: int) returns (x: int)
  opaque
  ensures x == 5
{
  x := 5
};
procedure h(x: int) returns (x: int)
  throws (e: E)
  opaque
  ensures x == 5
{
  x := 5
};
procedure expressionPosition()
  entry
  opaque
{
  var x: int := 1;
  var z: int := g(x) + 1;
  assert z == 6 && x == 1
};
procedure throwingCallee()
  entry
  opaque
{
  var x: int := 1;
  var t: int := 0;
  try {
    assign t := h(x)
  } catch e {
    t := 5
  };
  assert t == 5 && x == 1
};
#end

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (x: T)
  opaque
  ensures x == old(x)
{
};
procedure genericCallee()
  entry
  opaque
{
  var x: int := 1;
  var b: bool := true;
  var t: int := 0;
  var c: bool := false;
  assign t := idp(x);
  assign c := idp(b);
  assert t == 1 && c;
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs (drop info) in
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite E {}
procedure h(x: int) returns (x: int)
  throws (e: E)
  opaque
  modifies *
{
  x := 9;
  var e: E := new E;
  throw e
};
procedure throwLeavesOtherTarget()
  entry
  opaque
  modifies *
{
  var x: int := 1;
  var t: int := 0;
  try { assign t := h(x) } catch e { assert t == 0 };
  assert x == 1
};
procedure throwLeavesInPlaceTarget()
  entry
  opaque
  modifies *
{
  var x: int := 1;
  try { assign x := h(x) } catch e { assert x == 1 }
};
#end
