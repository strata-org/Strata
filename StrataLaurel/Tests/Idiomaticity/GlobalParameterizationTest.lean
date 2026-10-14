/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Shows what the file-scope global variable encoding looks like after the
`GlobalParameterization` pass. Globals are eliminated by threading them
through procedure signatures:

- a procedure that only *reads* a global gains an extra input parameter;
- a procedure that *writes* a global gains both an input and a same-named
  output (an "inout" parameter), so the updated value flows back to callers;
- call sites thread the caller's copy of the state: calls to writers become
  assignments (`g := writer(g)`), and a writer call in *value* position is
  rewritten into a block expression that first captures the hidden outputs
  (`assign g, var $g_tmp0 := f(g); $g_tmp0`) and then yields the original
  result.

Structural edge cases (name collisions, recursion, shadowing, metadata, …)
are covered in `StrataLaurel/Tests/UnitTests/GlobalParameterizationTest.lean`.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.EliminateValueInReturns
import StrataLaurel.Implementation.GlobalParameterization
import StrataLaurel.Implementation.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def printGlobalParam := printGlobalParameterization false

/--
info: procedure outer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := writer(someGlobal);
  var x: int := reader(someGlobal)
};
procedure writer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := 3
};
procedure reader(someGlobal: int)
  returns (r: int)
{
  r := someGlobal + 1;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var someGlobal: int := 0
procedure outer() {
  writer();
  var x: int := reader()
};
procedure writer() {
  someGlobal := 3
};
procedure reader() returns (r: int) {
  return someGlobal + 1
};
#end

/--
info: procedure bump(g: int)
  returns (g: int, r: int)
{
  g := g + 1;
  r := g;
  return
};
procedure useValue(g: int)
  returns (g: int, r: int)
{
  r := {
    assign g, var $g_tmp0: int := bump(g);
    $g_tmp0
  } + 1;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) {
  g := g + 1;
  return g
};
procedure useValue() returns (r: int) {
  return bump() + 1
};
#end

/--
info: procedure writesA(a: int)
  returns (a: int)
{
  a := 1
};
procedure readsB(b: int)
  returns (r: int)
{
  r := b;
  return
};
procedure both(a: int, b: int)
  returns (a: int, r: int)
{
  a := writesA(a);
  r := readsB(b);
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var a: int := 0
var b: int := 0
procedure writesA() {
  a := 1
};
procedure readsB() returns (r: int) {
  return b
};
procedure both() returns (r: int) {
  writesA();
  return readsB()
};
#end

/--
info: procedure main()
  entry
  opaque
{
  var someGlobal: int := 0;
  var other: bool := true;
  {
    someGlobal := writer(someGlobal);
    var x: int := reader(someGlobal);
    assert other
  }
};
procedure writer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := 3
};
procedure reader(someGlobal: int)
  returns (r: int)
{
  r := someGlobal + 1;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var someGlobal: int := 0
var other: bool := true
procedure main()
  entry
  opaque
{
  writer();
  var x: int := reader();
  assert other
};
procedure writer() {
  someGlobal := 3
};
procedure reader() returns (r: int) {
  return someGlobal + 1
};
#end

/--
info: procedure bump<T>(g: int, x: T)
  returns (g: int, r: T)
{
  g := g + 1;
  r := x;
  return
};
procedure useTwo(g: int)
  returns (g: int, r: int)
{
  var a: int := {
    assign g, var $g_tmp0: int := bump(g, 5);
    $g_tmp0
  };
  var b: bool := {
    assign g, var $g_tmp1: bool := bump(g, true);
    $g_tmp1
  };
  r := a;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure bump<T>(x: T) returns (r: T) {
  g := g + 1;
  return x
};
procedure useTwo() returns (r: int) {
  var a: int := bump(5);
  var b: bool := bump(true);
  return a
};
#end

end Strata.Laurel
