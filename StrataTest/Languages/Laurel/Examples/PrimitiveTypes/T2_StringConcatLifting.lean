/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 26:2-23  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure stringConcatWithAssignment()
  opaque
{
  var x: string := "Hello";
  var y: string := x ++ (x := " World");
  assert y == "Hello World";
  assert x == " World"
};

procedure stringConcatOK()
  opaque
{
  var a: string := "Hello";
  var b: string := " World";
  var c: string := a ++ b;
  assert c == "Hello World"
};

procedure stringConcatKO()
  opaque
{
  var a: string := "Hello";
  var b: string := " World";
  var c: string := a ++ b;
  assert c == "Goodbye"
};
#end
