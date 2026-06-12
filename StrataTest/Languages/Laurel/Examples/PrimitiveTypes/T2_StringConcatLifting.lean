/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;
procedure stringConcatWithAssignment()
  opaque
{
  var x: string := "Hello";
  var y: string := x ^ (x := " World");
  assert y == "Hello World";
  assert x == " World"
};

procedure stringConcatOK()
  opaque
{
  var a: string := "Hello";
  var b: string := " World";
  var c: string := a ^ b;
  assert c == "Hello World"
};

procedure stringConcatKO()
  opaque
{
  var a: string := "Hello";
  var b: string := " World";
  var c: string := a ^ b;
  assert c == "Goodbye"
//^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
