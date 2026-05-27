/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 7:2-27  error: assertion does not hold
33:2-24  error: assertion does not hold
49:2-29  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure testStringKO()
returns (result: string)
  opaque
{
  var message: string := "Hello";
  assert(message == "Hell");

  return message
};

procedure testStringOK()
returns (result: string)
  opaque
{
  var message: string := "Hello";
  assert(message == "Hello");

  return message
};

procedure testStringLiteralConcatOK()
  opaque
{
  var result: string := "a" ++ "b";
  assert(result == "ab")
};

procedure testStringLiteralConcatKO()
  opaque
{
  var result: string := "a" ++ "b";
  assert(result == "cd")
};

procedure testStringVarConcatOK()
  opaque
{
  var x: string := "Hello";
  var result: string := x ++ " World";
  assert(result == "Hello World")
};

procedure testStringVarConcatKO()
  opaque
{
  var x: string := "Hello";
  var result: string := x ++ " World";
  assert(result == "Goodbye")
};
#end
