/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple <|
#strata
program Laurel;
procedure testStringKO()
  returns (result: string)
  entry
  opaque
{
  var message: string := "Hello";
  assert(message == "Hell");
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  return message
};

procedure testStringOK()
returns (result: string)
  entry
  opaque
{
  var message: string := "Hello";
  assert(message == "Hello");

  return message
};

procedure testStringLiteralConcatOK()
  entry
  opaque
{
  var result: string := "a" ^ "b";
  assert(result == "ab")
};

procedure testStringLiteralConcatKO()
  entry
  opaque
{
  var result: string := "a" ^ "b";
  assert(result == "cd")
//^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testStringVarConcatOK()
  entry
  opaque
{
  var x: string := "Hello";
  var result: string := x ^ " World";
  assert(result == "Hello World")
};

procedure testStringVarConcatKO()
  entry
  opaque
{
  var x: string := "Hello";
  var result: string := x ^ " World";
  assert(result == "Goodbye")
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
