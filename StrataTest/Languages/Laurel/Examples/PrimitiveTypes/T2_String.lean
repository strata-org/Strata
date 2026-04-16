/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r#"
procedure testStringKO()
returns (result: string)
requires true
  opaque
{
  var message: string := "Hello";
  assert(message == "Hell");
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  return message
};

procedure testStringOK()
returns (result: string)
requires true
  opaque
{
  var message: string := "Hello";
  assert(message == "Hello");

  return message
};

procedure testStringLiteralConcatOK()
requires true
  opaque
{
  var result: string := "a" ++ "b";
  assert(result == "ab")
};

procedure testStringLiteralConcatKO()
requires true
  opaque
{
  var result: string := "a" ++ "b";
  assert(result == "cd")
//^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testStringVarConcatOK()
requires true
  opaque
{
  var x: string := "Hello";
  var result: string := x ++ " World";
  assert(result == "Hello World")
};

procedure testStringVarConcatKO()
requires true
  opaque
{
  var x: string := "Hello";
  var result: string := x ++ " World";
  assert(result == "Goodbye")
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"#

#guard_msgs(drop info, error) in
#eval testInputWithOffset "String" program 14 processLaurelFile
