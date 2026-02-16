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
{
  var message: string := "Hello";
  assert(message == "Hell");
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  return message;
}

procedure testStringOK()
returns (result: string)
requires true
{
  var message: string := "Hello";
  assert(message == "Hello");

  return message;
}
"#

#guard_msgs(drop info, error) in
#eval testInputWithOffset "String" program 14 processLaurelFile
