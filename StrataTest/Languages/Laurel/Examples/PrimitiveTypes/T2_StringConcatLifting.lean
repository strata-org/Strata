/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def stringConcatLiftingProgram := r#"
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
//^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"#

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "StringConcatLifting" stringConcatLiftingProgram 14 processLaurelFile

end Laurel
