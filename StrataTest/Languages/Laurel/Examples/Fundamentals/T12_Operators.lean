/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def operatorsProgram := r"
procedure testArithmetic() {
    var a: int := 10;
    var b: int := 3;
    var x: int := a - b;
    assert x == 7;
    var y: int := x * 2;
    assert y == 14;
    var z: int := y / 2;
    assert z == 7;
    var r: int := 17 % 5;
    assert r == 2;
}

procedure testLogical() {
    var t: bool := true;
    var f: bool := false;
    var a: bool := t && f;
    assert a == false;
    var b: bool := t || f;
    assert b == true;
    var c: bool := !f;
    assert c == true;
    assert t ==> t;
    assert f ==> t;
}

procedure testUnary() {
    var x: int := 5;
    var y: int := -x;
    assert y == 0 - 5;
}

procedure testTruncatingDiv() {
    assert 7 /t 3 == 2;
    assert 7 %t 3 == 1;
    assert (0 - 7) /t 3 == 0 - 2;
    assert (0 - 7) %t 3 == 0 - 1;
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Operators" operatorsProgram 14 processLaurelFile

end Laurel
