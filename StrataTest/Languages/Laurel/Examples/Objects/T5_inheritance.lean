/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
composite Base {
  var xValue: int
}

composite Extender extends Base {
  var yValue: int
}

procedure typeCheckingAndCasting() {
  var a: Base := new Base;
  assert a is Base;
  assert !(a is Extender);
  var b: Extender := new Extender;
  assert b is Base;
  assert b is Extender;

  var c: Base := b;
  var d: Extender := c as Extender;
  var e: Extender := a as Extender;
//                   ^^^^^^^^^^^^^ error: assertion could not be proved

  b#xValue := 1;
  b#yValue := 2;
}
"

#guard_msgs (drop info) in
#eval testInputWithOffset "Inheritance" program 14 processLaurelFile
