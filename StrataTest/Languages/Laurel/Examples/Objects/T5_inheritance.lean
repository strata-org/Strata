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

composite Base2 {
  var yValue: int
}

composite Extender extends Base, Base2 {
  var zValue: int
}

procedure inheritedFields(a: Extender) {
  a#xValue := 1;
  a#yValue := 2;
  a#zValue := 3;

  assert a#xValue == 1;
  assert a#yValue == 2;
  assert a#zValue == 3;
}

procedure typeCheckingAndCasting() {
  var a: Base := new Base;
  assert a is Base;
  assert !(a is Extender);
  var b: Extender := new Extender;
  assert b is Base;
  assert b is Base2;
  assert b is Extender;

  var c: Base := b;
  var d: Extender := c as Extender;
  var e: Extender := a as Extender;
//                   ^^^^^^^^^^^^^ error: assertion could not be proved
}

composite Top {
  var tValue: int
}

composite Left extends Top {
  var lValue: int
}
composite Right extends Top {
  var rValue: int
}
composite Bottom extends Left, Right {
  var bValue: int
}

procedure diamondInheritance() {
  var b: Bottom := new Bottom;
  b#lValue := 1;
  b#rValue := 2;
  b#bValue := 3;
  // tValue can not be used

  assert b#lValue == 1;
  assert b#rValue == 2;
  assert b#bValue == 3;

  assert b is Left;
  assert b is Right;
  assert b is Top;
  assert b is Bottom;
}

// Currently does not pass. Implementation needs b type invariant mechanism that we have yet to add.
//procedure typedParameter(b: Bottom) {
//  var b: Bottom := b;
//  assert b is Left;
//  assert b is Right;
//  assert b is Top;
//  assert b is Bottom;
//}
"

#guard_msgs (drop info) in
#eval testInputWithOffset "Inheritance" program 14 processLaurelFile
