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
composite Container {
  var intValue: int // var indicates mutable field
  var realValue: real
  var boolValue: bool
  var stringValue: string
}

procedure newsAreNotEqual()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  assert c != d
};

procedure simpleAssign()
  opaque
{
  var c: Container := new Container;
  var iv: int := c#intValue;
  var rv: real := c#realValue;
  var boolVar: bool := c#boolValue;
  var sv: string := c#stringValue;

  c#intValue := 2;
  c#realValue := 3.0;
  c#boolValue := true;
  c#stringValue := "hello";

  assert c#intValue == 2;
  assert c#realValue == 3.0;
  assert c#boolValue == true;
  assert c#stringValue == "hello"
};

procedure updatesAndAliasing()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;

  var initialCValue: int := c#intValue;
  var initialDValue: int := d#intValue;
  d#intValue := d#intValue + 1;
  assert initialCValue == c#intValue;
  c#intValue := c#intValue + 1;
  assert initialCValue + 1 == c#intValue;
  assert initialDValue + 1 == d#intValue;

  var dAlias: Container := d;
  dAlias#intValue := dAlias#intValue + 1;
  assert dAlias#intValue == d#intValue
};

procedure subsequentHeapMutations(c: Container)
  opaque
  modifies c
{
  // The additional parenthesis on the next line are needed to let the parser succeed. Joe, any idea why this is needed?
  var sum: int := ((c#intValue := 1) + c#intValue) + (c#intValue := 2);
  assert sum == 4
};

procedure implicitEquality(c: Container, d: Container)
  opaque
  modifies c
  modifies d
{
  c#intValue := 1;
  d#intValue := 2;
  if c#intValue == d#intValue then {
    assert c == d
  } else {
    // Somehow we can't prove this here
    // assert c != d;
  }
};

procedure useBool(c: Container) returns (r: bool)
  opaque
{
  r := c#boolValue
};

composite SameFieldName {
  var intValue: bool
}

procedure sameFieldNameDifferentType(a: Container, b: SameFieldName)
  opaque
  modifies a
  modifies b
{
  a#intValue := 1;
  b#intValue := true;

  assert a#intValue == 1;
  assert b#intValue
};

datatype Color {
  Red(),
  Green(),
  Blue()
}

composite Pixel {
  var x: int
  var color: Color
}

procedure datatypeField()
  opaque
{
  var p: Pixel := new Pixel;
  p#color := Red();
  assert Color..isRed(p#color);
  p#color := Blue();
  assert Color..isBlue(p#color);
  assert !Color..isRed(p#color)
};

// Following test-cases can't be run because Core procedures are not transparent.
// procedure modifiesFirst(c: Container, d: Container) returns (x: int) {
//  c#intValue := 3;
//  3
// }

// procedure caller() {
//   var c: Container := new Container;
//   var d: Container := new Container;
//   assume d#intValue == 1;
//   var x: int := modifiesFirst(c, d);
//   assert d#intValue == 1;
// }

// procedure allowHeapMutatingCallerInExpression() {
//   var c: Container := new Container;
//   var d: Container := new Container;
//   assume d#intValue == 1;
//   var x: int := modifiesFirst(c, d) + 1;
//   assert d#intValue == 1;
//   assert x == 4;
// }
"#

#guard_msgs(drop info, error) in
#eval testInputWithOffset "MutableFields" program 14 processLaurelFile
