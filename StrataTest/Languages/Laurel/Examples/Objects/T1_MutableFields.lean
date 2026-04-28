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

procedure newsAreNotEqual() {
  var c: Container := new Container;
  var d: Container := new Container;
  assert c != d
};

procedure simpleAssign() {
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

procedure subsequentHeapMutations(c: Container) {
  // The additional parenthesis on the next line are needed to let the parser succeed. Joe, any idea why this is needed?
  var sum: int := ((c#intValue := 1) + c#intValue) + (c#intValue := 2);
  assert sum == 4
};

procedure implicitEquality(c: Container, d: Container) {
  c#intValue := 1;
  d#intValue := 2;
  if c#intValue == d#intValue then {
    assert c == d
  } else {
    // Somehow we can't prove this here
    // assert c != d;
  }
};

procedure useBool(c: Container) returns (r: bool) {
  r := c#boolValue
};

composite SameFieldName {
  var intValue: bool
}

procedure sameFieldNameDifferentType(a: Container, b: SameFieldName) {
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

procedure datatypeField() {
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

procedure modifyHeapAndReturnMultiple(c: Container) returns (x: int, y: int, z: int)
  opaque
  ensures x == 1 && y == 2 && z == 3
  modifies c
;

procedure heapModifyingMultipleReturnCaller() {
  var c: Container := new Container;
  var y: int;
  assign var x: int, y, var z: int := modifyHeapAndReturnMultiple(c);
  assert x == 1;
  assert y == 2;
  assert z == 3
};

procedure fieldAssignsFromHeapModifyingMultipleReturnCaller() {
  var c: Container := new Container;
  var y: int;
  assign c#intValue, y, var z: int := modifyHeapAndReturnMultiple(c);
  assert c#intValue == 1;
  assert y == 2;
  assert z == 3
};
"#

#guard_msgs(drop info, error) in
#eval testInputWithOffset "MutableFields" program 14 processLaurelFile
