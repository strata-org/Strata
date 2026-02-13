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
composite Container {
  var intValue: int // var indicates mutable field
  var boolValue: bool
}

procedure foo(c: Container, d: Container) returns (r: int)
  requires c != d && d#intValue == 1
  ensures d#intValue == 3
{
  var x: int := c#intValue;
  var initialDValue: int := d#intValue;
  d#intValue := d#intValue + 1;
  c#intValue := c#intValue + 1;
  assert x + 1 == c#intValue; // pass
  assert initialDValue + 1 == d#intValue;

  var e: Container := d;
  e#intValue := e#intValue + 1;
  assert e#intValue == d#intValue;
}

procedure useBool(c: Container) returns (r: bool) {
  r := c#boolValue;
}

procedure caller(c: Container, d: Container) {
  assume d#intValue == 1;
  assume c != d;
  var x: int := foo(c, d);
  assert d#intValue == 3;
}

procedure allowHeapMutatingCallerInExpression(c: Container, d: Container) {
  assume d#intValue == 1;
  assume c != d;
  var x: int := foo(c, d) + 1;
  assert d#intValue == 3;
}

procedure subsequentHeapMutations(c: Container) {
  // The additional parenthesis on the next line are needed to let the parser succeed. Joe, any idea why this is needed?
  var sum: int := ((c#intValue := 1;) + c#intValue) + (c#intValue := 2;);
  assert sum == 4;
}

procedure implicitEquality(c: Container, d: Container) {
  c#intValue := 1;
  d#intValue := 2;
  if (c#intValue == d#intValue) {
// ATM, the assertion in this test is proven not to hold even though it holds
    assert c == d;
//  ^^^^^^^^^^^^^^ error: assertion does not hold
  } else {
    assert c != d;
  }
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "MutableFields" program 14 processLaurelFile
