/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def datatypeProgram := r"
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

// Construction and destructor access
procedure testConstruction() {
  var xs: IntList := Cons(42, Nil());
  assert IntList..head(xs) == 42;
}

// Constructor testing
procedure testConstructorTest() {
  var xs: IntList := Cons(1, Nil());
  assert IntList..isCons(xs);
  assert !IntList..isNil(xs);

  var ys: IntList := Nil();
  assert IntList..isNil(ys);
  assert !IntList..isCons(ys);
}

// Nested construction and deconstruction
procedure testNested() {
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert IntList..isCons(xs);
  assert IntList..head(xs) == 1;
  assert IntList..isCons(IntList..tail(xs));
  assert IntList..head(IntList..tail(xs)) == 2;
  assert IntList..isNil(IntList..tail(IntList..tail(xs)));
}

// Datatype in function
function listHead(xs: IntList): int
  requires IntList..isCons(xs)
{
  IntList..head(xs)
}

procedure testFunction() {
  var xs: IntList := Cons(10, Nil());
  var h: int := listHead(xs);
  assert h == 10;
}

// Failing assertion
procedure testFailing() {
  var xs: IntList := Nil();
  assert IntList..isCons(xs);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "Datatypes" datatypeProgram 14 processLaurelFile

end Laurel
