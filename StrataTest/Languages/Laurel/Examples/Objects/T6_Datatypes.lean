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
procedure testConstruction()
  opaque
{
  var xs: IntList := Cons(42, Nil());
  assert IntList..head(xs) == 42
};

// Constructor testing
procedure testConstructorTest()
  opaque
{
  var xs: IntList := Cons(1, Nil());
  assert IntList..isCons(xs);
  assert !IntList..isNil(xs);

  var ys: IntList := Nil();
  assert IntList..isNil(ys);
  assert !IntList..isCons(ys)
};

// Nested construction and deconstruction
procedure testNested()
  opaque
{
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert IntList..isCons(xs);
  assert IntList..head(xs) == 1;
  assert IntList..isCons(IntList..tail(xs));
  assert IntList..head(IntList..tail(xs)) == 2;
  assert IntList..isNil(IntList..tail(IntList..tail(xs)))
};

procedure unsafeDestructor()
  opaque
{
  var nil: IntList := Nil();
  var noError: int := IntList..head!(nil);
  var error: int := IntList..head(nil)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Datatype in function
function listHead(xs: IntList): int
  requires IntList..isCons(xs)
{
  IntList..head(xs)
};

procedure testFunction()
  opaque
{
  var xs: IntList := Cons(10, Nil());
  var h: int := listHead(xs);
  assert h == 10
};

// Failing assertion
procedure testFailing()
  opaque
{
  var xs: IntList := Nil();
  assert IntList..isCons(xs)
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Mutually recursive datatypes: even/odd-length lists
datatype EvenList {
  ENil(),
  ECons(head: int, tail: OddList)
}

datatype OddList {
  OCons(head: int, tail: EvenList)
}

procedure testMutualConstruction()
  opaque
{
  var even: EvenList := ENil();
  assert EvenList..isENil(even);
  var odd: OddList := OCons(1, ENil());
  assert OddList..isOCons(odd);
  assert OddList..head(odd) == 1;
  var even2: EvenList := ECons(2, OCons(3, ENil()));
  assert EvenList..isECons(even2);
  assert EvenList..head(even2) == 2
};

datatype RootBeforeLeaf { RootBeforeLeafC(leaf: LeafAfterRoot) }
datatype LeafAfterRoot { LeafAfterRootC }
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "Datatypes" datatypeProgram 14 processLaurelFile

end Laurel
