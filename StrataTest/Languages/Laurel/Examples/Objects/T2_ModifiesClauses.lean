/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
A modifies clause CAN be placed on any procedure to generate a modifies axiom.
The modifies clause determines which references the procedure may modify.
This modifies axiom states how the in and out heap of the procedure relate.

A modifies clause is crucial on opaque procedures,
since otherwise all heap state is lost after calling them.

-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
composite Container {
  var value: int
}

procedure modifyContainerOpaque(c: Container)
  ensures true // makes this procedure opaque. Maybe we should use explicit syntax
  modifies c
{
  c#value := c#value + 1;
}

procedure modifyContainerTransparant(c: Container)
{
  c#value := c#value + 1;
}

procedure caller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifyContainerOpaque(c)
  assert x == d#value; // pass
}

// This test-case does not work yet.
// Because Core procedures never have transparent bodies
//procedure modifyContainerWithPermission1(c: Container, d: Container)
//   ensures true
//   modifies c
//{
//    modifyContainerTransparant(c);
//}

procedure modifyContainerWithoutPermission1(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// the above error is because the body does not satisfy the empty modifies clause. error needs to be improved
   ensures true
{
    modifyContainerTransparant(c)
}

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
  ensures true
  modifies d
{
    c#value := 2;
}

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
  ensures true
  modifies d
{
    modifyContainerTransparant(c)
}

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  modifies c
  modifies d

procedure multipleModifiesClausesCaller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e)
  assert x == e#value; // pass
}

procedure newObjectDoNotCountForModifies()
  ensures true
{
  var c: Container := new Container;
  c#value := 1;
}
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ModifiesClauses" program 24 processLaurelFile
