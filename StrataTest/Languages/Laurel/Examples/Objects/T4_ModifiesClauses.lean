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

procedure caller(c: Container, d: Container) {
  assume c != d;
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
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an opaque procedure that mutates the heap must have a modifies clause
   ensures true
{
    modifyContainerTransparant(c)
}

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
  ensures true
  modifies d
//         ^ error: assertion could not be proved
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
{
    c#value := 2;
}

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
  ensures true
  modifies d
//         ^ error: assertion does not hold
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
{
    modifyContainerTransparant(c)
}

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  modifies c
  modifies d

procedure multipleModifiesClausesCaller(c: Container, d: Container, e: Container) {
  assume c != d;
  assume d != e;
  assume c != e;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e)
  assert x == e#value; // pass
}
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ModifiesClauses" program 24 processLaurelFile
