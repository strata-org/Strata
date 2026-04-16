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

procedure modifyContainerOpaque(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  true
};

procedure caller()
  opaque
//        ^^^^^^ error: postcondition does not hold
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := modifyContainerOpaque(c);
  assert x == d#value
};
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
  opaque
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  modifies d
{
    c#value := 2
};

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  opaque
  modifies c
  modifies d
;

procedure multipleModifiesClausesCaller()
  opaque
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
{
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e);
  assert x == e#value
};
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

procedure newObjectDoNotCountForModifies()
  opaque
{
  var c: Container := new Container;
  c#value := 1
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ModifiesClauses" program 24 processLaurelFile
