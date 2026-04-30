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
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := modifyContainerOpaque(c);
  assert x == d#value // pass
};

// Commented out because
// Transparent assignments are not supported yet
// procedure modifyContainerTransparant(c: Container) returns (i: int)
//{
//  c#value := c#value + 1;
//  7
//};
//procedure modifyContainerWithPermission1(c: Container, d: Container)
//   ensures true
//   modifies c
//{
//    var i: int := modifyContainerTransparant(c);
//}

procedure modifyContainerWildcard(c: Container) returns (i: int)
  opaque
  modifies *
{
  c#value := c#value + 1;
  7
};

procedure modifyContainerWithoutPermission1(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
{
    var i: int := modifyContainerWildcard(c)
};

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies d
{
    c#value := 2
};

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies d
{
    var i: bool := modifyContainerOpaque(c)
};

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  opaque
  modifies c
  modifies d
;

procedure multipleModifiesClausesCaller()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e);
  assert x == e#value // pass
};

procedure newObjectDoNotCountForModifies()
  opaque
{
  var c: Container := new Container;
  c#value := 1
};

procedure modifiesWildcardBodiless(c: Container, d: Container)
  opaque
  modifies *;

procedure modifiesWildcardBodilessCaller()
  opaque
  modifies *
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardBodiless(c, d);
  assert x == d#value // this should fail because modifies * means anything can change
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure modifiesWildcardWithBody(c: Container, d: Container)
  opaque
  modifies *
{
  c#value := 2;
  d#value := 3
};

procedure modifiesWildcardAndSpecific(c: Container, d: Container)
  opaque
  modifies c
  modifies *;

procedure modifiesWildcardAndSpecificCaller()
  opaque
  modifies *
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardAndSpecific(c, d);
  assert x == d#value // fails because modifies * subsumes modifies c
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ModifiesClauses" program 24 processLaurelFile
