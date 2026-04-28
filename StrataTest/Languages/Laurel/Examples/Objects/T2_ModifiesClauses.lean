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

procedure modifyContainerTransparant(c: Container) returns (i: int)
{
  c#value := c#value + 1;
  7
};

procedure caller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := modifyContainerOpaque(c);
  assert x == d#value // pass
};

// This test-case does not work yet.
// Because Core procedures never have transparent bodies
//procedure modifyContainerWithPermission1(c: Container, d: Container)
//   ensures true
//   modifies c
//{
//    var i: int := modifyContainerTransparant(c);
//}

procedure modifyContainerWithoutPermission1(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// the above error is because the body does not satisfy the empty modifies clause. error needs to be improved
   opaque
{
    var i: int := modifyContainerTransparant(c)
};

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
  opaque
  modifies d
{
    c#value := 2
};

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
  opaque
  modifies d
{
    var i: int := modifyContainerTransparant(c)
};

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  opaque
  modifies c
  modifies d
;

procedure multipleModifiesClausesCaller() {
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
<<<<<<< HEAD
  modifies *;
=======
  modifies *
;
>>>>>>> 9be587dccaf3a8f74236ad6bb5bbbd0044ce1780

procedure modifiesWildcardBodilessCaller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardBodiless(c, d);
  assert x == d#value // this should fail because modifies * means anything can change
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure modifiesWildcardWithBody(c: Container, d: Container)
  opaque
<<<<<<< HEAD
=======
  ensures true
>>>>>>> 9be587dccaf3a8f74236ad6bb5bbbd0044ce1780
  modifies *
{
  c#value := 2;
  d#value := 3
};

procedure modifiesWildcardAndSpecific(c: Container, d: Container)
  opaque
  modifies c
  modifies *;

procedure modifiesWildcardAndSpecificCaller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardAndSpecific(c, d);
  assert x == d#value // fails because modifies * subsumes modifies c
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Without `ensures`, the body is transparent and `modifies *` is silently dropped.
// The caller sees through the body, so heap changes are tracked directly. See #969.
procedure modifiesWildcardTransparent(c: Container, d: Container)
  opaque
  modifies *
{
  c#value := 2;
  d#value := 3
};

procedure modifiesWildcardTransparentCaller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardTransparent(c, d);
  assert x == d#value // fails because the transparent body's heap writes are visible
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ModifiesClauses" program 24 processLaurelFile
