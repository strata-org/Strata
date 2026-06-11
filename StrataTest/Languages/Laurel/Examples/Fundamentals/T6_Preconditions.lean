/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"
procedure hasRequires(x: int) returns (r: int)
  requires x > 2
// Call elimination reports precondition errors at the call site,
// not at the requires clause definition.
//
  opaque
{
  assert x > 0;
  assert x > 3;
//^^^^^^^^^^^^ error: assertion could not be proved
  x + 1
};

procedure caller()
  opaque
{
  var x: int := hasRequires(1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  var y: int := hasRequires(3)
};

procedure multipleRequires(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
  opaque
{
  x + y
};

procedure multipleRequiresCaller()
  opaque
{
  var a: int := multipleRequires(1, 2);
  var b: int := multipleRequires(-1, 2)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Preconditions" program 17 processLaurelFile
