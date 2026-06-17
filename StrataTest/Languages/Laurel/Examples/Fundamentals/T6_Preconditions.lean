/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;
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

#end
