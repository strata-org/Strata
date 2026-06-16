/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel
#strata
program Laurel;
procedure fooReassign(): int
  opaque // required because we don't yet support destructive assignment in transparent bodies
{
  var x: int := 0;
  x := x + 1;
  assert x == 1;
  x := x + 1;
  x
};

procedure fooSingleAssign(): int
{
  var x: int := 0;
  var x2: int := x + 1;
  var x3: int := x2 + 1;
  return x3
};

procedure fooProof()
  opaque
{
  var x: int := fooReassign();
  var y: int := fooSingleAssign()
// The following assertions fails while it should succeed,
// because we don't yet support making fooReassign transparent
//  assert x == y;
};

#end
