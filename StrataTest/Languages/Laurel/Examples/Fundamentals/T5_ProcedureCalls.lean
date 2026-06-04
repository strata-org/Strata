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
  x3
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

function aFunction(x: int): int
{
  x
};

procedure aFunctionCaller()
  opaque
{
  var x: int := aFunction(3);
  assert x == 3
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ProcedureCalls" program 14 processLaurelFile
