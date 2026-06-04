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

def program: String := r"
procedure hasMutatingAssignment(): int
  opaque
{
  var x: int := 0;
  x := x + 1;
  x
};

function functionWithMutatingAssignment(x: int): int
{
  x := x + 1
//^^^^^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
};

function functionWithWhile(x: int): int
{
  while(false) {}
//^^^^^^^^^^^^^^^ error: loops are not supported in functions or contracts
};
function functionCallingHasMutationAssignment(x: int): int
{
  hasMutatingAssignment()
};

procedure impureContractIsLegal1(x: int)
  requires x == hasMutatingAssignment()
  opaque
{
  assert hasMutatingAssignment() == 1
};

procedure impureContractIsNotLegal2(x: int)
  requires (x := 2) == 2
//          ^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  opaque
{
  assert (x := 2) == 2
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
