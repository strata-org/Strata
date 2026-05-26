/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

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
//^^^^^^^^^^ error: destructive assignments are not supported in functions or contracts
};

function functionWithWhile(x: int): int
{
  while(false) {}
//^^^^^^^^^^^^^^^ error: loops are not supported in functions or contracts
};
function functionCallingHasMutationAssignment(x: int): int
{
  hasMutatingAssignment()
//^^^^^^^^^^^^^^^^^^^^^^^ error: calls to procedures are not supported in functions or contracts
};

procedure impureContractIsNotLegal1(x: int)
  requires x == hasMutatingAssignment()
//              ^^^^^^^^^^^^^^^^^^^^^^^ error: calls to procedures are not supported in functions or contracts
  opaque
{
  assert hasMutatingAssignment() == 1
};

procedure impureContractIsNotLegal2(x: int)
  requires (x := 2) == 2
//          ^^^^^^ error: destructive assignments are not supported in functions or contracts
  opaque
{
  assert (x := 2) == 2
//        ^^^^^^ error: destructive assignments are not supported in functions or contracts
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
