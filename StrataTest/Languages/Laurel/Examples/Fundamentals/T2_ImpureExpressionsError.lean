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
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
}

function impureFunction1(x: int): int
{
  x := x + 1;
//^^^^^^^^^^^ error: destructive assignments are not supported in functions or contracts
}

function impureFunction2(x: int): int
{
  while(false) {}
//^^^^^^^^^^^^^^^ error: loops are not supported in functions or contracts
}
function impureFunction3(x: int): int
{
  impure()
//^^^^^^^^ error: calls to procedures are not supported in functions or contracts
}

procedure impureContractIsNotLegal1(x: int)
  requires x == impure()
//              ^^^^^^^^ error: calls to procedures are not supported in functions or contracts
{
  assert impure() == 1;
//       ^^^^^^^^ error: calls to procedures are not supported in functions or contracts
}

procedure impureContractIsNotLegal2(x: int)
  requires (x := 2;) == 2
//          ^^^^^^^ error: destructive assignments are not supported in functions or contracts
{
  assert (x := 2;) == 2;
//        ^^^^^^^ error: destructive assignments are not supported in functions or contracts
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
