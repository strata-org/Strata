/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Laurel

/-
A decreases clause CAN be added to a procedure to prove that it terminates.
A procedure with a decreases clause may be called in an erased context.
-/

def program := r"
procedure noDecreases(x: int): boolean
procedure caller(x: int)
  requires noDecreases(x)
//                    ^ error: noDecreases can not be called from a pure context, because it is not proven to terminate

procedure noCyclicCalls()
  decreases []
{
  leaf();
}

procedure leaf() decreases [1] { }

procedure mutualRecursionA(x: nat)
  decreases [x, 1]
{
  mutualRecursionB(x);
}

procedure mutualRecursionB(x: nat)
  decreases [x, 0]
{
  if x != 0 { mutualRecursionA(x-1); }
}
"

-- Not working yet
-- #eval! testInput "Decreases" program processLaurelFile

/-
Translation towards SMT:

proof foo_body {
  var x: nat;
  assert decreases([x, 1], [x, 0]);
}

proof bar_body {
  var x: nat;
  if (x != 0) {
    assert decreases([x, 0], [x - 1, 1]);
  }
}
-/
