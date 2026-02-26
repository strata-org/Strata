/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# If-Then-Else Precedence Regression Test (Issue #491)

Demonstrates that `if c then 10 else 1 + x` should parse as
`if c then 10 else (1 + x)`, not `(if c then 10 else 1) + x`.
-/

namespace Strata.IfElsePrecedenceTest

def ifElsePlusPgm : Program :=
#strata
program Core;

function myFunc (b : bool, x : int) : int {
  if b then 10 else 1 + x
}

procedure Test() returns ()
spec {
  ensures true;
}
{
  assert [trueCase]: myFunc(true, 5) == 10;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram ifElsePlusPgm) |>.snd |>.isEmpty

/--
info:
Obligation: trueCase
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify ifElsePlusPgm (options := .quiet)

end Strata.IfElsePrecedenceTest
