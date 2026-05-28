/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Function called with too many arguments -/

/--
error: <#strata>(442-463) ❌ Type checking error.
Impossible to unify int with (arrow int $__ty35).
-/
#guard_msgs in
#eval testLaurelExpect <|
#strata
program Laurel;
function f(x: int): int { x };

procedure caller()
  opaque
{
  var y: int := f(1, 2)
};
#end

/-! ## Multi-return procedure assigned to single target -/

#eval testLaurelExpect <|
#strata
program Laurel;
procedure twoReturns() returns (a: int, b: int)
  opaque
  ensures a == 1 && b == 2;

procedure mismatch()
  opaque
{
  var x: int;
  assign x := twoReturns()
//^^^^^^^^^^^^^^^^^^^^^^^^ error: Assignment target count mismatch: 1 targets but right-hand side produces 2 values
};
#end
