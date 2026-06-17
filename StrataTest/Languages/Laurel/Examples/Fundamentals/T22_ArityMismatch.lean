/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Function called with too many arguments

`showLocations := true` prints each diagnostic's file-relative `file:line:col`
(computed from the snippet's base line — no manual offsets), while the inline
`// ^^^` annotation still asserts the error. The golden below thus *shows* the
localization without catching a spurious "unexpected diagnostic". -/

/--
info: T22_ArityMismatch.lean:32:2  7:2-23  error: ❌ Type checking error.
Impossible to unify int with (arrow int $__ty35).
-/
#guard_msgs in
#eval testLaurel (showLocations := true) <|
#strata
program Laurel;
function f(x: int): int { x };

procedure caller()
  opaque
{
  var y: int := f(1, 2)
//^^^^^^^^^^^^^^^^^^^^^ error: Impossible to unify int with (arrow int $__ty35).
};
#end

/-! ## Multi-return procedure assigned to single target -/

#eval testLaurel <|
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
