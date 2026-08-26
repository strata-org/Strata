/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A call inside a `requires` or `ensures` is held to the callee's precondition. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure needsBig(x: int) returns (s: int)
  requires x > 100
  opaque;

procedure violatedInEnsures() returns (r: int)
  opaque
  ensures r == needsBig(0)
//        ^^^^^^^^^^^^^^^^ error: postcondition does not hold
//             ^^^^^^^^^^^ error: precondition does not hold
{
  r := 0
};

procedure violatedInRequires() returns (r: int)
  requires needsBig(0) > 0
//         ^^^^^^^^^^^ error: precondition does not hold
  opaque
{
  r := 0
};

procedure satisfiedInRequires() returns (r: int)
  requires needsBig(101) > 0
  opaque
{
  r := 0
};

procedure nestedInEnsures() returns (r: int)
  opaque
  ensures r == needsBig(needsBig(200))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
//             ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
{
  r := 0
};

procedure precedingRequiresDischarges(x: int) returns (r: int)
  requires x != 0
  requires 10 / x > 1
  opaque
{
  r := 0
};

procedure unguardedDivisionInRequires(x: int) returns (r: int)
  requires 10 / x > 1
//         ^^^^^^ error: divisor is non-zero does not hold
  opaque
{
  r := 0
};

procedure guardBeforeDivisionInRequires(x: int) returns (r: int)
  requires (x == 0 || 10 / x > 1)
  opaque
{
  r := 0
};

procedure divisionBeforeGuardInRequires(x: int) returns (r: int)
  requires (10 / x > 1 || x == 0)
//          ^^^^^^ error: divisor is non-zero does not hold
  opaque
{
  r := 0
};

procedure conjunctionGuardInRequires(x: int) returns (r: int)
  requires x != 0 && 10 / x > 1
  opaque
{
  r := 0
};

procedure ensuresDischargedByRequires(x: int) returns (r: int)
  requires x > 100
  opaque
  ensures needsBig(x) > 0
//        ^^^^^^^^^^^^^^^ error: postcondition does not hold
{
  r := 0
};

procedure ensuresNotDischarged(x: int) returns (r: int)
  opaque
  ensures needsBig(x) > 0
//        ^^^^^^^^^^^^^^^ error: postcondition does not hold
//        ^^^^^^^^^^^ error: precondition does not hold
{
  r := 0
};

procedure violatedInBody() returns (r: int)
  opaque
{
  var s: int := needsBig(0);
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  r := 0
};

procedure freeRequiresIsChecked(x: int) returns (r: int)
  free requires 10 / x > 1
//              ^^^^^^ error: divisor is non-zero does not hold
  opaque
{
  r := 0
};

procedure checkedRequiresIsChecked(x: int) returns (r: int)
  checked requires 10 / x > 1
//                 ^^^^^^ error: divisor is non-zero does not hold
  opaque
{
  r := 0
};

procedure precedingFreeRequiresDischarges(x: int) returns (r: int)
  free requires x != 0
  requires 10 / x > 1
  opaque
{
  r := 0
};

procedure precedingCheckedRequiresDischarges(x: int) returns (r: int)
  checked requires x != 0
  requires 10 / x > 1
  opaque
{
  r := 0
};

procedure precedingRequiresDischargesFree(x: int) returns (r: int)
  requires x != 0
  free requires 10 / x > 1
  opaque
{
  r := 0
};

procedure freeEnsuresIsChecked() returns (r: int)
  opaque
  free ensures r == needsBig(0)
//                  ^^^^^^^^^^^ error: precondition does not hold
{
  r := 0
};

procedure checkedEnsuresIsChecked() returns (r: int)
  opaque
  checked ensures r == needsBig(0)
//                ^^^^^^^^^^^^^^^^ error: postcondition does not hold
//                     ^^^^^^^^^^^ error: precondition does not hold
{
  r := 0
};
#end
