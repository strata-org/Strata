/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## End-to-end test: safe division (no errors) and unsafe division (error)

Division and modulo in Laurel translate to Core's safe operators, which have
built-in preconditions (divisor ≠ 0). The PrecondElim transform automatically
generates verification conditions for these preconditions.
-/

/-! ### Safe paths verify cleanly -/

/-- info: ok -/
#guard_msgs in
#eval testLaurel
#strata
program Laurel;
procedure safeDivision()
  opaque
{
  var x: int := 10;
  var y: int := 2;
  var z: int := x / y;
  assert z == 5
};

function pureDiv(x: int, y: int): int
  requires y != 0
{
  x / y
};

procedure callPureDivSafe()
  opaque
{
  var z: int := pureDiv(10, 2);
  assert z == 5
};
#end

/-! ### Unsafe division: divisor not constrained, fails verification -/

-- Error ranges are too wide because Core does not use expression locations.
#eval testLaurelExpect <|
#strata
program Laurel;
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Unsafe call to function with `requires y != 0` -/

#eval testLaurelExpect <|
#strata
program Laurel;
function pureDiv(x: int, y: int): int
  requires y != 0
{
  x / y
};

procedure callPureDivUnsafe(x: int)
  opaque
{
  var z: int := pureDiv(10, x)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
