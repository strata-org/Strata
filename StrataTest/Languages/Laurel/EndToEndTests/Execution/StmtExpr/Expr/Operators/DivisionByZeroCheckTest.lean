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

#eval testLaurelMultiple
#strata
program Laurel;
procedure safeDivision()
  entry
  opaque
{
  var x: int := 10;
  var y: int := 2;
  var z: int := x / y;
  assert z == 5
};

procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure callPureDivSafe()
  entry
  opaque
{
  var z: int := pureDiv(10, 2);
  assert z == 5
};
#end

/-! ### Unsafe division: divisor not constrained, fails verification -/

-- Error ranges are too wide because Core does not use expression locations.
-- We can't make this a testLaurelMultiple,
-- because unsafe division is checked through Core's safe division operator
-- and Core interpretation does not detect unsafe division
#eval testLaurel <|
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

#eval testLaurelMultiple <|
#strata
program Laurel;
procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure callPureDivUnsafe(x: int)
  opaque
{
  var z: int := pureDiv(10, x)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};

procedure root() entry opaque callPureDivUnsafe(0);
#end
