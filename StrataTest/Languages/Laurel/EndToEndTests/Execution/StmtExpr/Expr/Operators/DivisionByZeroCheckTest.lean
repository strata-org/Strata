/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## End-to-end test: safe division (no errors) and unsafe division (error)

Division and modulo in Laurel are calls to the built-in wrappers `$div` / `$mod`,
which declare `requires y != 0` and delegate to Core's safe operators. The
PrecondElim transform automatically generates verification conditions for these
preconditions, so an unconstrained divisor surfaces as a failed precondition.
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
-- `/` is a call to the `$div` wrapper, which declares `requires y != 0`, so the
-- unconstrained divisor surfaces as that precondition rather than an assertion.
-- Verify-only: `x` is an unconstrained parameter and nothing marks an `entry`,
-- so there is no concrete path for the interpreter to walk. The failure is
-- inherently symbolic — it says the precondition cannot be proved for *all* `x`.
#eval testLaurel <|
#strata
program Laurel;
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end

/-! ### Unsafe call to function with `requires y != 0` -/

-- Verify-only: the two phases disagree about how many diagnostics this program
-- produces, and `testLaurelMultiple` holds both to the same annotations.
--
-- `root` calls `callPureDivUnsafe(0)`, so concrete execution reaches `x / y`
-- with `y = 0`. `/` is a call to the `$div` wrapper, which declares
-- `requires y != 0`, and that precondition fails at runtime — the interpreter
-- reports a second diagnostic, inside `pureDiv`'s body, that the verifier does
-- not: to the verifier `pureDiv` is correct, since its own `requires y != 0`
-- discharges `$div`'s. Only the unsatisfied precondition at the *call site* is
-- common to both. Per `TestLaurel`'s rule, a block whose negatives are
-- phase-asymmetric belongs in `testLaurel`.
#eval testLaurel <|
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
