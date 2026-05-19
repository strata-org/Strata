/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

/-! ## Tests for cross-procedure error isolation in `Program.eval`

Regression tests for issue #1185 — when one procedure's partial evaluation
errors (e.g., function-name collision), the error must NOT contaminate
subsequent procedures' evaluation. Each procedure's evaluation should start
from a clean `Env.error` state. -/

---------------------------------------------------------------------
namespace Strata


/-- Issue #1185 exact repro. proc_a registers `foo`; proc_b's redefinition of
    `foo` raises a partial-evaluation error; proc_c's `assert false` MUST still
    be evaluated and reported as failing. Pre-fix: "All 0 goals passed" (the
    soundness bug). Post-fix: assert_0 reports ❌ fail. -/
private def issue1185Repro :=
#strata
program Core;

procedure proc_a()
{
  function foo(y : int) : int { y + 1 }
};

procedure proc_b()
{
  function foo(y : int) : int { y + 2 }
};

procedure proc_c()
{
  assert false;
};
#end


/--
info:
Obligation: assert_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify issue1185Repro (options := .quiet)


/-- Reorder regression: proc_c first, then the colliding pair. This already
    worked pre-fix (the issue's "Reordering Rescues the Obligation" section).
    Protect against regression. -/
private def issue1185Reordered :=
#strata
program Core;

procedure proc_c()
{
  assert false;
};

procedure proc_a()
{
  function foo(y : int) : int { y + 1 }
};

procedure proc_b()
{
  function foo(y : int) : int { y + 2 }
};
#end


/--
info:
Obligation: assert_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify issue1185Reordered (options := .quiet)


end Strata
