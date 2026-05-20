/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

/-! ## Tests for cross-procedure error isolation in `Program.eval`

When one procedure's partial evaluation errors (e.g., function-name
collision), the error must NOT contaminate subsequent procedures'
evaluation. Each procedure's evaluation should start from a clean
`Env.error` state. -/

---------------------------------------------------------------------
namespace Strata


/-- proc_a registers `foo`; proc_b's redefinition of `foo` raises a
    partial-evaluation error; proc_c's `assert false` MUST still be
    evaluated and reported as failing. -/
private def collisionThenAssertFalse :=
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
#eval verify collisionThenAssertFalse (options := .quiet)


/-- Reordered variant: proc_c runs before the colliding pair. Guards against
    a regression where ordering becomes load-bearing again. -/
private def assertFalseThenCollision :=
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
#eval verify assertFalseThenCollision (options := .quiet)


end Strata
