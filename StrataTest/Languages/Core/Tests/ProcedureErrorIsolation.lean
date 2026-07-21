/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-
Regression test for the `Env.error` procedure-boundary reset (sibling to
`ProcedurePathConditionIsolation`).

`Program.eval` threads one `Env` through procedures in source order. A
within-procedure error (here, `second`'s duplicate `foo` declaration) must not
contaminate later procedures: without the boundary reset it short-circuits every
subsequent command, so `third`'s `assert false` emits no obligation and passes
vacuously. The reset makes `third`'s obligation fail, as it would in isolation.
-/

meta section
open StrataDDM (Program)

namespace Strata

def errorLeakAcrossProcedures : Program :=
#strata
program Core;

procedure first()
{
  function foo(y : int) : int { y + 1 }
};

procedure second()
{
  function foo(y : int) : int { y + 2 }
};

procedure third()
{
  assert [bad]: false;
};
#end

/--
info:
Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify errorLeakAcrossProcedures (options := .quiet)

end Strata

end
