/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-
Regression test for strata-org/Strata#1390.

A structured `exit` bypasses `Env.merge`, so a procedure's path conditions used
to leak into later procedures; a contradictory leaked set then proved their
false obligations vacuously. `first` has an unsatisfiable precondition + a
structured `exit`; `second`'s `assert false` must fail, not silently pass.
-/

meta section
open StrataDDM (Program)

namespace Strata

def leakViaStructuredExit : Program :=
#strata
program Core;

procedure first(n : int)
spec {
  requires [c1]: (n >= 1);
  requires [c2]: (n <= 0);
}
{
  body: {
    if (n > 5) { exit body; }
  }
};

procedure second()
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
#eval Core.verify leakViaStructuredExit (options := .quiet)

end Strata

end
