/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-
Regression test for strata-org/Strata#1390.

`Program.eval` threads one `Env` through every procedure. A path that leaves a
labeled block via a structured `exit` does not get its path conditions popped
(the exiting path bypasses `Env.merge`), so a procedure's preconditions and
in-scope assumptions used to leak into the next procedure's verification
context. When the leaked set was contradictory, the next procedure proved false
obligations vacuously — a silent green pass.

`first` has an unsatisfiable precondition (`n >= 1` and `n <= 0`) and a
non-final structured `exit`. `second` has no spec; its `assert false` must be
reported as failing, not silently accepted. Before the fix this reported
`✅ pass`.
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
