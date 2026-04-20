/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

def topLevelBlockSelection : Strata.Program :=
#strata
program Boole;

{
  assert [top_assert]: true;
};

procedure helper() returns (x: int)
spec {
  ensures [helper_ensures]: x == 1;
}
{
  x := 1;
};
#end

/--
info:
Obligation: top_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" topLevelBlockSelection
        (proceduresToVerify := (some [Strata.Boole.topLevelBlockProcedureName]))
        (options := .quiet)

example : Strata.smtVCsCorrect topLevelBlockSelection := by
  gen_smt_vcs
  all_goals (try grind)
