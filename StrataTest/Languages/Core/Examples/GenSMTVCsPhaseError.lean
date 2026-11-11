/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)

---------------------------------------------------------------------

/-!
## `gen_smt_vcs` reports why VC generation failed

When a step of VC generation fails, `genCoreVCsWithError` and `gen_smt_vcs`
name the step and give its message. Here the type-checking phase rejects an
assignment of a `bool` to an `int` variable.
-/

namespace Strata

private def illTypedPgm : Program :=
#strata
program Core;

procedure bad(out r : int)
{
  r := true;
};
#end

-- `(651-661)` below is the byte range of `r := true` in this file, so an edit
-- above that line changes it.

/-- info: "phase 'typeCheck' failed: (651-661) ❌ Type checking error.\nImpossible to unify int with bool." -/
#guard_msgs in
#eval match genCoreVCsWithError illTypedPgm with
  | .ok _ => "unexpected success"
  | .error msg => msg

/--
error: gen_smt_vcs: failed to generate VCs: phase 'typeCheck' failed: (651-661) ❌ Type checking error.
Impossible to unify int with bool.
-/
#guard_msgs in
example : smtVCsCorrect illTypedPgm := by
  gen_smt_vcs

/-! A program whose main dialect is not Core is rejected before translation.
`gen_smt_vcs` gives no reason for such a program, since an extension may
override `genCoreVCs` for its dialect. -/

/-- info: "dialect 'NotCore' is not supported" -/
#guard_msgs in
#eval match genCoreVCsWithError { illTypedPgm with dialect := "NotCore" } with
  | .ok _ => "unexpected success"
  | .error msg => msg

/-- error: gen_smt_vcs: failed to generate VCs -/
#guard_msgs in
example : smtVCsCorrect { illTypedPgm with dialect := "NotCore" } := by
  gen_smt_vcs

end Strata
