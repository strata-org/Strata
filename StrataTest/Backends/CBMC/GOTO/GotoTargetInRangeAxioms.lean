/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.GotoTargetInRange

/-! # Axiom check for the `h_goto_target_in_range` discharge

Pure smoke test — ensures `goto_target_in_range_of_wf` elaborates
and tracks its axiom dependencies. -/

#print axioms CProverGOTO.GotoTargetInRange.goto_target_in_range_of_wf
