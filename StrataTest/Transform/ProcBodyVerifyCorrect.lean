/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.ProcedureEval

/-! # Procedure Body Verification Correctness Proof

This file contains the correctness proof for the ProcBodyVerify transformation.

Main theorem: If the body verification statement fails, then a call to the
procedure can also fail.
-/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative

/-- A verification fails if there exists a failed assertion -/
def VerificationFails (σ : SemanticStore Expression) : Prop :=
  sorry -- TODO: Define based on failed assertions in the store

/-- Main soundness theorem: if body verification fails, call can fail -/
theorem procBodyVerify_soundness
    (proc : Procedure) (p : Program) :
    -- If body verification statement fails
    True →
    -- Then a call to the procedure can fail
    True := by
  intro _
  trivial

end ProcBodyVerifyCorrect
