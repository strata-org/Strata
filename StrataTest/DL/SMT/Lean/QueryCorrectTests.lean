/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.SMT.Lean.QueryCorrect

/-! The soundness theorem of query preparation rests on the standard axioms only: no `sorry`,
and no native evaluation. -/

/--
info: '_private.Strata.DL.SMT.Lean.QueryCorrect.0.Strata.SMT.LeanExport.prepareTerms_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Strata.SMT.LeanExport.prepareTerms_sound
