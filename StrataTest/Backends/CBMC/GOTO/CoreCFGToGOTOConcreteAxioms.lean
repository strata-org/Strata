/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete

/-! # Axiom check for the concrete forward-simulation theorem family

Pure smoke test — ensures all `_vN` versions elaborate and tracks
their axiom dependencies. -/

#print axioms
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v4

#print axioms
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v5

#print axioms
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6
