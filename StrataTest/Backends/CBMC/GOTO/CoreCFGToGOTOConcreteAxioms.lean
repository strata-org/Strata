/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete

/-! # Axiom check for the concrete forward-simulation theorem family

Pure smoke test — tracks the axiom dependencies of the public
forward-simulation theorems (`_v6` and `_v7`). The internal
helpers `_v4`/`_v5` are `private` and not exposed here. -/

#print axioms
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6

#print axioms
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7
