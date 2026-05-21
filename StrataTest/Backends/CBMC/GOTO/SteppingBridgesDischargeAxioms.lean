/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge

/-! # Axiom check for the SteppingBridges discharge

Pure smoke test — ensures `steppingBridges_of_translator` elaborates
and tracks its axiom dependencies. -/

#print axioms CProverGOTO.SteppingBridgesDischarge.steppingBridges_of_translator
