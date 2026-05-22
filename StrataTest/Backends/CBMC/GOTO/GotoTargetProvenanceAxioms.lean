/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.GotoTargetProvenance

/-! # Axiom check for R8a's `everyGotoTargetIsLabelMapEntry_of_translator`

Pure smoke test — ensures the top-level theorems elaborate and tracks
their axiom dependencies. -/

#print axioms
  CProverGOTO.GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator_translatorMap

#print axioms
  CProverGOTO.GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator
