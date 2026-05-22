/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.NoDead

/-! # Axiom check for the `h_no_dead` discharge

Pure smoke test — ensures the no-DEAD theorems elaborate and tracks
their axiom dependencies. -/

#print axioms CProverGOTO.NoDead.no_dead_of_translator_no_contracts_explicit
#print axioms CProverGOTO.NoDead.no_dead_of_translator
#print axioms CProverGOTO.NoDead.no_dead_program_of_translator
