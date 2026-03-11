/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: assert/assume/return now use prec(0) to bind weakly
import Strata.DDM.Integration.Lean

namespace Strata.Laurel


#load_dialect "./LaurelGrammar.st"
