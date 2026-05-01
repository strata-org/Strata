/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Grammar updated: renamed Optional* categories (op names updated)
module

-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: merged modifiesWildcard, opaque keyword, and multiAssign field access targets.
public import Strata.DDM.Integration.Lean
public meta import Strata.DDM.Integration.Lean

namespace Strata.Laurel

public section

#load_dialect "./LaurelGrammar.st"

end
