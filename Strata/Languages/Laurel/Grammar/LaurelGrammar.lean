/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Grammar updated: renamed Optional* categories (op names updated)
module

-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: added opaque keyword between invokeOn and ensures in procedure/function ops.
public import Strata.DDM.AST
import Strata.DDM.BuiltinDialects.Init
import Strata.DDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "./LaurelGrammar.st"

end
