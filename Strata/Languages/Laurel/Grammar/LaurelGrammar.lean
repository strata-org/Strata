/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: modifiesClause refs parsed at prec 0 so `modifies o#f` (field target) parses.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
