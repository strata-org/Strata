/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: added optional `entry` clause on procedure (producer-set entry point for interpretation).
-- (prior: added `free`/`checked` modifiers to requires/ensures clauses.)
-- (prior: modifiesClause refs parsed at prec 0 so `modifies o#f` (field target) parses.)
-- Rebuild trigger: refresh stale grammar cache for entry clause and condition-mode clause keywords.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
