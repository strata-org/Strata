/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

-- The Laurel dialect, loaded from `LaurelGrammar.st` (the grammar itself — every
-- `op`/`category` and its own comments — lives there).
-- NOTE: the build system does NOT track `LaurelGrammar.st` as an input of this file,
-- so edit this file to force a recompile after changing the grammar.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
