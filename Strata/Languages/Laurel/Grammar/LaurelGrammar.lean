/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

-- The Laurel dialect definition, loaded from `LaurelGrammar.st` (which is where the
-- grammar itself — every `op`/`category` and its own comments — lives).
--
-- BUILD GOTCHA: the build system does NOT track `LaurelGrammar.st` as an input of this
-- file, so editing only the `.st` will not trigger a recompile. Touch this file (e.g.
-- bump this comment) after modifying the grammar.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
