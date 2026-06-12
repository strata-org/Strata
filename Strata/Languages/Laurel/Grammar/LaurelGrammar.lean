/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Grammar updated: renamed Optional* categories (op names updated)
module

-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: block format uses indent(2) with leading spaces for vertical layout.
--
-- This grammar drives editor syntax highlighting (.laurel.st). After changing
-- keywords, operators, or types here, regenerate the editor files (VSCode,
-- Emacs, Vim/Neovim, tree-sitter) by running:
--   lake env lean --run editors/GenSyntax.lean all
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
