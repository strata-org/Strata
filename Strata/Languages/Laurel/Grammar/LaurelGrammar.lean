/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Grammar updated: renamed Optional* categories (op names updated)
-- Grammar updated: `call` callee at prec 89 to accept fieldAccess (prec 90) chains
-- Grammar updated: `fieldAccess` is leftassoc so `a#b#c` parses as `(a#b)#c`
-- Grammar updated: added bitvector literal support (bvLiteral)

module
-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change: renamed strConcat token to `^`; added preIncr/preDecr/postIncr/postDecr; `return` value is now Option StmtExpr (supports a valueless return).
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
