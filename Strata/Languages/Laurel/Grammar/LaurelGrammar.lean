/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
-- Laurel dialect definition, loaded from LaurelGrammar.st.
-- The grammar includes compound-assignment ops (`+=`, `-=`, `*=`, `/=`, `%=`, `^=`),
-- an optional `entry` clause on procedures, `free`/`checked` modifiers on
-- requires/ensures clauses, and an optional type annotation on assignTargetDecl
-- (at explicit @[prec(0)], like varDecl, so it prints without parentheses).
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. the token below) to trigger a recompile after modifying LaurelGrammar.st.
-- Rebuild trigger token: assignTargetDecl-prec0
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
