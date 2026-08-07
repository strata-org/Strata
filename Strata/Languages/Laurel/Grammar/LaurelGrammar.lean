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
-- It also includes the exceptional channel: `throw`, `try`/`catch`/`finally`, a
-- `throws (e: T)` signature clause that always binds the thrown value (there is
-- no unbound form), and repeatable `throwsOn <guard> { ensures … modifies … }`
-- behavior-case blocks inside `opaqueSpec`, beside `ensures`/`modifies`.
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. the token below) to trigger a recompile after modifying LaurelGrammar.st.
-- Rebuild trigger token: exceptions-throwsOn-blocks
-- Rebuild trigger: file-scope global declarations.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
