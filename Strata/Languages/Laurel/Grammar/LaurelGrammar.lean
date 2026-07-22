/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
-- Laurel dialect definition, loaded from LaurelGrammar.st.
-- The grammar supports:
--   * Polymorphism: `<T>` type-param binders on
--     procedure/composite/datatype/type-alias; `appliedType` (`Box<int>`, datatype
--     type parameters); `parenType` so parenthesized/applied types round-trip;
--     `new C<τ>`; `is`/`as` operands widened to LaurelType; `extends` parents as
--     LaurelType (generic parents); the `type Name = Target` alias command; and a
--     `FieldPath` category for chained-field writes.
--   * The exceptional channel: `throw`, `try`/`catch`/`finally`, a `throws (e: T)`
--     signature clause that always binds the thrown value (there is no unbound
--     form), and repeatable `throwsOn <guard> { ensures … modifies … }` behavior-case
--     blocks inside `opaqueSpec`, beside `ensures`/`modifies`. A pass-generated
--     `modifiesWhenClause` (`modifies <refs> when <guard>`) renders the guarded
--     frames `EliminateExceptions` leaves behind; users never write it.
--   * Compound-assignment ops (`+=`, `-=`, `*=`, `/=`, `%=`, `^=`); an optional
--     `entry` clause on `procedure` (producer-set interpretation entry point);
--     `free`/`checked` modifiers on requires/ensures clauses; an optional type
--     annotation on `assignTargetDecl` (at explicit @[prec(0)], like `varDecl`, so
--     it prints without parentheses); and file-scope global declarations.
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. the token below) to trigger a recompile after modifying LaurelGrammar.st.
-- Rebuild trigger token: guarded-modifies-groups
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
