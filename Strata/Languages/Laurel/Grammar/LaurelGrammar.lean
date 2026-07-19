/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Last grammar change (polymorphism): `<T>` type-param binders on
-- procedure/function/composite/datatype/type-alias; `appliedType` (`Box<int>`); `new C<τ>`;
-- `is`/`as` operands widened to LaurelType; `extends` parents to LaurelType (generic parents);
-- the `type Name = Target` alias command; and a `FieldPath` category for chained-field writes.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end
