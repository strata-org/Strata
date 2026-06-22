/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
-- Then: `is`/`as` operands widened from Ident to LaurelType (generic `x is Box<int>`);
-- added a `type Name = Target` alias command (TypeAliasDecl).
-- Laurel dialect definition, loaded from LaurelGrammar.st
-- NOTE: Changes to LaurelGrammar.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying LaurelGrammar.st.
-- Grammar change: fieldAccess prec raised 90 -> 95 (paren-free `c#n++`); shares prec(95) with `call`.
-- Then (polymorphism): renamed strConcat token to `^`; added preIncr/preDecr/postIncr/postDecr; `return` value is now Option StmtExpr (supports a valueless return).
-- Then: procedure/function/composite gained an Option TypeParams binder (`<T, U>`)
-- for user-level polymorphism.
-- Then: added `appliedType` (`Box<int>`) generic type application in type position,
-- for generic composite instantiation.
-- Then: `extends` parents are now `CommaSepBy LaurelType` (was `CommaSepBy Ident`), so a
-- generic composite can extend a generic parent: `extends Base<T>`.
-- Then: added optional `<...>` type arguments to `new` (`new Box<int>`) so generic
-- composite allocations carry their instantiation explicitly (uniform across all
-- positions; bare `new C` still parses with empty type args).
-- Then: `datatype` gained an Option TypeParams binder (`datatype Box<T> { … }`) for
-- generic datatypes — native Core parametric datatypes, no monomorphization.
-- Then: moved the `TypeParams` category declaration above `datatype` so it is in
-- scope there (categories must be declared before use).
-- Then: annotated the `typeAnnotation` varType and `new` typeArgs references with `:0`
-- so the formatter does not parenthesize the `prec(80)` `appliedType`/`newTypeArgs` ops
-- (`(Box<int>)`, `new Box(<int>)`); the prec is needed for parse disambiguation only.
public import StrataDDM.AST
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

namespace Strata.Laurel

public section

#load_dialect "Strata/Languages/Laurel/Grammar/LaurelGrammar.st"

end

-- Then: assignTargetField obj is a dedicated FieldPath category.

-- Then: stripped plan-jargon from grammar comments.
