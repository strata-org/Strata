/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Implicit.Command

/-!
# Core-implicit statements

Core-implicit statements reuse Imperative's `Stmt` type, parameterized
with `ImplicitCmd` instead of Core's `Command`. This gives us all the
structured control flow (blocks, if-then-else, loops, exits) for free.
-/

namespace Core.Implicit

public section

open Core
open Imperative

/-- A Core-implicit statement: `Imperative.Stmt` parameterized with
`ImplicitCmd` as the atomic command type. -/
abbrev Statement := Stmt Expression ImplicitCmd

/-- A list of Core-implicit statements. -/
abbrev Statements := List Statement

end

end Core.Implicit
