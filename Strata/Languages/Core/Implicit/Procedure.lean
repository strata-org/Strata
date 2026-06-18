/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Implicit.Statement
public import Strata.Languages.Core.Implicit.HeapEffect
public import Strata.Languages.Core.Procedure

/-!
# Core-implicit procedures

A Core-implicit procedure reuses Core's `Procedure.Header` and
`Procedure.Spec` but adds a `HeapEffect` annotation and carries a body
of `Core.Implicit.Statement`s (which may include `HeapCmd` commands).

The `HeapEffect` replaces the role of the explicit heap parameter mode:
- `inout heap` in Core-explicit → `HeapEffect.writes`
- input `heap` in Core-explicit → `HeapEffect.reads`
- no heap parameter → `HeapEffect.none`

## Future refactoring

TODO: Parameterize Core's `Procedure` structure over its statement type
so that Core-explicit and Core-implicit can share a single definition.
This would eliminate the thin wrapper here and unify helper functions
(`getVars`, `eraseTypes`, etc.) via type class constraints. Deferred to
avoid a large refactor of downstream consumers today.
-/

namespace Core.Implicit

public section

open Core

/-- A Core-implicit procedure. Reuses Core's `Procedure.Header` and
`Procedure.Spec`; adds `HeapEffect` and uses `Core.Implicit.Statements`
for the body. -/
structure Procedure where
  /-- The standard Core procedure header (name, typeArgs, inputs, outputs).
      Note: the heap parameter is NOT present in inputs/outputs — that is
      the whole point of the implicit representation. -/
  header : Core.Procedure.Header
  /-- The heap effect of this procedure. -/
  effect : HeapEffect
  /-- The procedure's contract (preconditions and postconditions).
      Specs may use implicit field syntax (`obj.field`, `old(obj.field)`). -/
  spec : Core.Procedure.Spec
  /-- The procedure body. Empty for abstract (bodyless) procedures. -/
  body : Statements
  deriving Inhabited

end

end Core.Implicit
