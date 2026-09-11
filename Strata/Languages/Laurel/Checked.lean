/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Checked.BuilderM
public import Strata.Languages.Laurel.Checked.Gen
public import Strata.Languages.Laurel.Checked.Macros

public meta import Strata.Languages.Laurel.CoreDefinitionsForLaurel

/-!
# Checked Laurel: the type-safe Laurel builder

A Lean layer for constructing well-typed Laurel expressions by construction.

Re-exports the primitive vocabulary (`Ty`, `Expr`, `Ref`) from `Checked.Builder` and runs
`derive_laurel_ops` over the core Laurel prelude (`coreDefinitionsForLaurel`) to emit a
checked combinator for every external procedure in the prelude.
-/

public section
namespace Strata.Laurel.Checked

/--
info: derive_laurel_ops: skipping overloaded procedure 'add'
---
info: derive_laurel_ops: skipping overloaded procedure 'div'
---
info: derive_laurel_ops: skipping overloaded procedure 'ge'
---
info: derive_laurel_ops: skipping overloaded procedure 'gt'
---
info: derive_laurel_ops: skipping overloaded procedure 'le'
---
info: derive_laurel_ops: skipping overloaded procedure 'lt'
---
info: derive_laurel_ops: skipping overloaded procedure 'mul'
---
info: derive_laurel_ops: skipping overloaded procedure 'neg'
---
info: derive_laurel_ops: skipping overloaded procedure 'sub'
-/
#guard_msgs in
derive_laurel_ops coreDefinitionsForLaurel

end Strata.Laurel.Checked
end -- public section
