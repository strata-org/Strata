/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-! ## Test: `DeclState.ofDialects` is order-independent

`DeclState.ofDialects` folds over `LoadedDialects.dialects.toList`, whose order
depends on `HashMap` internals. If a child dialect imports a parent, the parent
may be opened transitively before being visited directly. The fold must be
idempotent (use `ensureLoaded!`, not `openLoadedDialect!`).

We declare two dialects where one imports the other, then parse a program using
the child. This exercises `DeclState.ofDialects` on a `LoadedDialects` containing
both dialects with an import relationship.
-/

open Strata

-- Declare a parent dialect
#guard_msgs in
#dialect
dialect OfDialectsParent;
type ParentType;
#end

-- Declare a child dialect that imports the parent
#guard_msgs in
#dialect
dialect OfDialectsChild;
import OfDialectsParent;
type ChildType;
#end

-- Parse a program using the child dialect.
-- The `LoadedDialects` passed to `DeclState.ofDialects` contains Init,
-- OfDialectsParent, and OfDialectsChild (where child imports parent).
-- `ensureLoaded!` guarantees idempotency: if HashMap iteration yields the child
-- before the parent, the parent is opened transitively first, and the subsequent
-- direct visit is a no-op.
def testProgram := #strata
program OfDialectsChild;
#end

/--
info: "program OfDialectsChild;\n"
-/
#guard_msgs in
#eval toString testProgram
