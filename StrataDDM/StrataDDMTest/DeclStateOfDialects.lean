/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean

/-! ## Test: `DeclState.ofDialects` is order-independent

`DeclState.ofDialects` folds over `LoadedDialects.dialects.toList`, whose order
depends on `HashMap` internals. If a child dialect imports a parent, the parent
may be opened transitively before being visited directly. The fold must be
idempotent (use `ensureLoaded!`, not `openLoadedDialect!`).

We simulate the problematic iteration order by calling `ensureLoaded!` on the
child first (which transitively opens the parent), then on the parent directly.
With the old `openLoadedDialect!` code, the second call would panic because the
parent is already open.
-/

open StrataDDM StrataDDM.Elab

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

-- Retrieve the loaded dialects from the Lean environment and simulate the
-- problematic HashMap iteration order: child visited before parent.
-- This directly exercises the `ensureLoaded!` idempotency that `ofDialects` relies on.
/--
info: true
-/
#guard_msgs in
#eval show Lean.CoreM _ from do
  let loaded := (StrataDDM.dialectExt.getState (← Lean.getEnv)).loaded
  -- Start from a fresh DeclState
  let s : DeclState := { openDialects := #[], openDialectSet := {} }
  -- Open child first — this transitively opens the parent
  let s := s.ensureLoaded! loaded "OfDialectsChild"
  -- Open parent directly — with the old openLoadedDialect! this would panic
  let s := s.ensureLoaded! loaded "OfDialectsParent"
  return "OfDialectsParent" ∈ s.openDialectSet && "OfDialectsChild" ∈ s.openDialectSet

-- Also call DeclState.ofDialects directly on the loaded dialects.
-- This exercises the actual fixed function end-to-end.
/--
info: true
-/
#guard_msgs in
#eval show Lean.CoreM _ from do
  let loaded := (StrataDDM.dialectExt.getState (← Lean.getEnv)).loaded
  let s := DeclState.ofDialects loaded
  return "OfDialectsParent" ∈ s.openDialectSet && "OfDialectsChild" ∈ s.openDialectSet
