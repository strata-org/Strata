/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.ToExpr

structure CachedValue {α} (v : α) where
  val : α := v
  isEqual : val = v := by trivial

namespace CachedValue

protected def default {α : Sort u} (v : α) : CachedValue v := {}

instance {α} (v : α) : Inhabited (CachedValue v) where
  default := .default v

instance  {α : Type _} (v : α) : Repr (CachedValue v) where
  reprPrec _ _ := .text "{}"

instance {α} (v : α) : CoeOut (CachedValue v) α where
  coe s := s.val

open Lean

instance {α : Type} [h : Lean.ToExpr α] (v : α) : Lean.ToExpr (CachedValue v) where
  toTypeExpr := mkApp2 (mkConst ``CachedValue [levelOne]) h.toTypeExpr (toExpr v)
  toExpr _ := mkApp2 (mkConst ``CachedValue.default [levelOne]) h.toTypeExpr (toExpr v)

instance {α : Type} [h : Quote α] (v : α) : Quote (CachedValue v) where
  quote _ := Syntax.mkCApp ``CachedValue.default #[quote v]

end CachedValue
