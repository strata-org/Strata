/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreLang
public import Strata.Transform.WP.WPOutOps

/-! # The operators of the guarded program of a Core statement list

The laws on operators of the expressions the WP phase builds hold for Core expressions
(`core_opsLaws`): a Core conditional references the operators of its parts, Boolean literals and
variables reference none, and `substFn` (`LExpr.substFvarsBy`) references the operators of the
expression and of the substituted values (`LExpr.getOps_substFvarsBy_mem`).  Hence every
operator the guarded program of a Core statement list references is an operator of the list
(`wpEntry_ops_core`).

Key theorems: `core_opsLaws`, `wpEntry_ops_core`. -/

open Imperative Imperative.WP Lambda

namespace Core
namespace WP

public section

/-- The laws on operators of the expressions the WP phase builds hold for Core expressions. -/
theorem core_opsLaws : OpsLaws Expression where
  ite c t e o h := by
    simpa [HasOps.getOps, WPOps.ite, LExpr.getOps, or_assoc] using h
  tt := rfl
  ff := rfl
  var x ty := by cases ty <;> rfl
  substFn := LExpr.getOps_substFvarsBy_mem

/-- **The WP phase references no new operator** on Core: every operator of the guarded program of
    the Core statement list `ss` (its commands and its `ite` conditions) is an operator of `ss`. -/
theorem wpEntry_ops_core {G : IdSet Expression} {tys : Tys Expression} {ss : Statements}
    {w : WOut Expression} (h : wpEntry G tys ss = .ok w) :
    ∀ o ∈ Block.getOps w.lay, o ∈ Block.getOps ss :=
  wpEntry_ops core_opsLaws h

end -- public section

end WP
end Core
