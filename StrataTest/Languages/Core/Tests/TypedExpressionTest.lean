/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.Passive.CoreTyped

/-! # Typed Core expressions

`Core.Expression.Typed` holds of `int.add(x, 1)` with `x` annotated `int`, at `int`; it does not
hold of a variable without annotation, whose value an SMT model does not constrain, nor at a
type other than the expression's. -/

namespace Strata.TypedExpressionTest

open Lambda

/-- The variable `x`. -/
def x : Core.Expression.Ident := ⟨"x", ()⟩

/-- `int.add(x, 1)`, with `x` and the operator annotated. -/
def addOne : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc (.op Core.valueLoc ⟨"Int.Add", ()⟩ (some (.arrow .int (.arrow .int .int))))
    (.fvar Core.valueLoc x (some .int))) (.intConst Core.valueLoc 1)

example : Core.Expression.Typed addOne (.forAll [] .int) :=
  ⟨.int, rfl, rfl, fun y τ? h => by
    simp only [addOne, LExpr.freeVars, List.nil_append, List.append_nil, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false] at h
    exact ⟨.int, h.2, rfl⟩, .app (.app .op .fvar) (.const rfl)⟩

example : ¬ Core.Expression.Typed (.fvar Core.valueLoc x none) (.forAll [] .int) := by
  rintro ⟨τ, -, -, ha, -⟩
  obtain ⟨_, h, -⟩ := ha x none (by simp [LExpr.freeVars])
  cases h

example : ¬ Core.Expression.Typed addOne (.forAll [] .bool) := by
  rintro ⟨τ, h, -, -, hT⟩
  cases h
  exact absurd (HasTypeA_unique hT (.app (.app .op .fvar) (.const rfl))) (by decide)

end Strata.TypedExpressionTest
