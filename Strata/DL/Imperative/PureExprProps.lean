/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PureExpr

/-! # Properties of the expression interfaces

The only free variable of a variable reference is the variable
(`HasFvar.eq_of_mem_getFvars_mkVar`).

Key theorems: `HasFvar.eq_of_mem_getFvars_mkVar`. -/

namespace Imperative

public section

/-- The only free variable of a variable reference is the variable. -/
theorem HasFvar.eq_of_mem_getFvars_mkVar {P : PureExpr} [HasFvar P] [HasFvars P]
    [LawfulHasFvars P] {x y : P.Ident} {ty : Option P.Ty}
    (h : y ∈ HasFvars.getFvars (HasFvar.mkVar x ty)) : y = x := by
  cases ty <;> simp only [HasFvar.mkVar] at h <;>
    grind [LawfulHasFvars.mkFvar_getFvars, LawfulHasFvars.mkTypedFvar_getFvars]

end -- public section

end Imperative
