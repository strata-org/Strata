/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import all Strata.Languages.Laurel.LaurelAST

/-!
# Properties of the Laurel AST

Properties of the definitions in `Strata.Languages.Laurel.LaurelAST`.

Key results:

- `highEq_source_irrel` — `highEq` ignores the source metadata of both
  arguments.
-/

namespace Strata.Laurel

public section

/-- `highEq` only inspects the wrapped type values, never the source metadata
    of either argument. -/
theorem highEq_source_irrel (a b : HighTypeMd) (sa sb : Option FileRange) :
    highEq ⟨a.val, sa⟩ ⟨b.val, sb⟩ = highEq a b := by
  rw [highEq.eq_def, highEq.eq_def]

end

end Strata.Laurel
