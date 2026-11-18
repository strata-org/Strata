/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.TypeSkolem

/-! # Properties of type-parameter renaming

Key theorem: `renameReservedWith_cases`, the two outcomes of renaming a declaration's
reserved type parameters. -/

public section

namespace Core

/-- `renameReservedWith` returns `x` when the reserved renaming is empty, and otherwise `rename`
    of that renaming. -/
theorem renameReservedWith_cases {α : Type} (typeArgs : List String)
    (avoid : Unit → List String) (rename : List (String × String) → α) (x : α) :
    (renameReservedWith typeArgs avoid rename x = x ∧
        reservedTypeArgsRenaming typeArgs avoid = []) ∨
      renameReservedWith typeArgs avoid rename x =
        rename (reservedTypeArgsRenaming typeArgs avoid) := by
  unfold renameReservedWith
  dsimp only
  split
  · rename_i hempty
    exact Or.inl ⟨rfl, List.isEmpty_iff.mp hempty⟩
  · exact Or.inr rfl

end Core

end -- public section
