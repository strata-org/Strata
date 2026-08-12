/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
## `Except` Utilities
-/

public section

namespace Except

/-- If `mapError f e` succeeds with `v`, then `e` succeeds with `v`. -/
theorem mapError_ok_h' {α β γ : Type} {f : α → β} {e : Except α γ} {v : γ}
    (h : Except.mapError f e = .ok v) : e = .ok v := by
  cases e with
  | error a => simp [Except.mapError] at h
  | ok val => simp [Except.mapError] at h; exact congrArg Except.ok h

end Except
