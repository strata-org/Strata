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

/-- `Except`'s bind on a success, as a rewrite. -/
theorem ok_bind {E α β} (a : α) (h : α → Except E β) :
    ((Except.ok a : Except E α) >>= h) = h a := rfl

/-- `Except`'s bind on an error, as a rewrite. -/
theorem error_bind {E α β} (e : E) (h : α → Except E β) :
    ((Except.error e : Except E α) >>= h) = .error e := rfl

/-- If `mapError f e` succeeds with `v`, then `e` succeeds with `v`. -/
theorem mapError_ok_h' {α β γ : Type} {f : α → β} {e : Except α γ} {v : γ}
    (h : Except.mapError f e = .ok v) : e = .ok v := by
  cases e with
  | error a => simp [Except.mapError] at h
  | ok val => simp [Except.mapError] at h; exact congrArg Except.ok h

/-- Bind inversion: a bind succeeds exactly when it factors through a
    successful intermediate result. The `mp` direction replaces manual case
    analysis whose `error` branches are impossible. -/
theorem bind_is_ok {E α β} (m : Except E α) (h : α → Except E β) (r : β) :
    ((m >>= h) = .ok r) ↔ ∃ (a : α), m = .ok a ∧ h a = .ok r := by
  match m with
  | .ok a => simp [Bind.bind, Except.bind]
  | .error e => simp [Bind.bind, Except.bind]

end Except
